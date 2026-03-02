//! Static method dispatch and related intrinsics.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, RcLifecycle};
use vole_frontend::Symbol;
use vole_identity::{
    MethodId, NameId, NodeId, StaticMethodMonomorphKey, TypeDefId, TypeId, VirTypeId,
};
use vole_vir::VirStaticMethodMonomorphInfo;
use vole_vir::expr::{VirMethodDispatchMeta, VirStaticMethodMonomorphKey};
use vole_vir::types::VirType;

use super::methods::ArgSource;

pub(super) struct StaticMethodCallArgs<'a> {
    pub type_def_id: TypeDefId,
    pub method_id: MethodId,
    pub func_type_id: TypeId,
    pub arg_source: &'a ArgSource<'a>,
    pub method_sym: Symbol,
    pub expr_id: NodeId,
    pub vir_dispatch: Option<&'a VirMethodDispatchMeta>,
}

impl Cg<'_, '_, '_> {
    /// Handle static method call: TypeName.method(args)
    /// Static methods don't have a receiver, so we don't compile the object expression.
    pub(super) fn static_method_call(
        &mut self,
        args: StaticMethodCallArgs<'_>,
    ) -> CodegenResult<CompiledValue> {
        let StaticMethodCallArgs {
            type_def_id,
            method_id,
            func_type_id,
            arg_source,
            method_sym,
            expr_id,
            vir_dispatch,
        } = args;

        let arg_count = arg_source.len();

        // Check for float intrinsics (nan, infinity, neg_infinity, epsilon)
        // These are compiled directly to constants, no function call needed.
        if arg_count == 0
            && let Some(result) = self.try_float_intrinsic(type_def_id, method_sym)?
        {
            return Ok(result);
        }

        let return_type_hint = vir_dispatch
            .and_then(|dispatch| {
                dispatch
                    .substituted_return_type
                    .map(|ty| self.sema_type_id(self.try_substitute_type_v(ty)))
                    .or_else(|| {
                        dispatch.resolved_method.as_ref().map(|resolved| {
                            self.sema_type_id(self.try_substitute_type_v(resolved.return_type_id()))
                        })
                    })
            })
            .or_else(|| self.get_expr_type_substituted(&expr_id));

        // Check for Array.filled<T> intrinsic (compiled as ArrayFilled runtime call)
        if let Some(result) = self.try_array_filled_intrinsic(
            type_def_id,
            arg_source,
            method_sym,
            Some(expr_id),
            return_type_hint,
        )? {
            return Ok(result);
        }

        // Get the method's name_id for lookup
        let method_def = self.analyzed().method_def(method_id);
        let method_name_id = method_def.name_id;

        // Check for monomorphized static method (generic classes)
        let vir_static_key =
            vir_dispatch.and_then(|dispatch| dispatch.static_method_generic.as_ref());
        if let Some(instance) = self.find_static_monomorph_instance(
            method_name_id,
            type_def_id,
            if vir_dispatch.is_some() {
                None
            } else {
                Some(expr_id)
            },
            vir_static_key,
        ) {
            return self.call_static_monomorph_instance(&instance, arg_source);
        }

        // Look up the static method info via unified method_func_keys map
        // Uses type's NameId for stable lookup across different analyzer instances
        let type_name_id = self.analyzed().entity_type_name_id(type_def_id);
        let func_key = *self.method_func_keys()
            .get(&(type_name_id, method_name_id))
            .ok_or_else(|| {
                let name_table = self.name_table();
                let type_name = name_table.display(type_name_id);
                let method_name = name_table.display(method_name_id);
                let registered_keys: Vec<_> = self.method_func_keys()
                    .keys()
                    .map(|(tn_id, mn_id)| {
                        let tn = name_table.display(*tn_id);
                        let mn = name_table.display(*mn_id);
                        format!("({}, {})", tn, mn)
                    })
                    .collect();
                let static_candidates: Vec<_> = self.analyzed()
                    .vir_program()
                    .static_method_monomorphs
                    .iter()
                    .filter(|(k, _)| k.class_name == type_name_id && k.method_name == method_name_id)
                    .map(|(k, inst)| {
                        let mangled = self.analyzed().display_name(inst.mangled_name);
                        format!("{:?} -> {}", k, mangled)
                    })
                    .collect();
                CodegenError::internal_with_context(
                    "static method not found",
                    format!(
                        "{}::{} (type_name_id={:?}, method_name_id={:?}). Registered: {:?}. Static candidates: {:?}",
                        type_name, method_name, type_name_id, method_name_id, registered_keys, static_candidates
                    ),
                )
            })?;

        // Get param types and return type via VirTypeTable
        let (param_ids, return_type_id) = {
            let (params, ret) = self
                .vir_query_unwrap_function_sema_v(self.vir_lookup(func_type_id))
                .ok_or_else(|| {
                    CodegenError::type_mismatch(
                        "static method call",
                        "function type",
                        "non-function",
                    )
                })?;
            (params, ret)
        };

        // Compile provided arguments (no receiver for static methods), tracking RC temps.
        // When named args were used, sema stored a resolved_call_args mapping that tells
        // us which call.args[j] fills each parameter slot i (and None means use the default).
        let mut args = Vec::new();
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        let mapping_is_valid = |mapping: &[Option<usize>]| {
            if mapping.len() != param_ids.len() {
                return false;
            }
            let mut seen = vec![false; arg_count];
            let mut mapped_count = 0usize;
            for call_idx in mapping.iter().flatten().copied() {
                if call_idx >= arg_count || seen[call_idx] {
                    return false;
                }
                seen[call_idx] = true;
                mapped_count += 1;
            }
            mapped_count == arg_count
        };
        let named_mapping = vir_dispatch
            .and_then(|dispatch| dispatch.resolved_call_args.clone())
            .filter(|mapping| mapping_is_valid(mapping));
        if let Some(ref mapping) = named_mapping {
            // Named arg reordering: compile each slot in parameter order using the mapping.
            for (slot, opt_call_idx) in mapping.iter().enumerate() {
                let param_id = param_ids[slot];
                let compiled = if let Some(&Some(call_arg_idx)) = Some(opt_call_idx) {
                    let compiled =
                        self.compile_arg_with_expected_type(arg_source, call_arg_idx, param_id)?;
                    if compiled.is_owned() {
                        rc_temps.push(compiled);
                    }
                    self.coerce_to_type_id(compiled, param_id)?
                } else {
                    // slot uses its default value
                    let (default_vals, rc_owned) =
                        self.compile_method_default_args(method_id, slot, &[param_id], false)?;
                    rc_temps.extend(rc_owned);
                    if let Some(&val) = default_vals.first() {
                        self.compiled_with_ty(val, self.cranelift_type(param_id), param_id)
                    } else {
                        continue;
                    }
                };
                args.push(compiled.value);
            }
        } else {
            for (i, param_id) in param_ids.iter().enumerate().take(arg_count) {
                let compiled = self.compile_arg_with_expected_type(arg_source, i, *param_id)?;
                if compiled.is_owned() {
                    rc_temps.push(compiled);
                }
                let compiled = self.coerce_to_type_id(compiled, *param_id)?;
                args.push(compiled.value);
            }

            // If there are fewer provided args than expected, compile default expressions
            if args.len() < param_ids.len() {
                let (default_args, _rc_owned) = self.compile_method_default_args(
                    method_id,
                    args.len(),
                    &param_ids[args.len()..],
                    false,
                )?;
                args.extend(default_args);
            }
        }
        // Handle sret convention for large struct returns (3+ flat slots).
        // The function signature has a hidden first parameter for the return
        // buffer pointer that must be prepended to the call arguments.
        let is_sret = if let Some(sret_ptr) = self.alloc_sret_ptr(return_type_id)? {
            args.insert(0, sret_ptr);
            true
        } else {
            false
        };

        // Get function reference and call
        let func_ref = self.func_ref(func_key)?;
        let call = self.emit_call(func_ref, &args);

        // For sret, result[0] is the sret pointer we passed in
        let mut result = if is_sret {
            let results = self.builder.inst_results(call);
            self.compiled_with_ty(results[0], self.ptr_type(), return_type_id)
        } else {
            // call_result must run before consume_rc_args to copy union data
            // from callee's stack before rc_dec calls can clobber it
            self.call_result(call, return_type_id)?
        };
        self.consume_rc_args(&mut rc_temps)?;

        // Mark RC-typed results as Owned so they get properly cleaned up
        if self.rc_state(return_type_id).needs_cleanup() {
            result.rc_lifecycle = RcLifecycle::Owned;
        }

        Ok(result)
    }

    /// Resolve a monomorphized static method instance for a generic class static call.
    ///
    /// Tries direct lookup (with type param substitution key rewriting), then falls
    /// back to scoring-based candidate selection. Returns a cloned instance to avoid
    /// borrow conflicts with the mutable caller.
    fn find_static_monomorph_instance(
        &self,
        method_name_id: NameId,
        type_def_id: TypeDefId,
        _expr_id: Option<NodeId>,
        vir_key: Option<&VirStaticMethodMonomorphKey>,
    ) -> Option<VirStaticMethodMonomorphInfo> {
        let mono_key = vir_key.map(|key| {
            StaticMethodMonomorphKey::new(
                key.class_name,
                key.method_name,
                key.class_type_keys
                    .iter()
                    .map(|&ty| self.sema_type_id(self.try_substitute_type_v(ty)))
                    .collect(),
                key.method_type_keys
                    .iter()
                    .map(|&ty| self.sema_type_id(self.try_substitute_type_v(ty)))
                    .collect(),
            )
        });

        // Try direct monomorph lookup with key rewriting
        if let Some(mono_key) = mono_key.as_ref() {
            // Static method call sites inside generic class methods are often recorded
            // with abstract TypeParam keys. Rewrite those keys through the current
            // substitution map before looking in the monomorph cache.
            let effective_key = if let Some(subs) = self.substitutions {
                let table = self.vir_type_table();
                let unwrap_param = |type_id: TypeId| -> Option<NameId> {
                    let vir = table.lookup_type_id(type_id)?;
                    match table.get(vir) {
                        VirType::Param { name } => Some(*name),
                        _ => None,
                    }
                };
                let needs_substitution = mono_key
                    .class_type_keys
                    .iter()
                    .chain(mono_key.method_type_keys.iter())
                    .any(|&type_id| unwrap_param(type_id).is_some());
                if needs_substitution {
                    let map_keys = |keys: &[TypeId]| {
                        keys.iter()
                            .map(|&type_id| {
                                if let Some(name_id) = unwrap_param(type_id) {
                                    subs.get(&name_id)
                                        .map(|&v| self.sema_type_id(v))
                                        .unwrap_or(type_id)
                                } else {
                                    type_id
                                }
                            })
                            .collect::<Vec<TypeId>>()
                    };
                    StaticMethodMonomorphKey::new(
                        mono_key.class_name,
                        mono_key.method_name,
                        map_keys(&mono_key.class_type_keys),
                        map_keys(&mono_key.method_type_keys),
                    )
                } else {
                    mono_key.clone()
                }
            } else {
                mono_key.clone()
            };

            // Look up the monomorphized instance from VirProgram
            if let Some(instance) = self
                .analyzed()
                .vir_program()
                .static_method_monomorphs
                .get(&effective_key)
            {
                return Some(instance.clone());
            }
        }

        // Fallback: choose a compatible cached static monomorph instance by class/method.
        // This handles class-independent static helpers where sema records an abstract key
        // (or no concrete key in module-local NodeId space), while still preferring a
        // concrete instance that matches the current substitution map when available.
        let type_name_id = self.analyzed().entity_type_name_id(type_def_id);
        let subs = self.substitutions;
        let table = self.vir_type_table();
        let is_type_param = |type_id: TypeId| -> bool {
            table
                .lookup_type_id(type_id)
                .is_some_and(|vir| matches!(table.get(vir), VirType::Param { .. }))
        };
        self.analyzed()
            .vir_program()
            .static_method_monomorphs
            .iter()
            .filter_map(|(key, instance)| {
                if key.class_name != type_name_id || key.method_name != method_name_id {
                    return None;
                }

                let substitution_matches = if let Some(subs) = subs {
                    let mut matches = 0usize;
                    let mut incompatible = false;
                    for (name_id, inst_vir_ty) in &instance.vir_substitutions {
                        if let Some(ctx_vir_ty) = subs.get(name_id).copied() {
                            if ctx_vir_ty == *inst_vir_ty {
                                matches += 1;
                            } else if !is_type_param(instance.substitutions[name_id]) {
                                // Concrete mismatch: this candidate does not match
                                // the current monomorphized call context.
                                incompatible = true;
                                break;
                            }
                        }
                    }
                    if incompatible {
                        return None;
                    }
                    matches
                } else {
                    0
                };
                let concrete_key = key
                    .class_type_keys
                    .iter()
                    .all(|&type_id| !is_type_param(type_id))
                    && key
                        .method_type_keys
                        .iter()
                        .all(|&type_id| !is_type_param(type_id));

                // Prefer substitution-compatible concrete instances first.
                let score = (
                    substitution_matches,
                    concrete_key as usize,
                    instance.substitutions.len(),
                );

                Some((score, instance))
            })
            .max_by_key(|(score, _)| *score)
            .map(|(_, instance)| instance.clone())
    }

    fn call_static_monomorph_instance(
        &mut self,
        instance: &VirStaticMethodMonomorphInfo,
        arg_source: &ArgSource<'_>,
    ) -> CodegenResult<CompiledValue> {
        // Compile arguments with substituted param types (TypeId-based)
        let param_type_ids = &instance.func_type.params_id;
        let mono_arg_count = arg_source.len();
        let mut args = Vec::new();
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        for (i, &param_type_id) in param_type_ids.iter().enumerate().take(mono_arg_count) {
            let compiled = self.compile_arg_with_expected_type(arg_source, i, param_type_id)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            let compiled = self.coerce_to_type_id(compiled, param_type_id)?;
            args.push(compiled.value);
        }

        // Get monomorphized function reference and call
        let return_type_id = instance.func_type.return_type_id;
        // Handle sret convention for large struct returns (3+ flat slots).
        let is_sret = if let Some(sret_ptr) = self.alloc_sret_ptr(return_type_id)? {
            args.insert(0, sret_ptr);
            true
        } else {
            false
        };

        let func_key = self.funcs().intern_name_id(instance.mangled_name);
        let func_ref = self.func_ref(func_key)?;
        let call = self.emit_call(func_ref, &args);

        // For sret, result[0] is the sret pointer we passed in
        let mut result = if is_sret {
            let results = self.builder.inst_results(call);
            self.compiled_with_ty(results[0], self.ptr_type(), return_type_id)
        } else {
            // call_result must run before consume_rc_args to copy union data
            // from callee's stack before rc_dec calls can clobber it
            self.call_result(call, return_type_id)?
        };
        self.consume_rc_args(&mut rc_temps)?;

        // Mark RC-typed results as Owned so they get properly cleaned up
        if self.rc_state(return_type_id).needs_cleanup() {
            result.rc_lifecycle = RcLifecycle::Owned;
        }

        Ok(result)
    }

    /// Try to compile a float intrinsic (nan, infinity, neg_infinity, epsilon).
    /// Returns Some(value) if this is a known intrinsic, None otherwise.
    fn try_float_intrinsic(
        &mut self,
        type_def_id: TypeDefId,
        method_sym: Symbol,
    ) -> CodegenResult<Option<CompiledValue>> {
        // Get type name_id and check if it's f32 or f64
        let type_name_id = self.analyzed().entity_type_name_id(type_def_id);
        let name_table = self.name_table();
        let is_f32 = type_name_id == name_table.primitives.f32;
        let is_f64 = type_name_id == name_table.primitives.f64;

        if !is_f32 && !is_f64 {
            return Ok(None);
        }

        // Get method name string
        let method_name = self.interner().resolve(method_sym);

        // Match intrinsic methods
        let value = match method_name {
            "nan" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::NAN);
                    CompiledValue::new(v, types::F32, VirTypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::NAN);
                    CompiledValue::new(v, types::F64, VirTypeId::F64)
                }
            }
            "infinity" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::INFINITY);
                    CompiledValue::new(v, types::F32, VirTypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::INFINITY);
                    CompiledValue::new(v, types::F64, VirTypeId::F64)
                }
            }
            "neg_infinity" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::NEG_INFINITY);
                    CompiledValue::new(v, types::F32, VirTypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::NEG_INFINITY);
                    CompiledValue::new(v, types::F64, VirTypeId::F64)
                }
            }
            "epsilon" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::EPSILON);
                    CompiledValue::new(v, types::F32, VirTypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::EPSILON);
                    CompiledValue::new(v, types::F64, VirTypeId::F64)
                }
            }
            _ => return Ok(None),
        };

        Ok(Some(value))
    }

    /// Intercept `Array.filled<T>(count, value) -> [T]` and compile as a direct
    /// `vole_array_filled(count, tag, value)` runtime call. Handles union boxing
    /// so each array slot gets its own heap-allocated union pointer.
    fn try_array_filled_intrinsic(
        &mut self,
        type_def_id: TypeDefId,
        arg_source: &ArgSource<'_>,
        method_sym: Symbol,
        expr_id: Option<NodeId>,
        return_type_hint: Option<TypeId>,
    ) -> CodegenResult<Option<CompiledValue>> {
        // Check if this is Array.filled
        let type_name_id = self.analyzed().entity_type_name_id(type_def_id);
        let type_name = self.name_table().last_segment_str(type_name_id);
        if type_name.as_deref() != Some("Array") {
            return Ok(None);
        }
        let method_name = self.interner().resolve(method_sym);
        if method_name != "filled" {
            return Ok(None);
        }

        let filled_arg_count = arg_source.len();
        // We expect exactly two arguments: count and value
        if filled_arg_count != 2 {
            return Err(CodegenError::arg_count("Array.filled", 2, filled_arg_count));
        }

        // Get the return type [T] from sema to determine element type T.
        // VIR-return metadata may still be an unresolved placeholder; if so,
        // fall back to expression type metadata before failing.
        let unwrap_array_sema = |ret_ty: TypeId| -> Option<(TypeId, TypeId)> {
            let vir = self.vir_lookup(ret_ty);
            let elem_vir = self.vir_query_unwrap_array_v(vir)?;
            let elem_ty = self.sema_type_id(elem_vir);
            Some((ret_ty, elem_ty))
        };
        let hint_array_elem = return_type_hint.and_then(&unwrap_array_sema);
        let expr_array_elem = expr_id
            .and_then(|id| self.get_expr_type_substituted(&id))
            .and_then(unwrap_array_sema);
        let (return_type_id, elem_type_id) =
            hint_array_elem.or(expr_array_elem).ok_or_else(|| {
                CodegenError::type_mismatch("Array.filled", "array type", "non-array")
            })?;
        let is_wide_elem = matches!(elem_type_id, TypeId::I128 | TypeId::F128);

        // Compile count argument
        let count = self.compile_arg_from_source(arg_source, 0)?;

        // Compile value argument
        let value = self.compile_arg_from_source(arg_source, 1)?;

        let (tag_val, value_bits, mut stored_value) =
            self.prepare_dynamic_array_store(value, elem_type_id)?;

        // Call vole_array_filled(count, tag, value) -> *mut RcArray
        let filled_ref = self.runtime_func_ref(RuntimeKey::ArrayFilled)?;
        let call = self.emit_call(filled_ref, &[count.value, tag_val, value_bits]);
        let result_val = self.builder.inst_results(call)[0];

        // Array.filled clones the provided element into each slot; release the
        // original temporary value now that ownership has transferred.
        if is_wide_elem {
            self.call_runtime_void(RuntimeKey::RcDec, &[value_bits])?;
        } else {
            self.consume_rc_value(&mut stored_value)?;
        }

        let mut result = self.compiled_with_ty(result_val, self.ptr_type(), return_type_id);
        result.rc_lifecycle = RcLifecycle::Owned;

        Ok(Some(result))
    }
}
