//! Static method dispatch and related intrinsics.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, RcLifecycle};
use vole_frontend::{MethodCallExpr, NodeId, Symbol};
use vole_identity::{MethodId, NameId, TypeDefId};
use vole_sema::generic::{StaticMethodMonomorphInstance, StaticMethodMonomorphKey};
use vole_sema::type_arena::TypeId;

impl Cg<'_, '_, '_> {
    /// Handle static method call: TypeName.method(args)
    /// Static methods don't have a receiver, so we don't compile the object expression.
    pub(super) fn static_method_call(
        &mut self,
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type_id: TypeId,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Check for float intrinsics (nan, infinity, neg_infinity, epsilon)
        // These are compiled directly to constants, no function call needed.
        if mc.args.is_empty()
            && let Some(result) = self.try_float_intrinsic(type_def_id, mc.method)?
        {
            return Ok(result);
        }

        // Check for Array.filled<T> intrinsic (compiled as ArrayFilled runtime call)
        if let Some(result) = self.try_array_filled_intrinsic(type_def_id, mc, expr_id)? {
            return Ok(result);
        }

        // Get the method's name_id for lookup
        let method_def = self.query().get_method(method_id);
        let method_name_id = method_def.name_id;

        // Check for monomorphized static method (generic classes)
        if let Some(instance) =
            self.find_static_monomorph_instance(method_name_id, type_def_id, expr_id)
        {
            return self.call_static_monomorph_instance(&instance, mc);
        }

        // Look up the static method info via unified method_func_keys map
        // Uses type's NameId for stable lookup across different analyzer instances
        let type_name_id = self.query().get_type(type_def_id).name_id;
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
                let static_candidates: Vec<_> = self
                    .registry()
                    .static_method_monomorph_cache
                    .instances()
                    .filter(|(k, _)| k.class_name == type_name_id && k.method_name == method_name_id)
                    .map(|(k, inst)| {
                        let mangled = self.query().display_name(inst.mangled_name);
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

        // Get param types and return type from arena
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) = arena.unwrap_function(func_type_id).ok_or_else(|| {
                CodegenError::type_mismatch("static method call", "function type", "non-function")
            })?;
            (params.clone(), ret)
        };

        // Compile provided arguments (no receiver for static methods), tracking RC temps
        let mut args = Vec::new();
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        for (arg, param_id) in mc.args.iter().zip(param_ids.iter()) {
            let compiled = self.expr_with_expected_type(arg, *param_id)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            let compiled = self.coerce_to_type(compiled, *param_id)?;
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
        let coerced = self.coerce_call_args(func_ref, &args);
        let call = self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear();

        // For sret, result[0] is the sret pointer we passed in
        let mut result = if is_sret {
            let results = self.builder.inst_results(call);
            CompiledValue::new(results[0], self.ptr_type(), return_type_id)
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
        expr_id: NodeId,
    ) -> Option<StaticMethodMonomorphInstance> {
        // Try direct monomorph lookup with key rewriting
        if let Some(mono_key) = self.query().static_method_generic_at(expr_id) {
            // Static method call sites inside generic class methods are often recorded
            // with abstract TypeParam keys. Rewrite those keys through the current
            // substitution map before looking in the monomorph cache.
            let effective_key = if let Some(subs) = self.substitutions {
                let arena = self.arena();
                let needs_substitution = mono_key
                    .class_type_keys
                    .iter()
                    .chain(mono_key.method_type_keys.iter())
                    .any(|&type_id| arena.unwrap_type_param(type_id).is_some());
                if needs_substitution {
                    let map_keys = |keys: &[TypeId]| {
                        keys.iter()
                            .map(|&type_id| {
                                if let Some(name_id) = arena.unwrap_type_param(type_id) {
                                    subs.get(&name_id).copied().unwrap_or(type_id)
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

            // Look up the monomorphized instance
            if let Some(instance) = self
                .registry()
                .static_method_monomorph_cache
                .get(&effective_key)
            {
                return Some(instance.clone());
            }
        }

        // Fallback: choose a compatible cached static monomorph instance by class/method.
        // This handles class-independent static helpers where sema records an abstract key
        // (or no concrete key in module-local NodeId space), while still preferring a
        // concrete instance that matches the current substitution map when available.
        let type_name_id = self.query().get_type(type_def_id).name_id;
        let subs = self.substitutions;
        let arena = self.arena();
        self.registry()
            .static_method_monomorph_cache
            .instances()
            .filter_map(|(key, instance)| {
                if key.class_name != type_name_id || key.method_name != method_name_id {
                    return None;
                }

                let substitution_matches = if let Some(subs) = subs {
                    let mut matches = 0usize;
                    let mut incompatible = false;
                    for (name_id, inst_ty) in &instance.substitutions {
                        if let Some(ctx_ty) = subs.get(name_id).copied() {
                            if ctx_ty == *inst_ty {
                                matches += 1;
                            } else if arena.unwrap_type_param(*inst_ty).is_none() {
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
                    .all(|&type_id| arena.unwrap_type_param(type_id).is_none())
                    && key
                        .method_type_keys
                        .iter()
                        .all(|&type_id| arena.unwrap_type_param(type_id).is_none());

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
        instance: &StaticMethodMonomorphInstance,
        mc: &MethodCallExpr,
    ) -> CodegenResult<CompiledValue> {
        // Compile arguments with substituted param types (TypeId-based)
        let param_type_ids = &instance.func_type.params_id;
        let mut args = Vec::new();
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
            let compiled = self.expr_with_expected_type(arg, param_type_id)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            let compiled = self.coerce_to_type(compiled, param_type_id)?;
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
        let coerced = self.coerce_call_args(func_ref, &args);
        let call = self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear();

        // For sret, result[0] is the sret pointer we passed in
        let mut result = if is_sret {
            let results = self.builder.inst_results(call);
            CompiledValue::new(results[0], self.ptr_type(), return_type_id)
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
        let type_name_id = self.query().get_type(type_def_id).name_id;
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
                    CompiledValue::new(v, types::F32, TypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::NAN);
                    CompiledValue::new(v, types::F64, TypeId::F64)
                }
            }
            "infinity" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::INFINITY);
                    CompiledValue::new(v, types::F32, TypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::INFINITY);
                    CompiledValue::new(v, types::F64, TypeId::F64)
                }
            }
            "neg_infinity" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::NEG_INFINITY);
                    CompiledValue::new(v, types::F32, TypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::NEG_INFINITY);
                    CompiledValue::new(v, types::F64, TypeId::F64)
                }
            }
            "epsilon" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::EPSILON);
                    CompiledValue::new(v, types::F32, TypeId::F32)
                } else {
                    let v = self.builder.ins().f64const(f64::EPSILON);
                    CompiledValue::new(v, types::F64, TypeId::F64)
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
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> CodegenResult<Option<CompiledValue>> {
        // Check if this is Array.filled
        let type_name_id = self.query().get_type(type_def_id).name_id;
        let type_name = self.name_table().last_segment_str(type_name_id);
        if type_name.as_deref() != Some("Array") {
            return Ok(None);
        }
        let method_name = self.interner().resolve(mc.method);
        if method_name != "filled" {
            return Ok(None);
        }

        // We expect exactly two arguments: count and value
        if mc.args.len() != 2 {
            return Err(CodegenError::arg_count("Array.filled", 2, mc.args.len()));
        }

        // Get the return type [T] from sema to determine element type T
        let return_type_id = self
            .get_expr_type_substituted(&expr_id)
            .ok_or_else(|| CodegenError::missing_resource("Array.filled return type from sema"))?;
        let elem_type_id = self.arena().unwrap_array(return_type_id).ok_or_else(|| {
            CodegenError::type_mismatch("Array.filled", "array type", "non-array")
        })?;
        let is_wide_elem = {
            let arena = self.arena();
            elem_type_id == arena.i128() || elem_type_id == arena.f128()
        };

        // Compile count argument
        let count = self.expr(&mc.args[0])?;

        // Compile value argument
        let value = self.expr(&mc.args[1])?;

        let (tag_val, value_bits, mut stored_value) =
            self.prepare_dynamic_array_store(value, elem_type_id)?;

        // Call vole_array_filled(count, tag, value) -> *mut RcArray
        let filled_ref = self.runtime_func_ref(RuntimeKey::ArrayFilled)?;
        let args = self.coerce_call_args(filled_ref, &[count.value, tag_val, value_bits]);
        let call = self.builder.ins().call(filled_ref, &args);
        let result_val = self.builder.inst_results(call)[0];

        // Array.filled clones the provided element into each slot; release the
        // original temporary value now that ownership has transferred.
        if is_wide_elem {
            self.call_runtime_void(RuntimeKey::RcDec, &[value_bits])?;
        } else {
            self.consume_rc_value(&mut stored_value)?;
        }

        let mut result = CompiledValue::new(result_val, self.ptr_type(), return_type_id);
        result.rc_lifecycle = RcLifecycle::Owned;

        Ok(Some(result))
    }
}
