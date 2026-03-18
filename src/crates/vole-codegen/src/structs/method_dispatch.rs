// src/codegen/structs/method_dispatch.rs
//
// Interface dispatch (vtable), functional interface calls, and module method routing.

use cranelift::prelude::*;
use cranelift_module::Module;
use smallvec::{SmallVec, smallvec};

use crate::RuntimeKey;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use crate::context::Cg;
use crate::context::ExternalMethodRef;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, module_name_id};
use vole_identity::{ModuleId, MonomorphKey, NameId, TypeDefId, TypeId, VirTypeId};
use vole_vir::expr::{VirFunctionMonomorphKey, VirResolvedMethod};

use super::methods::ArgSource;

impl Cg<'_, '_, '_> {
    /// Handle module method calls (e.g., math.sqrt(16.0), math.lerp(...)).
    /// Dispatches to external native functions, generic intrinsics, or pure Vole module functions.
    pub(super) fn module_method_call(
        &mut self,
        module_id: ModuleId,
        arg_source: &ArgSource<'_>,
        method_name_str: &str,
        vir_resolution: &VirResolvedMethod,
        vir_generic_key: Option<&VirFunctionMonomorphKey>,
        resolved_call_args: Option<&[Option<usize>]>,
    ) -> CodegenResult<CompiledValue> {
        let module_path = self
            .analyzed()
            .name_table()
            .module_path(module_id)
            .to_string();
        let name_id = module_name_id(self.analyzed(), module_id, method_name_str);
        let (external_info, func_vir_type_id) = match vir_resolution {
            VirResolvedMethod::Implemented {
                external_info,
                func_type_id,
                ..
            } => (
                external_info.map(ExternalMethodRef::from),
                self.try_substitute_type_v(*func_type_id),
            ),
            _ => {
                return Err(CodegenError::not_found(
                    "module method",
                    format!("{}::{}", module_path, method_name_str),
                ));
            }
        };

        // Get return type from function type (unwrap VirTypeId, then convert for downstream)
        let return_type_id = {
            let (_, ret_vir) = self
                .vir_query_unwrap_function_v(func_vir_type_id)
                .expect("INTERNAL: module method: missing function type");
            let table = self.vir_type_table();
            table.vir_to_type_id(ret_vir)
        };

        // Compile arguments, tracking owned RC temps for cleanup
        let (args, mut rc_temps) = self.compile_args_tracking_rc(arg_source)?;

        if let Some(ext_info) = external_info {
            // External FFI function
            let result = self.call_external_id(&ext_info, &args, return_type_id)?;
            self.consume_rc_args(&mut rc_temps)?;
            return Ok(result);
        }

        // Check if this is a generic external intrinsic (e.g., math.sqrt<f64>)
        let monomorph_key = vir_generic_key.map(|key| {
            let effective_type_keys: Vec<VirTypeId> = key
                .type_keys
                .iter()
                .map(|&vir_ty| {
                    let substituted = self.try_substitute_type_v(vir_ty);
                    if let Some(subs) = self.substitutions
                        && let Some(name_id) = self.vir_query_unwrap_type_param_v(substituted)
                    {
                        subs.get(&name_id).copied().unwrap_or(substituted)
                    } else {
                        substituted
                    }
                })
                .collect();
            MonomorphKey::new(key.func_name, effective_type_keys)
        });

        if let Some(monomorph_key) = monomorph_key.as_ref() {
            let instance_data = self.free_monomorph(monomorph_key).map(|inst| {
                (
                    inst.original_name,
                    inst.func_type.params_id.to_vec(),
                    inst.func_type.return_type_id,
                    inst.substitutions.clone(),
                )
            });

            if let Some((original_name, mono_param_type_ids, mono_return_type_id, substitutions)) =
                instance_data
                && let Some(callee_name) = self.name_table().last_segment_str(original_name)
                && let Some(generic_ext_info) =
                    self.analyzed().generic_external_by_name(&callee_name)
            {
                let key = self.resolve_intrinsic_key_for_monomorph(
                    &callee_name,
                    &generic_ext_info.type_mappings,
                    &substitutions,
                )?;
                let ext_module_path = self
                    .name_table()
                    .last_segment_str(generic_ext_info.module_path)
                    .unwrap_or_default();

                let return_type_id = self.substitute_type(mono_return_type_id);
                let concrete_param_type_ids: Vec<TypeId> = mono_param_type_ids
                    .iter()
                    .map(|&ty| {
                        self.vir_query_expect_substitute(
                            ty,
                            &substitutions,
                            "module generic intrinsic args",
                        )
                    })
                    .collect();

                // Clean up rc_temps from initial arg compilation
                // (generic intrinsic recompiles args internally)
                self.consume_rc_args(&mut rc_temps)?;
                return self.call_generic_external_intrinsic_method_args(
                    &ext_module_path,
                    &key,
                    arg_source,
                    return_type_id,
                    Some(&concrete_param_type_ids),
                );
            }
        }

        // Pure Vole function - call by mangled name
        let name_id = name_id.ok_or_else(|| {
            CodegenError::not_found(
                "module method",
                format!("{}::{}", module_path, method_name_str),
            )
        })?;
        let func_key = self.funcs().intern_name_id(name_id);
        let func_id = self.funcs().func_id(func_key).ok_or_else(|| {
            CodegenError::not_found(
                "module function",
                format!("{}::{}", module_path, method_name_str),
            )
        })?;

        // Use the func_registry's return type if it was overridden (e.g. generators
        // have their return type changed from Iterator<T> to RuntimeIterator(T) in
        // pass 1). Fall back to the sema return type otherwise.
        let return_type_id = self.funcs().return_type(func_key).unwrap_or(return_type_id);

        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        // Get expected parameter types from the function's Cranelift signature
        // and fill in defaults for omitted parameters.
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let expected_types: Vec<Type> = self.builder.func.dfg.signatures[sig_ref]
            .params
            .iter()
            .map(|p| p.value_type)
            .collect();

        // Handle sret convention for large struct returns (3+ flat slots).
        let is_sret = if let Some(sret_ptr) = self.alloc_sret_ptr(return_type_id)? {
            // When using named arg reordering, we build call_args from scratch below,
            // so only prepend sret for the positional (non-named) path.
            if resolved_call_args.is_none() {
                let mut new_args = Vec::with_capacity(args.len() + 1);
                new_args.push(sret_ptr);
                new_args.extend_from_slice(&args);
                // Replace args with sret-prepended version for positional path below.
                // For the named-arg path, sret is prepended in the branch below.
                return self.module_method_call_positional(
                    func_ref,
                    new_args,
                    &expected_types,
                    name_id,
                    return_type_id,
                    true,
                    &mut rc_temps,
                );
            }
            true
        } else {
            false
        };

        let user_param_offset = if is_sret { 1 } else { 0 };
        let expected_user_params = expected_types.len() - user_param_offset;

        // When named arguments are present, reorder args and fill defaults
        // according to the sema-provided mapping.
        if let Some(mapping) = resolved_call_args {
            let sema_func_id = self.analyzed().function_id_by_name_id(name_id);
            let arg_count = arg_source.len();

            // Validate mapping: length must match expected params, and every
            // provided arg index must be in range.
            let mapping_valid = mapping.len() == expected_user_params && {
                let mut seen = vec![false; arg_count];
                let mut mapped = 0usize;
                let mut ok = true;
                for call_idx in mapping.iter().flatten().copied() {
                    if call_idx >= arg_count || seen[call_idx] {
                        ok = false;
                        break;
                    }
                    seen[call_idx] = true;
                    mapped += 1;
                }
                ok && mapped == arg_count
            };

            if mapping_valid {
                let mut call_args: Vec<Value> = Vec::with_capacity(expected_types.len());

                // Prepend sret pointer if needed.
                if is_sret {
                    let sret_ptr = self
                        .alloc_sret_ptr(return_type_id)?
                        .expect("INTERNAL: sret already checked");
                    call_args.push(sret_ptr);
                }

                for (slot, opt_call_idx) in mapping.iter().enumerate() {
                    let expected_ty = expected_types.get(slot + user_param_offset).copied();
                    let val = if let Some(&call_arg_idx) = opt_call_idx.as_ref() {
                        // This slot maps to a caller-provided arg (already compiled).
                        let compiled = args[call_arg_idx];
                        // The arg is already a raw Value; coerce to the signature type.
                        if let Some(expected) = expected_ty {
                            let actual = self.builder.func.dfg.value_type(compiled);
                            self.coerce_cranelift_value(compiled, actual, expected)
                        } else {
                            compiled
                        }
                    } else {
                        // This slot uses its default value.
                        let sema_fid = sema_func_id.expect(
                            "INTERNAL: named arg mapping with defaults but no sema function id",
                        );
                        let default_vir = self
                            .function_default_vir_init(sema_fid, slot)
                            .cloned()
                            .ok_or_else(|| {
                            CodegenError::internal_with_context(
                                "missing VIR function default expression",
                                format!("{sema_fid:?} param {slot}"),
                            )
                        })?;
                        let compiled = self.compile_vir_expr(&default_vir)?;
                        self.coerce_arg_to_sig_type(compiled, expected_ty)
                    };
                    call_args.push(val);
                }

                let call_inst = self.emit_call(func_ref, &call_args);

                let result = if is_sret {
                    let results = self.builder.inst_results(call_inst);
                    self.compiled_with_ty(results[0], self.ptr_type(), return_type_id)
                } else {
                    self.call_result(call_inst, return_type_id)?
                };
                self.consume_rc_args(&mut rc_temps)?;
                return Ok(result);
            }
            // If mapping is invalid, fall through to positional path.
        }

        // Positional path: args are already in order, just fill trailing defaults.
        let mut call_args = args;
        if is_sret {
            let sret_ptr = self
                .alloc_sret_ptr(return_type_id)?
                .expect("INTERNAL: sret already checked");
            call_args.insert(0, sret_ptr);
        }
        self.module_method_call_positional(
            func_ref,
            call_args,
            &expected_types,
            name_id,
            return_type_id,
            is_sret,
            &mut rc_temps,
        )
    }

    /// Positional argument path for module method calls: fills trailing defaults
    /// for omitted parameters and emits the call.
    #[expect(clippy::too_many_arguments)]
    fn module_method_call_positional(
        &mut self,
        func_ref: cranelift_codegen::ir::FuncRef,
        mut call_args: Vec<Value>,
        expected_types: &[Type],
        name_id: NameId,
        return_type_id: TypeId,
        is_sret: bool,
        rc_temps: &mut [CompiledValue],
    ) -> CodegenResult<CompiledValue> {
        let user_param_offset = if is_sret { 1 } else { 0 };
        let expected_user_params = expected_types.len() - user_param_offset;

        // If there are fewer provided args than expected, compile default expressions
        if call_args.len() - user_param_offset < expected_user_params {
            let sema_func_id = self.analyzed().function_id_by_name_id(name_id);
            if let Some(sema_func_id) = sema_func_id {
                let start_index = call_args.len() - user_param_offset;
                for (idx, &expected_ty) in expected_types
                    .iter()
                    .enumerate()
                    .take(expected_types.len())
                    .skip(start_index + user_param_offset)
                {
                    // idx is the index into expected_types (includes sret offset);
                    // the parameter slot in the function definition is idx - user_param_offset.
                    let param_slot = idx - user_param_offset;
                    let Some(default_vir) = self
                        .function_default_vir_init(sema_func_id, param_slot)
                        .cloned()
                    else {
                        if self
                            .analyzed()
                            .has_function_default_expr(sema_func_id, param_slot)
                        {
                            return Err(CodegenError::internal_with_context(
                                "missing VIR function default expression",
                                format!("{sema_func_id:?} param {param_slot}"),
                            ));
                        }
                        continue;
                    };
                    let compiled = self.compile_vir_expr(&default_vir)?;
                    let arg_value = self.coerce_arg_to_sig_type(compiled, Some(expected_ty));
                    call_args.push(arg_value);
                }
            }
        }

        let call_inst = self.emit_call(func_ref, &call_args);

        // For sret, result[0] is the sret pointer we passed in
        let result = if is_sret {
            let results = self.builder.inst_results(call_inst);
            self.compiled_with_ty(results[0], self.ptr_type(), return_type_id)
        } else {
            self.call_result(call_inst, return_type_id)?
        };
        self.consume_rc_args(rc_temps)?;
        Ok(result)
    }

    /// Handle functional interface calls (closures and pure functions).
    pub(super) fn functional_interface_call(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        is_closure: bool,
        arg_source: &ArgSource<'_>,
    ) -> CodegenResult<CompiledValue> {
        // Extract function type components as VirTypeIds (no sema_type_id round-trip)
        let (param_virs, return_vir) =
            self.vir_query_unwrap_function(func_type_id)
                .ok_or_else(|| {
                    CodegenError::type_mismatch(
                        "functional interface call",
                        "function type",
                        "other",
                    )
                })?;

        // Check if this is actually a closure or a pure function
        // The is_closure flag is determined by the caller based on the actual
        // lambda's compilation, not the interface's generic signature.
        if is_closure {
            // It's a closure - extract function pointer and pass closure
            let func_ptr = self.call_runtime(RuntimeKey::ClosureGetFunc, &[func_ptr_or_closure])?;

            // Build the Cranelift signature for the closure call
            // First param is the closure pointer, then the user params
            let mut sig = self.jit_module().make_signature();
            sig.params.push(AbiParam::new(self.ptr_type())); // Closure pointer
            for &param_vir in &param_virs {
                sig.params
                    .push(AbiParam::new(self.cranelift_type_v(param_vir)));
            }
            let is_void_return = return_vir == VirTypeId::VOID;
            if !is_void_return {
                sig.returns
                    .push(AbiParam::new(self.cranelift_type_v(return_vir)));
            }

            // Compile arguments - closure pointer first, then user args
            let mut args: ArgVec = smallvec![func_ptr_or_closure];
            let func_arg_count = arg_source.len();
            for i in 0..func_arg_count {
                let compiled = self.compile_arg_from_source(arg_source, i)?;
                args.push(compiled.value);
            }

            let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);

            // Perform the indirect call (call_result still needs sema TypeId)
            let table = self.vir_type_table();
            let return_type_id = table.vir_to_type_id(return_vir);
            let call_inst = self.emit_call_indirect(sig_ref, func_ptr, &args);
            self.call_result(call_inst, return_type_id)
        } else {
            // It's a pure function - call directly
            let mut sig = self.jit_module().make_signature();
            for &param_vir in &param_virs {
                sig.params
                    .push(AbiParam::new(self.cranelift_type_v(param_vir)));
            }
            let is_void_return = return_vir == VirTypeId::VOID;
            if !is_void_return {
                sig.returns
                    .push(AbiParam::new(self.cranelift_type_v(return_vir)));
            }

            let (values, _) = self.compile_args_tracking_rc(arg_source)?;
            let mut args = values;
            let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);
            let table = self.vir_type_table();
            let return_type_id = table.vir_to_type_id(return_vir);
            let call_inst = self.emit_call_indirect(sig_ref, func_ptr_or_closure, &args);
            self.call_result(call_inst, return_type_id)
        }
    }

    /// Get the vtable slot index for an interface method by TypeDefId and method NameId.
    fn interface_method_slot(
        &self,
        interface_type_id: TypeDefId,
        method_name_id: NameId,
    ) -> CodegenResult<usize> {
        crate::interfaces::interface_method_slot_by_type_def_id(
            interface_type_id,
            method_name_id,
            self.analyzed(),
        )
    }

    /// Dispatch an interface method call by TypeDefId (EntityRegistry-based)
    pub(crate) fn interface_dispatch_call_args_by_type_def_id(
        &mut self,
        obj: &CompiledValue,
        arg_source: &ArgSource<'_>,
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let slot = self.interface_method_slot(interface_type_id, method_name_id)?;
        self.interface_dispatch_call_args_inner(obj, arg_source, slot, func_type_id, None)
    }

    /// Dispatch an interface method call with pre-computed vtable slot index.
    /// This is the optimized path where sema has already computed the slot.
    /// `return_type_override` is the concrete return type from sema's
    /// concrete_return_hint (e.g. RuntimeIterator<T> for iterator methods).
    pub(crate) fn interface_dispatch_call_args_by_slot(
        &mut self,
        obj: &CompiledValue,
        arg_source: &ArgSource<'_>,
        slot: u32,
        func_type_id: TypeId,
        return_type_override: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        self.interface_dispatch_call_args_inner(
            obj,
            arg_source,
            slot as usize,
            func_type_id,
            return_type_override,
        )
    }

    fn interface_dispatch_call_args_inner(
        &mut self,
        obj: &CompiledValue,
        arg_source: &ArgSource<'_>,
        slot: usize,
        func_type_id: TypeId,
        return_type_override: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let word_type = self.ptr_type();
        let word_bytes = word_type.bytes() as i32;
        let dispatch_func_type_id = self
            .vir_query_unwrap_interface_v(obj.type_id)
            .and_then(|(interface_type_def_id, _)| {
                self.analyzed()
                    .interface_method_ids_ordered(interface_type_def_id)
                    .get(slot)
                    .copied()
            })
            .map(|method_id| self.analyzed().method_signature_id(method_id))
            .unwrap_or(func_type_id);

        // Unwrap function type to get params and return type as VirTypeIds
        let (param_virs, return_vir) = self
            .vir_query_unwrap_function(dispatch_func_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch("interface dispatch", "function type", "non-function")
            })?;
        let is_void_return = return_vir == VirTypeId::VOID;

        // Load data pointer from boxed interface (first word)
        // Currently unused but kept for interface dispatch debugging
        let _data_word = self
            .builder
            .ins()
            .load(word_type, MemFlags::new(), obj.value, 0);
        let vtable_ptr = self
            .builder
            .ins()
            .load(word_type, MemFlags::new(), obj.value, word_bytes);
        // Slot 0 is the meta getter; method slots start at VTABLE_METHOD_OFFSET.
        let vtable_offset =
            (slot as i32 + crate::interfaces::vtable::VTABLE_METHOD_OFFSET as i32) * word_bytes;
        let func_ptr =
            self.builder
                .ins()
                .load(word_type, MemFlags::new(), vtable_ptr, vtable_offset);

        tracing::trace!(
            slot = slot,
            vtable_offset = vtable_offset,
            "interface vtable dispatch"
        );

        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(word_type));
        for _ in 0..param_virs.len() {
            sig.params.push(AbiParam::new(word_type));
        }
        if !is_void_return {
            sig.returns.push(AbiParam::new(word_type));
        }
        let sig_ref = self.builder.import_signature(sig);

        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;

        // Pass the full boxed interface pointer (not just data_word) so wrappers can
        // access both data and vtable. This is needed for Iterator methods that create
        // RcIterator adapters via vole_interface_iter.
        let iface_arg_count = arg_source.len();
        let mut call_args: ArgVec = smallvec![obj.value];
        for i in 0..iface_arg_count {
            let compiled = self.compile_arg_from_source(arg_source, i)?;
            // Coerce arguments to their expected parameter types before converting
            // to word representation. Without this, union-typed parameters would be
            // passed as their concrete variant (e.g. i16) rather than as a tagged
            // union pointer, causing the callee's `is` checks to segfault.
            let compiled = if let Some(&expected_vir) = param_virs.get(i) {
                self.coerce_to_type(compiled, expected_vir)?
            } else {
                compiled
            };
            let word = self.emit_word(&compiled, Some(heap_alloc_ref))?;
            call_args.push(word);
        }

        let call = self.emit_call_indirect(sig_ref, func_ptr, &call_args);
        let results = self.builder.inst_results(call);

        if is_void_return {
            return Ok(self.void_value());
        }

        // Convert result from i64 storage to typed value (needs sema TypeId)
        let table = self.vir_type_table();
        let return_type_id = table.vir_to_type_id(return_vir);
        let word = results
            .first()
            .copied()
            .ok_or_else(|| CodegenError::internal("interface call missing return value"))?;
        let value = self.convert_from_i64_storage(word, return_type_id);

        // Use concrete return type override from sema's concrete_return_hint
        // when available (e.g. RuntimeIterator<T> for iterator methods).
        // For callers without a hint, convert Iterator<T> return types to
        // RuntimeIterator<T> inline since external iterator methods return
        // raw iterator pointers, not boxed interface values.
        let return_type_id = return_type_override
            .unwrap_or_else(|| self.convert_interface_iterator_return(return_vir, return_type_id));

        Ok(self.compiled(value, return_type_id))
    }

    /// Resolve an `Iterator<T>` VirTypeId return to its sema TypeId.
    ///
    /// If the VIR type is `Interface { Iterator, [elem] }`, looks up the
    /// corresponding sema TypeId. Returns `fallback` otherwise.
    fn convert_interface_iterator_return(&self, vir_ty: VirTypeId, fallback: TypeId) -> TypeId {
        if self.vir_query_is_iterator_interface_v(vir_ty) {
            let table = self.vir_type_table();
            if let Some(sema_id) = table.lookup_vir_type_id(vir_ty) {
                return sema_id;
            }
        }
        fallback
    }

    /// Convert an Iterator<T> sema TypeId return to RuntimeIterator<T>.
    ///
    /// Resolves the TypeId to VirTypeId and delegates to the VIR-native check.
    /// Both types are thin pointers — this is a type-tag bridge only.
    /// Will be removed in iter-10.
    pub(crate) fn convert_interface_iterator_return_by_type(&self, ty: TypeId) -> TypeId {
        let vir_ty = self.vir_lookup(ty);
        self.convert_interface_iterator_return(vir_ty, ty)
    }

    /// Find the Iterator<T> element type for a concrete receiver type.
    ///
    /// When the receiver is a class/struct that implements Iterator<T>,
    /// returns `Some((elem_vir, iterator_interface_vir))` so callers can
    /// box+wrap the receiver as RuntimeIterator<T> before method dispatch.
    pub(crate) fn find_iterator_elem_for_concrete_receiver(
        &self,
        receiver_vir: VirTypeId,
    ) -> Option<(VirTypeId, VirTypeId)> {
        let iterator_tdef = self.name_table().well_known.iterator_type_def?;
        let table = self.vir_type_table();
        let type_def_id = table.type_def_id(receiver_vir)?;

        // Check if this type implements Iterator<T> and get the type args
        let type_args = self
            .analyzed()
            .entity_metadata()
            .implementation_type_args(type_def_id, iterator_tdef);
        let &elem_vir = type_args.first()?;

        // Look up the existing Iterator<T> interface VirTypeId
        let iface_type = vole_vir::types::VirType::Interface {
            def: iterator_tdef,
            type_args: vec![elem_vir],
        };
        let iface_vir = table.lookup(&iface_type)?;

        Some((elem_vir, iface_vir))
    }
}
