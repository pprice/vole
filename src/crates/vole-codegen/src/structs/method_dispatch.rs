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
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, module_name_id, type_id_to_cranelift};
use vole_frontend::ast::CallArg;
use vole_frontend::{MethodCallExpr, NodeId};
use vole_identity::TypeDefId;
use vole_identity::{ModuleId, NameId};
use vole_sema::resolution::ResolvedMethod;
use vole_sema::type_arena::TypeId;

impl Cg<'_, '_, '_> {
    /// Handle module method calls (e.g., math.sqrt(16.0), math.lerp(...)).
    /// Dispatches to external native functions, generic intrinsics, or pure Vole module functions.
    pub(super) fn module_method_call(
        &mut self,
        module_id: ModuleId,
        mc: &MethodCallExpr,
        expr_id: NodeId,
        method_name_str: &str,
    ) -> CodegenResult<CompiledValue> {
        let module_path = self
            .analyzed()
            .name_table()
            .module_path(module_id)
            .to_string();
        let name_id = module_name_id(self.analyzed(), module_id, method_name_str);
        let resolution = self.analyzed().query().method_at(expr_id);
        let Some(ResolvedMethod::Implemented {
            external_info,
            func_type_id,
            ..
        }) = resolution
        else {
            return Err(CodegenError::not_found(
                "module method",
                format!("{}::{}", module_path, method_name_str),
            ));
        };

        // Get return type from arena
        let return_type_id = {
            let arena = self.arena();
            let (_, ret, _) = arena
                .unwrap_function(*func_type_id)
                .expect("INTERNAL: module method: missing function type");
            ret
        };

        // Compile arguments, tracking owned RC temps for cleanup
        let (args, mut rc_temps) = self.compile_call_args_tracking_rc(&mc.args)?;

        if let Some(ext_info) = external_info {
            // External FFI function
            let result = self.call_external_id(ext_info, &args, return_type_id)?;
            self.consume_rc_args(&mut rc_temps)?;
            return Ok(result);
        }

        // Check if this is a generic external intrinsic (e.g., math.sqrt<f64>)
        if let Some(monomorph_key) = self.query().monomorph_for(expr_id) {
            let instance_data = self.monomorph_cache().get(monomorph_key).map(|inst| {
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
                && let Some(generic_ext_info) = self
                    .analyzed()
                    .implement_registry()
                    .get_generic_external(&callee_name)
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
                        self.arena().expect_substitute(
                            ty,
                            &substitutions,
                            "module generic intrinsic args",
                        )
                    })
                    .collect();

                // Clean up rc_temps from initial arg compilation
                // (generic intrinsic recompiles args internally)
                self.consume_rc_args(&mut rc_temps)?;
                return self.call_generic_external_intrinsic_args(
                    &ext_module_path,
                    &key,
                    &mc.args,
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
        // Handle sret convention for large struct returns (3+ flat slots).
        let mut call_args = args;
        let is_sret = if let Some(sret_ptr) = self.alloc_sret_ptr(return_type_id)? {
            call_args.insert(0, sret_ptr);
            true
        } else {
            false
        };

        let call_inst = self.emit_call(func_ref, &call_args);

        // For sret, result[0] is the sret pointer we passed in
        let result = if is_sret {
            let results = self.builder.inst_results(call_inst);
            CompiledValue::new(results[0], self.ptr_type(), return_type_id)
        } else {
            self.call_result(call_inst, return_type_id)?
        };
        self.consume_rc_args(&mut rc_temps)?;
        Ok(result)
    }

    /// Handle functional interface calls (closures and pure functions).
    pub(super) fn functional_interface_call(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        is_closure: bool,
        mc: &MethodCallExpr,
    ) -> CodegenResult<CompiledValue> {
        // Extract function type components from the arena
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) = arena.unwrap_function(func_type_id).ok_or_else(|| {
                CodegenError::type_mismatch("functional interface call", "function type", "other")
            })?;
            (params.clone(), ret)
        };

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
            for &param_id in &param_ids {
                sig.params.push(AbiParam::new(type_id_to_cranelift(
                    param_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }
            let is_void_return = self.arena().is_void(return_type_id);
            if !is_void_return {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_type_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }

            // Compile arguments - closure pointer first, then user args
            let mut args: ArgVec = smallvec![func_ptr_or_closure];
            for arg in &mc.args {
                let compiled = self.expr(arg.expr())?;
                args.push(compiled.value);
            }

            let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);

            // Perform the indirect call
            let call_inst = self.emit_call_indirect(sig_ref, func_ptr, &args);
            self.call_result(call_inst, return_type_id)
        } else {
            // It's a pure function - call directly
            let mut sig = self.jit_module().make_signature();
            for &param_id in &param_ids {
                sig.params.push(AbiParam::new(type_id_to_cranelift(
                    param_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }
            let is_void_return = self.arena().is_void(return_type_id);
            if !is_void_return {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_type_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }

            let mut args = self.compile_call_args(&mc.args)?;
            let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);
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
            self.registry(),
        )
    }

    /// Dispatch an interface method call by TypeDefId (EntityRegistry-based)
    pub(crate) fn interface_dispatch_call_args_by_type_def_id(
        &mut self,
        obj: &CompiledValue,
        args: &[CallArg],
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let slot = self.interface_method_slot(interface_type_id, method_name_id)?;
        self.interface_dispatch_call_args_inner(obj, args, slot, func_type_id)
    }

    /// Dispatch an interface method call with pre-computed vtable slot index.
    /// This is the optimized path where sema has already computed the slot.
    pub(crate) fn interface_dispatch_call_args_by_slot(
        &mut self,
        obj: &CompiledValue,
        args: &[CallArg],
        slot: u32,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.interface_dispatch_call_args_inner(obj, args, slot as usize, func_type_id)
    }

    fn interface_dispatch_call_args_inner(
        &mut self,
        obj: &CompiledValue,
        args: &[CallArg],
        slot: usize,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let word_type = self.ptr_type();
        let word_bytes = word_type.bytes() as i32;

        // Unwrap function type to get params and return type
        let (param_count, param_type_ids, return_type_id, is_void_return) = {
            let arena = self.arena();
            let (params, ret_id, _is_closure) =
                arena.unwrap_function(func_type_id).ok_or_else(|| {
                    CodegenError::type_mismatch(
                        "interface dispatch",
                        "function type",
                        "non-function",
                    )
                })?;
            (params.len(), params.to_vec(), ret_id, arena.is_void(ret_id))
        };

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
        for _ in 0..param_count {
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
        let mut call_args: ArgVec = smallvec![obj.value];
        for (i, arg) in args.iter().enumerate() {
            let compiled = if let Some(&expected_type_id) = param_type_ids.get(i) {
                self.expr_with_expected_type(arg.expr(), expected_type_id)?
            } else {
                self.expr(arg.expr())?
            };
            // Coerce arguments to their expected parameter types before converting
            // to word representation. Without this, union-typed parameters would be
            // passed as their concrete variant (e.g. i16) rather than as a tagged
            // union pointer, causing the callee's `is` checks to segfault.
            let compiled = if let Some(&expected_type_id) = param_type_ids.get(i) {
                self.coerce_to_type(compiled, expected_type_id)?
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

        let word = results
            .first()
            .copied()
            .ok_or_else(|| CodegenError::internal("interface call missing return value"))?;
        let value = self.convert_from_i64_storage(word, return_type_id);

        // Convert Iterator return types to RuntimeIterator for interface dispatch
        // since external iterator methods return raw iterator pointers, not boxed interfaces
        let return_type_id = self.maybe_convert_iterator_return_type(return_type_id);

        Ok(self.compiled(value, return_type_id))
    }
}
