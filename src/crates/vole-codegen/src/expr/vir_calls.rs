// src/codegen/expr/vir_calls.rs
//
// VIR call-target dispatch.  Each `CallTarget` variant gets a dedicated
// method that delegates to the existing codegen infrastructure.

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, is_wide_fallible, type_id_to_cranelift};
use crate::union_layout;

use vole_sema::type_arena::TypeId;
use vole_vir::{CallTarget, VirRef};

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile a VIR call expression.
    ///
    /// Dispatches on `CallTarget` to select the correct calling convention.
    pub fn compile_vir_call(
        &mut self,
        target: &CallTarget,
        args: &[VirRef],
        ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match target {
            CallTarget::Direct { function_id } => {
                self.compile_vir_direct_call(*function_id, args, ty)
            }
            CallTarget::Lambda => self.compile_vir_lambda_call(args, ty),
            CallTarget::Intrinsic { key } => self.compile_vir_intrinsic_call(*key, args, ty),
            CallTarget::IntrinsicRuntime { key } => {
                self.compile_vir_intrinsic_runtime_call(*key, args, ty)
            }
            CallTarget::VtableMethod { slot } => self.compile_vir_vtable_call(*slot, args, ty),
            CallTarget::BuiltinMethod { method } => {
                self.compile_vir_builtin_method_call(*method, args, ty)
            }
            CallTarget::Native {
                module_path,
                native_name,
                abi,
            } => self.compile_vir_native_call(*module_path, *native_name, *abi, args, ty),
        }
    }

    /// Compile a direct call to a known function via its `FunctionId`.
    ///
    /// Resolves the sema `FunctionId` to a Cranelift `FuncId` through the
    /// entity registry and function registry, compiles VIR arguments, and
    /// emits the call instruction.
    fn compile_vir_direct_call(
        &mut self,
        function_id: vole_identity::FunctionId,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Resolve FunctionId -> NameId -> FunctionKey -> FuncId
        let func_def = self.query().get_function(function_id);
        let full_name_id = func_def.full_name_id;
        let func_key = self.funcs().intern_name_id(full_name_id);
        let func_id = self
            .funcs_ref()
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("compiled function for VIR direct call", ""))?;

        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        let (arg_values, mut rc_temps) = self.compile_vir_args(args)?;
        let call_inst = self.emit_call(func_ref, &arg_values);
        self.consume_rc_args(&mut rc_temps)?;
        self.call_result(call_inst, return_ty)
    }

    /// Compile a lambda/closure call.
    ///
    /// The first VIR arg is the closure pointer; the remaining args are the
    /// actual parameters.  We extract the function pointer from the closure
    /// struct via `ClosureGetFunc`, build a signature, and emit an indirect call.
    fn compile_vir_lambda_call(
        &mut self,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        assert!(
            !args.is_empty(),
            "VIR Lambda call must have closure as first arg"
        );
        let closure_val = self.compile_vir_expr(&args[0])?;
        let closure_ptr = closure_val.value;

        // Extract the raw function pointer from the closure struct
        let func_ptr = self.call_runtime(RuntimeKey::ClosureGetFunc, &[closure_ptr])?;

        // Compile args once — use their Cranelift types to build the signature
        let mut call_args = Vec::with_capacity(args.len());
        let mut rc_temps = Vec::new();
        call_args.push(closure_ptr);
        for arg in &args[1..] {
            let compiled = self.compile_vir_expr(arg)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            call_args.push(compiled.value);
        }

        let sig = self.build_vir_lambda_sig(return_ty, &call_args[1..])?;
        let sig_ref = self.import_sig_and_coerce_args(sig, &mut call_args);
        let call_inst = self.emit_call_indirect(sig_ref, func_ptr, &call_args);
        self.consume_rc_args(&mut rc_temps)?;
        self.vir_closure_result(call_inst, return_ty)
    }

    /// Build a Cranelift `Signature` for a VIR lambda call.
    ///
    /// The first param is always the closure pointer; additional params are
    /// derived from the already-compiled argument `Value`s.
    fn build_vir_lambda_sig(
        &mut self,
        return_ty: TypeId,
        param_values: &[Value],
    ) -> CodegenResult<Signature> {
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr

        for &val in param_values {
            let ty = self.builder.func.dfg.value_type(val);
            sig.params.push(AbiParam::new(ty));
        }

        let arena = self.arena();
        if !arena.is_void(return_ty) {
            if is_wide_fallible(return_ty, arena) {
                sig.returns.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
            } else if arena.unwrap_fallible(return_ty).is_some() {
                sig.returns.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
            } else {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_ty,
                    arena,
                    self.ptr_type(),
                )));
            }
        }

        Ok(sig)
    }

    /// Extract the result of a closure call, handling fallible/union return types.
    fn vir_closure_result(
        &mut self,
        call_inst: cranelift_codegen::ir::Inst,
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let results = self.builder.inst_results(call_inst).to_vec();
        if results.is_empty() {
            return Ok(self.void_value());
        }

        let arena = self.arena();
        if results.len() == 2 && arena.unwrap_fallible(return_ty).is_some() {
            let tag = results[0];
            let payload = results[1];
            let slot = self.alloc_stack(union_layout::STANDARD_SIZE);
            self.builder.ins().stack_store(tag, slot, 0);
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            Ok(CompiledValue::new(ptr, ptr_type, return_ty))
        } else if arena.is_union(return_ty) {
            let src_ptr = results[0];
            Ok(self.copy_union_ptr_to_local(src_ptr, return_ty))
        } else {
            Ok(self.compiled(results[0], return_ty))
        }
    }

    /// Compile a compiler-intrinsic call (`CallTarget::Intrinsic`).
    ///
    /// Delegates to the existing `call_compiler_intrinsic_key_typed_with_line`
    /// method which handles both inline and runtime-backed intrinsics.
    fn compile_vir_intrinsic_call(
        &mut self,
        key: crate::IntrinsicKey,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let typed_args = self.compile_vir_typed_args(args)?;
        // Line 0: VIR nodes don't carry span info yet.
        self.call_compiler_intrinsic_key_typed_with_line(key, &typed_args, return_ty, 0)
    }

    /// Compile a runtime-intrinsic call (`CallTarget::IntrinsicRuntime`).
    ///
    /// Like `Intrinsic`, but always resolves to a runtime function call
    /// rather than an inline emission.  Delegates to the same intrinsic
    /// dispatch path.
    fn compile_vir_intrinsic_runtime_call(
        &mut self,
        key: crate::IntrinsicKey,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // IntrinsicRuntime uses the same dispatch path as Intrinsic — the
        // callable registry resolves IntrinsicKey to the correct RuntimeKey.
        let typed_args = self.compile_vir_typed_args(args)?;
        self.call_compiler_intrinsic_key_typed_with_line(key, &typed_args, return_ty, 0)
    }

    /// Compile a vtable method dispatch (`CallTarget::VtableMethod`).
    ///
    /// The first VIR arg is the interface-boxed receiver; remaining args
    /// are method parameters.  We load the function pointer from the vtable
    /// at the given slot and emit an indirect call.
    fn compile_vir_vtable_call(
        &mut self,
        slot: usize,
        _args: &[VirRef],
        _return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        todo!(
            "VIR CallTarget::VtableMethod(slot={}) — \
             requires interface dispatch lowering (not yet emitted by VIR lowering)",
            slot
        )
    }

    /// Compile a built-in method call (`CallTarget::BuiltinMethod`).
    ///
    /// Built-in methods on arrays, strings, ranges, and iterators are
    /// compiled via runtime calls or compiler intrinsics rather than
    /// user-defined function bodies.
    fn compile_vir_builtin_method_call(
        &mut self,
        method: vole_vir::BuiltinMethod,
        _args: &[VirRef],
        _return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        todo!(
            "VIR CallTarget::BuiltinMethod({:?}) — \
             requires method call lowering (not yet emitted by VIR lowering)",
            method
        )
    }

    /// Compile a native (FFI) call (`CallTarget::Native`).
    fn compile_vir_native_call(
        &mut self,
        _module_path: vole_identity::Symbol,
        _native_name: vole_identity::Symbol,
        _abi: vole_vir::NativeAbi,
        _args: &[VirRef],
        _return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        todo!(
            "VIR CallTarget::Native — \
             requires FFI call lowering (not yet emitted by VIR lowering)",
        )
    }

    // =====================================================================
    // Helpers
    // =====================================================================

    /// Compile VIR args into raw `Value`s plus a list of owned RC temps.
    fn compile_vir_args(
        &mut self,
        args: &[VirRef],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let mut values = Vec::with_capacity(args.len());
        let mut rc_temps = Vec::new();
        for arg in args {
            let compiled = self.compile_vir_expr(arg)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            values.push(compiled.value);
        }
        Ok((values, rc_temps))
    }

    /// Compile VIR args into typed `CompiledValue`s (for intrinsic dispatch).
    fn compile_vir_typed_args(&mut self, args: &[VirRef]) -> CodegenResult<Vec<CompiledValue>> {
        args.iter().map(|arg| self.compile_vir_expr(arg)).collect()
    }
}
