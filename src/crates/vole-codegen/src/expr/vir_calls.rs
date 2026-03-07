// src/codegen/expr/vir_calls.rs
//
// VIR call-target dispatch.  Each `CallTarget` variant gets a dedicated
// method that delegates to the existing codegen infrastructure.

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, native_type_to_cranelift};
use crate::union_layout;

use vole_identity::{MethodId, TypeDefId, TypeId, VirTypeId};
use vole_runtime::native_registry::NativeType;
use vole_vir::{CallTarget, VirRef};

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile a VIR call expression.
    ///
    /// Dispatches on `CallTarget` to select the correct calling convention.
    #[deny(clippy::wildcard_enum_match_arm)]
    pub fn compile_vir_call(
        &mut self,
        target: &CallTarget,
        args: &[VirRef],
        vir_ty: VirTypeId,
        result_is_fallible: bool,
    ) -> CodegenResult<CompiledValue> {
        let ty = self.vir_type_table().vir_to_type_id(vir_ty);
        match target {
            CallTarget::Direct { function_id } => {
                self.compile_vir_direct_call(*function_id, args, ty)
            }
            CallTarget::Lambda => self.compile_vir_lambda_call(args, ty, result_is_fallible),
            CallTarget::Intrinsic { key, line } => {
                self.compile_vir_intrinsic_call(*key, args, ty, *line)
            }
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
            CallTarget::GenericCall { .. } => {
                unreachable!("CallTarget::GenericCall must be resolved before codegen")
            }
            CallTarget::VirDirect { function_index } => {
                self.compile_vir_direct_call_by_index(*function_index, args, ty)
            }
            CallTarget::ClosureVariable {
                var_name,
                vir_type,
                resolved_call_args,
                lambda_defaults,
            } => self.compile_vir_closure_variable_call(
                *var_name,
                *vir_type,
                args,
                resolved_call_args.as_deref(),
                *lambda_defaults,
                ty,
            ),
            CallTarget::CapturedClosure {
                var_name,
                vir_type,
                resolved_call_args,
                lambda_defaults,
            } => self.compile_vir_captured_closure_call(
                *var_name,
                *vir_type,
                args,
                resolved_call_args.as_deref(),
                *lambda_defaults,
                ty,
            ),
            CallTarget::FunctionalInterface {
                var_name,
                vir_type,
                interface_type_def_id,
                method_id,
            } => self.compile_vir_functional_interface_call(
                *var_name,
                *vir_type,
                *interface_type_def_id,
                *method_id,
                args,
            ),
            CallTarget::GlobalClosure {
                var_name,
                resolved_call_args,
                lambda_defaults,
                monomorph_key,
            } => {
                self.vir_monomorph_key = monomorph_key.clone();
                self.compile_vir_global_closure_call(
                    *var_name,
                    args,
                    resolved_call_args.as_deref(),
                    *lambda_defaults,
                    ty,
                )
            }
            CallTarget::Unresolved {
                callee_sym,
                call_node_id,
                line,
                resolved_call_args,
                lambda_defaults,
                monomorph_key,
            } => {
                self.vir_monomorph_key = monomorph_key.clone();
                self.compile_vir_unresolved_call(
                    *callee_sym,
                    args,
                    *call_node_id,
                    *line,
                    resolved_call_args.as_deref(),
                    *lambda_defaults,
                    ty,
                )
            }
        }
    }

    /// Compile a direct call to a known function via its `FunctionId`.
    ///
    /// Resolves the sema `FunctionId` to a Cranelift `FuncId` through the
    /// entity registry and function registry, compiles VIR arguments, and
    /// emits the call instruction.
    ///
    /// Handles struct return conventions:
    /// - Small structs (1-2 flat slots): multi-value return in registers,
    ///   handled by `call_result`.
    /// - Large structs (3+ flat slots): sret convention with a hidden first
    ///   parameter pointing to a caller-allocated return buffer.
    ///
    /// For generator functions, the func_registry return type is overridden
    /// to `RuntimeIterator(T)` during pass 1 (via `override_generator_return_type`).
    /// We use the func_registry's return type for interpreting the call result
    /// so that downstream code sees the correct concrete type rather than the
    /// sema-level `Iterator<T>` interface type.
    fn compile_vir_direct_call(
        &mut self,
        function_id: vole_identity::FunctionId,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Resolve FunctionId -> NameId -> FunctionKey -> FuncId.
        // Use `name_id` (the key used by declare_function_by_name_id) rather
        // than `full_name_id` so the lookup matches the JIT registration.
        let func_def = self.analyzed().function_def(function_id);
        let name_id = func_def.name_id;
        let func_key = self.funcs().intern_name_id(name_id);
        let func_id = self
            .funcs_ref()
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("compiled function for VIR direct call", ""))?;

        // Use the func_registry's return type if available (may differ from VIR
        // type for generators, where pass 1 overrides it to RuntimeIterator(T)).
        let callee_return_ty = self
            .codegen_ctx
            .funcs()
            .return_type(func_key)
            .unwrap_or(return_ty);

        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        let is_sret = self.is_sret_struct_return(callee_return_ty);

        let (mut arg_values, mut rc_temps) = self.compile_vir_args(args)?;

        // For sret convention (large structs with 3+ flat slots), allocate a
        // stack buffer for the return value and prepend its pointer as the
        // first argument (hidden parameter).
        if is_sret && let Some(sret_ptr) = self.alloc_sret_ptr(callee_return_ty)? {
            arg_values.insert(0, sret_ptr);
        }

        let call_inst = self.emit_call(func_ref, &arg_values);

        // For union returns, copy the value out of the callee's stack frame
        // BEFORE RC temp cleanup — rc_dec calls may clobber the callee's
        // return slot (same ordering as call_func_id_impl).
        let union_copy = if !is_sret && self.vir_query_is_union(callee_return_ty) {
            let results = self.builder.inst_results(call_inst);
            let src_ptr = results[0];
            Some(self.copy_union_ptr_to_local(src_ptr, callee_return_ty))
        } else {
            None
        };

        self.consume_rc_args(&mut rc_temps)?;

        if let Some(result) = union_copy {
            return Ok(result);
        }

        // For sret, the returned value is the sret pointer we passed in.
        if is_sret {
            let results = self.builder.inst_results(call_inst);
            let ptr_type = self.ptr_type();
            let result = self.compiled_with_ty(results[0], ptr_type, callee_return_ty);
            return Ok(self.mark_rc_owned(result));
        }

        let result = self.call_result(call_inst, callee_return_ty)?;
        Ok(self.mark_rc_owned(result))
    }

    /// Compile a direct call to a VIR-monomorphized function by its index
    /// in `VirProgram.functions`.
    ///
    /// Looks up the pre-declared `FuncId` from `state.vir_direct_func_ids`,
    /// imports it into the current function, compiles VIR arguments, and
    /// emits the call instruction.
    fn compile_vir_direct_call_by_index(
        &mut self,
        function_index: usize,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let func_id = *self
            .env
            .state
            .vir_direct_func_ids
            .get(&function_index)
            .ok_or_else(|| {
                CodegenError::not_found("VirDirect function", format!("index {function_index}"))
            })?;

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
    ///
    /// If the closure value is an owned temporary (e.g. from an indirect call
    /// like `array[0]()`), it is RC-decremented after the call completes.
    fn compile_vir_lambda_call(
        &mut self,
        args: &[VirRef],
        return_ty: TypeId,
        result_is_fallible: bool,
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

        // RC-cleanup the closure value if it was an owned temporary (e.g.
        // indirect call like `array[0]()` produces an owned closure).
        let mut closure_val = closure_val;
        self.consume_rc_value(&mut closure_val)?;

        self.vir_closure_result(call_inst, return_ty, result_is_fallible)
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

        let abi =
            vole_vir::func::ReturnAbi::classify(self.vir_lookup(return_ty), self.vir_type_table());
        match abi {
            vole_vir::func::ReturnAbi::WideFallible => {
                sig.returns.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
            }
            vole_vir::func::ReturnAbi::Fallible => {
                sig.returns.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
            }
            vole_vir::func::ReturnAbi::Void => {}
            _ => {
                sig.returns
                    .push(AbiParam::new(self.vir_query_type_to_cranelift(return_ty)));
            }
        }

        Ok(sig)
    }

    /// Extract the result of a closure call, handling fallible/union return types.
    ///
    /// `result_is_fallible` is a VIR-lowering hint that short-circuits the
    /// type-table lookup.  When the hint is `false`, the fallback query is
    /// still performed so that generic/unresolved paths remain correct.
    fn vir_closure_result(
        &mut self,
        call_inst: cranelift_codegen::ir::Inst,
        return_ty: TypeId,
        result_is_fallible: bool,
    ) -> CodegenResult<CompiledValue> {
        let results = self.builder.inst_results(call_inst).to_vec();
        if results.is_empty() {
            return Ok(self.void_value());
        }

        if results.len() == 2 && (result_is_fallible || self.vir_query_is_fallible(return_ty)) {
            let tag = results[0];
            let payload = results[1];
            let slot = self.alloc_stack(union_layout::STANDARD_SIZE);
            self.builder.ins().stack_store(tag, slot, 0);
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            Ok(self.compiled_with_ty(ptr, ptr_type, return_ty))
        } else if self.vir_query_is_union(return_ty) {
            let src_ptr = results[0];
            Ok(self.copy_union_ptr_to_local(src_ptr, return_ty))
        } else {
            Ok(self.compiled(results[0], return_ty))
        }
    }

    /// Compile a compiler-intrinsic call (`CallTarget::Intrinsic`).
    ///
    /// Builtins (`Assert`, `PrintChar`) are handled inline; all other keys
    /// delegate to `call_compiler_intrinsic_key_typed_with_line`.
    fn compile_vir_intrinsic_call(
        &mut self,
        key: crate::IntrinsicKey,
        args: &[VirRef],
        return_ty: TypeId,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        use crate::IntrinsicKey;
        match key {
            IntrinsicKey::Assert => {
                let arg_source = crate::structs::methods::ArgSource(args);
                self.call_assert(&arg_source, line)
            }
            IntrinsicKey::PrintChar => {
                let arg_source = crate::structs::methods::ArgSource(args);
                self.call_print_char(&arg_source)
            }
            _ => {
                let typed_args = self.compile_vir_typed_args(args)?;
                self.call_compiler_intrinsic_key_typed_with_line(key, &typed_args, return_ty, line)
            }
        }
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
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        assert!(
            !args.is_empty(),
            "VIR VtableMethod call must have receiver as first arg"
        );

        let receiver = self.compile_vir_expr(&args[0])?;
        let word_type = self.ptr_type();
        let word_bytes = word_type.bytes() as i32;

        // Load vtable pointer from the boxed interface (second word)
        let vtable_ptr =
            self.builder
                .ins()
                .load(word_type, MemFlags::new(), receiver.value, word_bytes);
        // Slot 0 is the meta getter; method slots start at VTABLE_METHOD_OFFSET.
        let vtable_offset =
            (slot as i32 + crate::interfaces::vtable::VTABLE_METHOD_OFFSET as i32) * word_bytes;
        let func_ptr =
            self.builder
                .ins()
                .load(word_type, MemFlags::new(), vtable_ptr, vtable_offset);

        // Build signature: all params and return are word-typed (interface ABI)
        let is_void = self.vir_query_is_void(return_ty);
        let param_count = args.len(); // receiver + method params
        let mut sig = self.jit_module().make_signature();
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(word_type));
        }
        if !is_void {
            sig.returns.push(AbiParam::new(word_type));
        }

        // Compile remaining args as word values (interface dispatch uses i64 ABI)
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let mut call_args = Vec::with_capacity(args.len());
        call_args.push(receiver.value);
        for arg in &args[1..] {
            let compiled = self.compile_vir_expr(arg)?;
            let word = self.emit_word(&compiled, Some(heap_alloc_ref))?;
            call_args.push(word);
        }

        let sig_ref = self.import_sig_and_coerce_args(sig, &mut call_args);
        let call = self.emit_call_indirect(sig_ref, func_ptr, &call_args);
        let results = self.builder.inst_results(call);

        if is_void {
            return Ok(self.void_value());
        }
        let word = results
            .first()
            .copied()
            .ok_or_else(|| CodegenError::internal("vtable call missing return value"))?;
        let value = self.convert_from_i64_storage(word, return_ty);
        let return_ty = self.maybe_convert_iterator_return_type(return_ty);
        Ok(self.compiled(value, return_ty))
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
             needs per-method dispatch to existing builtin_method()/runtime_iterator_method() \
             infrastructure.  Each variant (ArrayLength, ArrayIter, StringIter, IterMap, …) \
             uses different runtime keys, elem_tag setup, RC ownership, and return-type \
             logic.  Delegate to builtin_methods.rs and iterator_methods.rs once VIR \
             lowering emits BuiltinMethod call nodes.",
            method
        )
    }

    /// Compile a native (FFI) call (`CallTarget::Native`).
    ///
    /// Resolves the module/function symbols, looks up the `NativeFunction` in
    /// the runtime registry, compiles VIR args, and emits the indirect call.
    fn compile_vir_native_call(
        &mut self,
        module_path: vole_identity::Symbol,
        native_name: vole_identity::Symbol,
        _abi: vole_vir::NativeAbi,
        args: &[VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let module_str = self.interner().resolve(module_path).to_string();
        let name_str = self.interner().resolve(native_name).to_string();
        let native_func = self
            .native_registry()
            .lookup(&module_str, &name_str)
            .ok_or_else(|| {
                CodegenError::not_found("native function", format!("{module_str}::{name_str}"))
            })?
            .clone();

        // Compile VIR args and coerce to the expected native parameter types
        let (arg_values, mut rc_temps) = self.compile_vir_args(args)?;
        let expected_types: Vec<Type> = native_func
            .signature
            .params
            .iter()
            .map(|nt| native_type_to_cranelift(nt, self.ptr_type()))
            .collect();
        let coerced: Vec<Value> = arg_values
            .iter()
            .zip(expected_types.iter())
            .map(|(&arg, &expected_ty)| {
                let actual_ty = self.builder.func.dfg.value_type(arg);
                self.coerce_cranelift_value(arg, actual_ty, expected_ty)
            })
            .collect();

        let call_inst = self.call_native_indirect(&native_func, &coerced);
        self.consume_rc_args(&mut rc_temps)?;

        if native_func.signature.return_type == NativeType::Nil {
            return Ok(self.void_value());
        }
        self.native_call_result(call_inst, &native_func, return_ty)
    }

    /// Compile an unresolved call by delegating to `call_dispatch()`.
    ///
    /// VIR lowering emits `CallTarget::Unresolved` for call expressions it
    /// could not fully classify (functions with defaults/sret/interface params,
    /// FFI, test-scoped functions, sema-fallback monomorphs, module bindings,
    /// prelude externals, and generic template calls).  See `CallTarget::Unresolved`
    /// for the full list.
    ///
    /// This method stashes the VIR-resolved named-arg mapping, lambda
    /// defaults, and return type, then passes the VIR-lowered `args` through
    /// `ArgSource::Vir` so all dispatch paths compile from VIR instead of
    /// the original AST.
    #[allow(clippy::too_many_arguments)]
    fn compile_vir_unresolved_call(
        &mut self,
        callee_sym: vole_identity::Symbol,
        args: &[VirRef],
        call_node_id: vole_identity::NodeId,
        line: u32,
        resolved_call_args: Option<&[Option<usize>]>,
        lambda_defaults: Option<vole_vir::LambdaDefaultsInfo>,
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let arg_source = crate::structs::methods::ArgSource(args);
        // Stash the VIR-resolved named-arg mapping, lambda defaults, and
        // return type so call_dispatch() sub-functions can read them.
        // The monomorph key is already stashed by the caller (`compile_vir_call`).
        self.vir_resolved_call_args = resolved_call_args.map(|m| m.to_vec());
        self.vir_lambda_defaults = lambda_defaults;
        self.vir_call_return_type = Some(return_ty);
        let result = self.call_dispatch(callee_sym, &arg_source, line, call_node_id);
        self.vir_resolved_call_args = None;
        self.vir_lambda_defaults = None;
        self.vir_monomorph_key = None;
        self.vir_call_return_type = None;
        result.map(|r| self.mark_rc_owned(r))
    }

    /// Compile a call to a local closure variable (`CallTarget::ClosureVariable`).
    ///
    /// Looks up the variable in `vars`, loads its value, stashes lambda
    /// defaults and named-arg mapping, then delegates to `call_closure`.
    fn compile_vir_closure_variable_call(
        &mut self,
        var_name: vole_identity::Symbol,
        vir_type: VirTypeId,
        args: &[VirRef],
        resolved_call_args: Option<&[Option<usize>]>,
        lambda_defaults: Option<vole_vir::LambdaDefaultsInfo>,
        _return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let (var, var_vir_ty) = self.vars.get(&var_name).copied().ok_or_else(|| {
            CodegenError::not_found("closure variable", self.interner().resolve(var_name))
        })?;
        let func_vir_ty = if self.vir_query_is_function_v(var_vir_ty) {
            var_vir_ty
        } else {
            vir_type
        };
        let arg_source = crate::structs::methods::ArgSource(args);
        self.vir_resolved_call_args = resolved_call_args.map(|m| m.to_vec());
        self.vir_lambda_defaults = lambda_defaults;
        let result = self.call_closure(
            var,
            func_vir_ty,
            &arg_source,
            vole_identity::NodeId::new(vole_identity::ModuleId::new(0), 0),
        );
        self.vir_resolved_call_args = None;
        self.vir_lambda_defaults = None;
        result.map(|r| self.mark_rc_owned(r))
    }

    /// Compile a call to a captured closure variable (`CallTarget::CapturedClosure`).
    ///
    /// Loads the capture from the closure environment, stashes lambda
    /// defaults and named-arg mapping, then delegates to `call_closure_value`.
    fn compile_vir_captured_closure_call(
        &mut self,
        var_name: vole_identity::Symbol,
        vir_type: VirTypeId,
        args: &[VirRef],
        resolved_call_args: Option<&[Option<usize>]>,
        lambda_defaults: Option<vole_vir::LambdaDefaultsInfo>,
        _return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let binding = self.get_capture(&var_name).copied().ok_or_else(|| {
            CodegenError::not_found("captured closure", self.interner().resolve(var_name))
        })?;
        let captured = self.load_capture(&binding)?;
        let func_vir_ty = if self.vir_query_is_function_v(binding.vole_type) {
            binding.vole_type
        } else {
            vir_type
        };
        let arg_source = crate::structs::methods::ArgSource(args);
        self.vir_resolved_call_args = resolved_call_args.map(|m| m.to_vec());
        self.vir_lambda_defaults = lambda_defaults;
        let result = self.call_closure_value(
            captured.value,
            func_vir_ty,
            &arg_source,
            vole_identity::NodeId::new(vole_identity::ModuleId::new(0), 0),
        );
        self.vir_resolved_call_args = None;
        self.vir_lambda_defaults = None;
        result.map(|r| self.mark_rc_owned(r))
    }

    /// Compile a call to a local variable that holds a functional interface
    /// value (`CallTarget::FunctionalInterface`).
    ///
    /// Loads the variable from `vars`, looks up the interface's single
    /// callable method, and dispatches via vtable.
    fn compile_vir_functional_interface_call(
        &mut self,
        var_name: vole_identity::Symbol,
        vir_type: VirTypeId,
        interface_type_def_id: TypeDefId,
        method_id: MethodId,
        args: &[VirRef],
    ) -> CodegenResult<CompiledValue> {
        let (var, var_vir_ty) = self.vars.get(&var_name).copied().ok_or_else(|| {
            CodegenError::not_found(
                "functional interface variable",
                self.interner().resolve(var_name),
            )
        })?;
        let value = self.builder.use_var(var);
        let use_vir_ty = if self.vir_query_is_interface_v(var_vir_ty) {
            var_vir_ty
        } else {
            vir_type
        };
        let obj = CompiledValue::new(value, self.cranelift_type_v(use_vir_ty), use_vir_ty);

        let method = self.analyzed().method_def(method_id);
        let func_type_id = method.signature_id;
        let method_name_id = method.name_id;

        let arg_source = crate::structs::methods::ArgSource(args);
        let result = self.interface_dispatch_call_args_by_type_def_id(
            &obj,
            &arg_source,
            interface_type_def_id,
            method_name_id,
            func_type_id,
        )?;
        Ok(self.mark_rc_owned(result))
    }

    /// Compile a call to a global variable that holds a closure or functional
    /// interface value (`CallTarget::GlobalClosure`).
    ///
    /// Compiles the global's VIR-lowered initializer, then dispatches as
    /// either a closure call or a functional interface call depending on the
    /// global's declared type.
    fn compile_vir_global_closure_call(
        &mut self,
        var_name: vole_identity::Symbol,
        args: &[VirRef],
        resolved_call_args: Option<&[Option<usize>]>,
        lambda_defaults: Option<vole_vir::LambdaDefaultsInfo>,
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let arg_source = crate::structs::methods::ArgSource(args);
        let placeholder_node_id = vole_identity::NodeId::new(vole_identity::ModuleId::new(0), 0);

        // Stash VIR-resolved named-arg mapping and lambda defaults.
        self.vir_resolved_call_args = resolved_call_args.map(|m| m.to_vec());
        self.vir_lambda_defaults = lambda_defaults;
        self.vir_call_return_type = Some(return_ty);

        let result = self.try_call_global(var_name, &arg_source, placeholder_node_id)?;

        self.vir_resolved_call_args = None;
        self.vir_lambda_defaults = None;
        self.vir_monomorph_key = None;
        self.vir_call_return_type = None;

        match result {
            Some(r) => Ok(self.mark_rc_owned(r)),
            None => Err(CodegenError::not_found(
                "global closure/function",
                self.interner().resolve(var_name),
            )),
        }
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
