// calls/mod.rs
//
// Call-related codegen - impl Cg methods and standalone helpers.
//
// Submodules:
//   closure_calls  - closure call compilation and signature building
//   lambda_search  - AST traversal to find lambda expressions by NodeId
//   native_calls   - native (FFI) call compilation, generic externals, monomorphization
//   string_ops     - string literal, interpolation, and value-to-string conversion

mod closure_calls;
mod lambda_search;
mod native_calls;
mod string_ops;

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::errors::{CodegenError, CodegenResult};

use vole_frontend::ast::CallExpr;
use vole_frontend::{Expr, ExprKind, NodeId, Symbol};
use vole_identity::NameId;
use vole_sema::type_arena::TypeId;

use super::context::{Cg, deref_expr_ptr};
use super::types::CompiledValue;
use super::{FunctionKey, RuntimeKey};

use cranelift_module::FuncId;

impl Cg<'_, '_, '_> {
    /// Compile a function call
    #[tracing::instrument(skip(self, call))]
    pub fn call(
        &mut self,
        call: &CallExpr,
        call_line: u32,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let callee_sym = match &call.callee.kind {
            ExprKind::Identifier(sym) => *sym,
            _ => return self.indirect_call(call),
        };

        let callee_name = self.interner().resolve(callee_sym);

        // Handle builtins
        // assert uses inline codegen (brif) to avoid function-call overhead
        // and a pre-existing class-field-access register clobber bug (v-a1f9).
        match callee_name {
            "print_char" => return self.call_print_char(call),
            "assert" => return self.call_assert(call, call_line),
            _ => {}
        }

        // Check if it's a module binding (from destructuring import)
        if let Some(&(module_id, export_name, _)) = self.module_bindings.get(&callee_sym) {
            // Check if this is a generic external function that needs monomorphization
            if let Some(result) =
                self.try_call_generic_external_intrinsic_from_monomorph(call_expr_id, call)?
            {
                return Ok(result);
            }

            return self.call_module_binding(module_id, export_name, call, call_expr_id);
        }

        // Check if it's a closure variable
        if let Some((var, type_id)) = self.vars.get(&callee_sym)
            && self.arena().is_function(*type_id)
        {
            return self.call_closure(*var, *type_id, call, call_expr_id);
        }

        // Check if it's a captured closure (e.g., recursive lambda or captured function)
        if self.has_captures()
            && let Some(binding) = self.get_capture(&callee_sym).copied()
            && self.arena().is_function(binding.vole_type)
        {
            let captured = self.load_capture(&binding)?;
            return self.call_closure_value(captured.value, binding.vole_type, call, call_expr_id);
        }

        // Check if it's a functional interface variable
        if let Some((var, type_id)) = self.vars.get(&callee_sym) {
            let value = self.builder.use_var(*var);
            let obj = CompiledValue::new(value, self.cranelift_type(*type_id), *type_id);
            if let Some(result) = self.try_call_functional_interface(&obj, &call.args)? {
                return Ok(result);
            }
        }

        // Check if it's a global lambda or global functional interface
        if let Some(result) = self.try_call_global(callee_sym, call)? {
            return Ok(result);
        }

        // Check if this is a call to a generic function (via monomorphization)
        // Use module-aware lookup to handle per-module NodeId spaces correctly.
        if let Some(result) =
            self.try_call_monomorphized_function(call_expr_id, call, callee_sym, callee_name)?
        {
            return Ok(result);
        }

        // Regular function call - handle module context
        // 1. Try direct function lookup
        // 2. If in module context, try mangled name
        // 3. If in module context, try FFI call
        let program_module = self.current_module().unwrap_or(self.env.analyzed.module_id);
        let direct_name_id = {
            let names = self.name_table();
            names.name_id(program_module, &[callee_sym], self.interner())
        };
        if let Some(name_id) = direct_name_id {
            let func_key = self.funcs().intern_name_id(name_id);
            if let Some(func_id) = self.funcs_ref().func_id(func_key) {
                return self.call_func_id(func_key, func_id, call, callee_sym, call_expr_id);
            }
        }

        // Check module context for mangled name or FFI
        if let Some(module_id) = self.current_module() {
            let module_path = self.name_table().module_path(module_id).to_string();
            let name_id = crate::types::module_name_id(self.analyzed(), module_id, callee_name);
            if let Some(name_id) = name_id {
                let func_key = self.funcs().intern_name_id(name_id);
                if let Some(func_id) = self.funcs().func_id(func_key) {
                    // Found module function with qualified name
                    return self.call_func_id(func_key, func_id, call, callee_sym, call_expr_id);
                }
            }

            // Try FFI call for external module functions
            if let Some(native_func) = self.native_registry().lookup(&module_path, callee_name) {
                return self.call_native_external(native_func, callee_sym, call, &call_expr_id);
            }

            // Fall through to try prelude external functions
        }

        // Try prelude external functions (works in module context too)
        // Look up the external info (module path and native name) from implement_registry
        let ext_info = self
            .analyzed()
            .implement_registry()
            .get_external_func(callee_name)
            .copied();
        if let Some(ref info) = ext_info {
            // Check if this is a compiler intrinsic (e.g., panic)
            let module_path_str = self
                .name_table()
                .last_segment_str(info.module_path)
                .unwrap_or_default();
            if module_path_str == Cg::COMPILER_INTRINSIC_MODULE {
                // Compile args and dispatch through intrinsic handler
                let mut args = Vec::new();
                for arg in &call.args {
                    args.push(self.expr(arg)?);
                }
                let native_name_str = self
                    .name_table()
                    .last_segment_str(info.native_name)
                    .unwrap_or_default();
                let return_type_id = self
                    .get_expr_type(&call_expr_id)
                    .expect("INTERNAL: compiler intrinsic call: missing sema return type");
                return self.call_compiler_intrinsic_key_typed_with_line(
                    crate::IntrinsicKey::from(native_name_str.as_str()),
                    &args,
                    return_type_id,
                    call_line,
                );
            }
        }
        let native_lookup = ext_info.as_ref().and_then(|info| {
            let name_table = self.name_table();
            let module_path = name_table.last_segment_str(info.module_path)?;
            let native_name = name_table.last_segment_str(info.native_name)?;
            let func = self.native_registry().lookup(&module_path, &native_name)?;
            Some((module_path.to_string(), native_name.to_string(), func))
        });
        if let Some((_module_path, _native_name, native_func)) = native_lookup {
            return self.call_native_external(native_func, callee_sym, call, &call_expr_id);
        }

        // Try prelude Vole functions (e.g., assert from builtins.vole)
        let prelude_paths: Vec<String> = self
            .query()
            .module_paths()
            .filter(|p| p.starts_with("std:prelude/"))
            .map(String::from)
            .collect();
        for module_path in &prelude_paths {
            let module_id = self.query().module_id_or_main(module_path);
            let name_id = crate::types::module_name_id(self.analyzed(), module_id, callee_name);
            if let Some(name_id) = name_id {
                let func_key = self.funcs().intern_name_id(name_id);
                if let Some(func_id) = self.funcs_ref().func_id(func_key) {
                    return self.call_func_id_by_name_id(
                        func_key,
                        func_id,
                        call,
                        name_id,
                        call_expr_id,
                    );
                }
            }
        }

        Err(CodegenError::not_found("function", callee_name))
    }

    /// Try to call a global lambda or global functional interface.
    ///
    /// Returns `Some(result)` if the callee is a global with a lambda or interface
    /// initializer, `None` otherwise.
    fn try_call_global(
        &mut self,
        callee_sym: Symbol,
        call: &CallExpr,
    ) -> CodegenResult<Option<CompiledValue>> {
        let init_expr = match self.global_init(callee_sym).cloned() {
            Some(expr) => expr,
            None => return Ok(None),
        };

        // Compile the global's initializer to get its value
        let lambda_val = self.expr(&init_expr)?;

        // Get declared type from GlobalDef (uses sema-resolved type, not TypeExpr)
        // Scope the name_table borrow to avoid conflicts with later mutable borrows
        let global_type_id = {
            let name_table = self.name_table();
            let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);
            name_table
                .name_id(module_id, &[callee_sym], self.interner())
                .and_then(|name_id| self.query().global(name_id))
                .map(|global_def| global_def.type_id)
        };

        if let Some(declared_type_id) = global_type_id {
            // If declared as functional interface, call via vtable dispatch
            let iface_info = self.interface_type_def_id(declared_type_id);
            if let Some(type_def_id) = iface_info
                && let Some(method_id) = self.query().is_functional_interface(type_def_id)
            {
                let method = self.query().get_method(method_id);
                let func_type_id = method.signature_id;
                let method_name_id = method.name_id;
                // Box the lambda value to create the interface representation
                let boxed = self.box_interface_value(lambda_val, declared_type_id)?;
                let result = self.interface_dispatch_call_args_by_type_def_id(
                    &boxed,
                    &call.args,
                    type_def_id,
                    method_name_id,
                    func_type_id,
                )?;
                // Dec the boxed interface instance (which transitively frees
                // the closure via instance_drop).
                self.emit_rc_dec_for_type(boxed.value, boxed.type_id)?;
                return Ok(Some(result));
            }
        }

        // If it's a function type, call as closure
        // Note: Global lambdas don't support default params lookup (use call.callee.id as placeholder)
        if self.arena().is_function(lambda_val.type_id) {
            let result = self.call_closure_value(
                lambda_val.value,
                lambda_val.type_id,
                call,
                call.callee.id,
            )?;
            // The global init re-compiles the lambda each call, creating a
            // fresh closure allocation. Dec it now that the call has finished.
            let mut tmp = lambda_val;
            self.consume_rc_value(&mut tmp)?;
            return Ok(Some(result));
        }

        // If it's an interface type (functional interface), call via vtable
        if let Some(result) = self.try_call_functional_interface(&lambda_val, &call.args)? {
            // Dec the interface instance created by the global init.
            self.emit_rc_dec_for_type(lambda_val.value, lambda_val.type_id)?;
            return Ok(Some(result));
        }

        Ok(None)
    }

    /// Call a function by its FuncId, using Symbol to look up NameId for param types/defaults.
    pub(super) fn call_func_id(
        &mut self,
        func_key: FunctionKey,
        func_id: FuncId,
        call: &CallExpr,
        callee_sym: Symbol,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Look up the function's NameId for param types and default args.
        // Use self.interner() (not self.query()) because callee_sym comes from the
        // current AST, which may be a module with its own interner. ProgramQuery
        // always uses the main program's interner, causing index-out-of-bounds when
        // a module Symbol index exceeds the main interner's size.
        let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);
        let name_id = self
            .name_table()
            .name_id(module_id, &[callee_sym], self.interner());
        let return_type_override = self.get_expr_type_substituted(&call_expr_id);
        self.call_func_id_impl(func_key, func_id, call, name_id, None, return_type_override)
    }

    /// Call a function by FuncId using NameId for default parameter lookup.
    /// Used for prelude Vole functions where the callee's NameId is already known.
    fn call_func_id_by_name_id(
        &mut self,
        func_key: FunctionKey,
        func_id: FuncId,
        call: &CallExpr,
        name_id: NameId,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let return_type_override = self.get_expr_type_substituted(&call_expr_id);
        self.call_func_id_impl(
            func_key,
            func_id,
            call,
            Some(name_id),
            None,
            return_type_override,
        )
    }

    /// Core implementation for calling a function by FuncId.
    /// Takes an optional NameId for looking up parameter types and default arguments.
    pub(super) fn call_func_id_impl(
        &mut self,
        func_key: FunctionKey,
        func_id: FuncId,
        call: &CallExpr,
        name_id: Option<NameId>,
        param_type_ids_override: Option<Vec<TypeId>>,
        return_type_id_override: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        // Get return type early to check for sret convention.
        // Return type is always set when the function is declared/compiled.
        let callee_return_type_id = self
            .codegen_ctx
            .funcs()
            .return_type(func_key)
            .expect("INTERNAL: function call: missing return type in registry");
        let return_type_id = return_type_id_override.unwrap_or(callee_return_type_id);

        let is_sret = self.is_sret_struct_return(callee_return_type_id);

        // Get expected parameter types from the function's signature
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let sig = &self.builder.func.dfg.signatures[sig_ref];
        let expected_types: Vec<Type> = sig.params.iter().map(|p| p.value_type).collect();

        // For sret convention, allocate return buffer and prepend as first arg
        let ptr_type = self.ptr_type();
        let mut args = Vec::new();
        let sret_slot = if is_sret {
            let flat_count = self
                .struct_flat_slot_count(callee_return_type_id)
                .expect("INTERNAL: sret call: missing flat slot count");
            let total_size = (flat_count as u32) * 8;
            let slot = self.alloc_stack(total_size);
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            args.push(ptr);
            Some(slot)
        } else {
            None
        };

        // Determine the offset into expected_types for user args (skip sret param)
        let user_param_offset = if is_sret { 1 } else { 0 };

        // Get parameter TypeIds from the function definition for union coercion
        let param_type_ids: Vec<TypeId> = param_type_ids_override.unwrap_or_else(|| {
            let func_id_sema = name_id.and_then(|id| self.registry().function_by_name(id));
            if let Some(fid) = func_id_sema {
                let func_def = self.registry().get_function(fid);
                func_def.signature.params_id.iter().copied().collect()
            } else {
                Vec::new()
            }
        });

        // Compile arguments with type narrowing, tracking RC temps for cleanup
        let mut rc_temp_args = Vec::new();
        for (i, arg) in call.args.iter().enumerate() {
            let compiled = if let Some(&param_type_id) = param_type_ids.get(i) {
                self.expr_with_expected_type(arg, param_type_id)?
            } else {
                self.expr(arg)?
            };
            if compiled.is_owned() {
                rc_temp_args.push(compiled);
            }

            // Coerce argument to parameter type if needed (e.g., string -> string?)
            let compiled = if let Some(&param_type_id) = param_type_ids.get(i) {
                self.coerce_to_type(compiled, param_type_id)?
            } else {
                compiled
            };

            let expected_ty = expected_types.get(i + user_param_offset).copied();

            // Narrow/extend integer types or promote/demote floats if needed
            let arg_value = if let Some(expected) = expected_ty {
                if compiled.ty.is_int() && expected.is_int() && expected.bits() < compiled.ty.bits()
                {
                    self.builder.ins().ireduce(expected, compiled.value)
                } else if compiled.ty.is_int()
                    && expected.is_int()
                    && expected.bits() > compiled.ty.bits()
                {
                    self.builder.ins().sextend(expected, compiled.value)
                } else if compiled.ty == types::F32 && expected == types::F64 {
                    self.builder.ins().fpromote(types::F64, compiled.value)
                } else if compiled.ty == types::F64 && expected == types::F32 {
                    self.builder.ins().fdemote(types::F32, compiled.value)
                } else {
                    compiled.value
                }
            } else {
                compiled.value
            };
            args.push(arg_value);
        }

        // If there are fewer provided args than expected, compile default expressions
        let total_user_args = args.len() - user_param_offset;
        let expected_user_params = expected_types.len() - user_param_offset;
        if total_user_args < expected_user_params
            && let Some(name_id) = name_id
        {
            let provided_args = total_user_args;
            let (default_args, rc_owned) =
                self.compile_default_args_with_types(name_id, provided_args, &param_type_ids)?;
            args.extend(default_args);
            rc_temp_args.extend(rc_owned);
        }

        let args = self.coerce_call_args(func_ref, &args);
        let call_inst = self.builder.ins().call(func_ref, &args);
        self.field_cache.clear(); // Callee may mutate instance fields

        // For union returns, copy the value out of the callee's stack frame
        // before RC temp cleanup. rc_dec may clobber the callee return slot.
        let union_copy = if sret_slot.is_none() && self.arena().is_union(callee_return_type_id) {
            let results = self.builder.inst_results(call_inst);
            let src_ptr = results[0];
            Some(self.copy_union_ptr_to_local(src_ptr, callee_return_type_id))
        } else {
            None
        };

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temp_args)?;

        if let Some(result) = union_copy {
            let mut result = result;
            if return_type_id != callee_return_type_id {
                result = self.coerce_to_type(result, return_type_id)?;
            }
            return Ok(result);
        }

        // For sret, the returned value is the sret pointer we passed in
        if sret_slot.is_some() {
            let results = self.builder.inst_results(call_inst);
            let mut result = CompiledValue::new(results[0], ptr_type, callee_return_type_id);
            if return_type_id != callee_return_type_id {
                result = self.coerce_to_type(result, return_type_id)?;
            }
            return Ok(result);
        }

        let mut result = self.call_result(call_inst, callee_return_type_id);
        if return_type_id != callee_return_type_id {
            result = self.coerce_to_type(result, return_type_id)?;
        }
        Ok(result)
    }

    fn compile_default_args_with_types(
        &mut self,
        name_id: NameId,
        start_index: usize,
        param_type_ids_override: &[TypeId],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let func_id = self.registry().function_by_name(name_id);
        let Some(func_id) = func_id else {
            return Ok((Vec::new(), Vec::new()));
        };

        let (default_ptrs, param_type_ids): (Vec<Option<*const Expr>>, Vec<TypeId>) = {
            let func_def = self.registry().get_function(func_id);
            let ptrs = func_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect();
            let type_ids = func_def.signature.params_id.iter().copied().collect();
            (ptrs, type_ids)
        };

        let param_type_ids = if param_type_ids_override.is_empty() {
            param_type_ids
        } else {
            param_type_ids_override.to_vec()
        };

        self.compile_defaults_from_ptrs(
            &default_ptrs,
            start_index,
            &param_type_ids[start_index..],
            false,
        )
    }

    /// Compile call arguments for an external function, including defaults for omitted parameters.
    /// Looks up the function by Symbol in EntityRegistry to get default expressions.
    /// `expected_types` are the Cranelift types from the native function signature.
    pub(super) fn compile_external_call_args(
        &mut self,
        callee_sym: Symbol,
        call: &CallExpr,
        expected_types: &[Type],
    ) -> CodegenResult<Vec<Value>> {
        // Compile provided arguments
        let mut args = self.compile_call_args(&call.args)?;

        let expected_param_count = expected_types.len();

        // If we have all expected arguments, we're done
        if args.len() >= expected_param_count {
            return Ok(args);
        }

        // Otherwise, we need to compile defaults for the missing parameters
        let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);

        // Get the function ID from EntityRegistry.
        // Use self.interner() to resolve module-local Symbols correctly (see call_func_id).
        let func_id = {
            let name_id = self
                .name_table()
                .name_id(module_id, &[callee_sym], self.interner());
            name_id.and_then(|id| self.registry().function_by_name(id))
        };

        let Some(func_id) = func_id else {
            return Ok(args);
        };

        // Get raw pointers to default expressions.
        // These point to data in EntityRegistry which lives for the duration of AnalyzedProgram.
        // We use raw pointers to work around the borrow checker since self.expr() needs &mut self.
        let default_ptrs: Vec<Option<*const Expr>> = {
            let func_def = self.registry().get_function(func_id);
            func_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect()
        };

        // Compile defaults for missing parameters
        let start_index = args.len();
        for (param_idx, &expected_ty) in expected_types
            .iter()
            .enumerate()
            .skip(start_index)
            .take(expected_param_count - start_index)
        {
            if let Some(Some(default_ptr)) = default_ptrs.get(param_idx) {
                let default_expr = deref_expr_ptr(*default_ptr);
                let compiled = self.expr(default_expr)?;

                // Narrow/extend integer types or promote/demote floats if needed
                let arg_value = if compiled.ty.is_int()
                    && expected_ty.is_int()
                    && expected_ty.bits() < compiled.ty.bits()
                {
                    self.builder.ins().ireduce(expected_ty, compiled.value)
                } else if compiled.ty.is_int()
                    && expected_ty.is_int()
                    && expected_ty.bits() > compiled.ty.bits()
                {
                    self.builder.ins().sextend(expected_ty, compiled.value)
                } else if compiled.ty == types::F32 && expected_ty == types::F64 {
                    self.builder.ins().fpromote(types::F64, compiled.value)
                } else if compiled.ty == types::F64 && expected_ty == types::F32 {
                    self.builder.ins().fdemote(types::F32, compiled.value)
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }

        Ok(args)
    }

    /// Compile an indirect call (closure or function value)
    fn indirect_call(&mut self, call: &CallExpr) -> CodegenResult<CompiledValue> {
        let callee = self.expr(&call.callee)?;

        if self.arena().is_function(callee.type_id) {
            // Note: Indirect calls don't support default params lookup (use callee.id as placeholder)
            return self.call_closure_value(callee.value, callee.type_id, call, call.callee.id);
        }

        Err(CodegenError::type_mismatch(
            "call expression",
            "function",
            "non-function",
        ))
    }

    /// Compile print_char builtin for ASCII output
    fn call_print_char(&mut self, call: &CallExpr) -> CodegenResult<CompiledValue> {
        if call.args.len() != 1 {
            return Err(CodegenError::arg_count("print_char", 1, call.args.len()));
        }

        let arg = self.expr(&call.args[0])?;

        // Convert to u8 if needed (truncate from i64)
        let char_val = if arg.ty == types::I64 {
            self.builder.ins().ireduce(types::I8, arg.value)
        } else if arg.ty == types::I8 {
            arg.value
        } else {
            return Err(CodegenError::type_mismatch(
                "print_char argument",
                "i32 or i64",
                "non-integer",
            ));
        };

        self.call_runtime_void(RuntimeKey::PrintChar, &[char_val])?;
        Ok(self.void_value())
    }

    /// Compile assert as inline codegen.
    /// Uses brif + assert_fail instead of a function call to avoid
    /// a pre-existing class-field-access register clobber bug (v-a1f9).
    fn call_assert(&mut self, call: &CallExpr, call_line: u32) -> CodegenResult<CompiledValue> {
        if call.args.is_empty() {
            return Err(CodegenError::arg_count("assert", 1, 0));
        }

        let cond = self.expr(&call.args[0])?;
        let cond_i32 = self.cond_to_i32(cond.value);

        let pass_block = self.builder.create_block();
        let fail_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(cond_i32, pass_block, &[], fail_block, &[]);

        self.switch_and_seal(fail_block);

        // vole_assert_fail(file_ptr, file_len, line)
        let (file_ptr, file_len) = self.source_file();
        let ptr_type = self.ptr_type();
        let file_ptr_val = self.builder.ins().iconst(ptr_type, file_ptr as i64);
        let file_len_val = self.builder.ins().iconst(ptr_type, file_len as i64);
        let line_val = self.builder.ins().iconst(types::I32, call_line as i64);

        self.call_runtime_void(
            RuntimeKey::AssertFail,
            &[file_ptr_val, file_len_val, line_val],
        )?;
        self.builder.ins().jump(pass_block, &[]);

        self.switch_and_seal(pass_block);

        Ok(self.void_value())
    }

    /// Emit a panic with a static message at the given line.
    /// Used for runtime errors like division by zero that don't have a user-provided message.
    /// Returns Ok(()) on success, but note that control flow doesn't continue after this
    /// (an unreachable block is created for any following code).
    pub fn emit_panic_static(&mut self, msg: &str, line: u32) -> CodegenResult<()> {
        // Create the message string constant
        let msg_val = self.string_literal(msg)?;

        // vole_panic(msg, file_ptr, file_len, line)
        let (file_ptr, file_len) = self.source_file();
        let ptr_type = self.ptr_type();
        let file_ptr_val = self.builder.ins().iconst(ptr_type, file_ptr as i64);
        let file_len_val = self.builder.ins().iconst(ptr_type, file_len as i64);
        let line_val = self.builder.ins().iconst(types::I32, line as i64);

        self.call_runtime_void(
            RuntimeKey::Panic,
            &[msg_val.value, file_ptr_val, file_len_val, line_val],
        )?;

        // Since panic never returns, emit trap and create unreachable block
        self.builder.ins().trap(crate::trap_codes::PANIC);

        // Create an unreachable block for code that follows the panic call
        let unreachable_block = self.builder.create_block();
        self.switch_and_seal(unreachable_block);

        Ok(())
    }
}
