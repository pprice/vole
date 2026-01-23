// src/codegen/calls.rs
//
// Call-related codegen - impl Cg methods and standalone helpers.

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};
use smallvec::{SmallVec, smallvec};

use crate::errors::CodegenError;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use vole_frontend::{CallExpr, ExprKind, NodeId, StringPart};
use vole_runtime::native_registry::{NativeFunction, NativeType};
use vole_sema::type_arena::{TypeArena, TypeId};

use super::context::Cg;
use super::types::{CompiledValue, native_type_to_cranelift, type_id_to_cranelift};
use super::{FunctionKey, FunctionRegistry, RuntimeFn};

/// Compile a string literal by calling vole_string_new.
/// Returns the raw Cranelift Value - caller should wrap with string_value() for CompiledValue.
pub(crate) fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: Type,
    module: &mut JITModule,
    func_registry: &FunctionRegistry,
) -> Result<Value, String> {
    // Get the vole_string_new function
    let func_id = func_registry
        .runtime_key(RuntimeFn::StringNew)
        .and_then(|key| func_registry.func_id(key))
        .ok_or_else(|| {
            CodegenError::not_found("runtime function", "vole_string_new").to_string()
        })?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    // Pass the string data pointer and length as constants
    // The string is a Rust &str, so we can get its pointer and length
    let data_ptr = s.as_ptr() as i64;
    let len = s.len() as i64;

    let data_val = builder.ins().iconst(pointer_type, data_ptr);
    let len_val = builder.ins().iconst(pointer_type, len);

    // Call vole_string_new(data, len) -> *mut RcString
    let call = builder.ins().call(func_ref, &[data_val, len_val]);
    Ok(builder.inst_results(call)[0])
}
impl Cg<'_, '_, '_> {
    /// Compile a string literal
    pub fn string_literal(&mut self, s: &str) -> Result<CompiledValue, String> {
        let value = compile_string_literal(
            self.builder,
            s,
            self.ptr_type(),
            self.codegen_ctx.module,
            self.codegen_ctx.func_registry,
        )?;
        Ok(self.string_value(value))
    }

    /// Compile an interpolated string
    pub fn interpolated_string(&mut self, parts: &[StringPart]) -> Result<CompiledValue, String> {
        if parts.is_empty() {
            return self.string_literal("");
        }

        let mut string_values: Vec<Value> = Vec::new();
        for part in parts {
            let str_val = match part {
                StringPart::Literal(s) => self.string_literal(s)?.value,
                StringPart::Expr(expr) => {
                    let compiled = self.expr(expr)?;
                    self.value_to_string(compiled)?
                }
            };
            string_values.push(str_val);
        }

        if string_values.len() == 1 {
            return Ok(self.string_value(string_values[0]));
        }

        let concat_key = self
            .funcs()
            .runtime_key(RuntimeFn::StringConcat)
            .ok_or_else(|| "vole_string_concat not found".to_string())?;
        let concat_func_ref = self.func_ref(concat_key)?;
        let mut result = string_values[0];
        for &next in &string_values[1..] {
            let call = self.builder.ins().call(concat_func_ref, &[result, next]);
            result = self.builder.inst_results(call)[0];
        }

        Ok(self.string_value(result))
    }

    /// Convert a value to a string
    fn value_to_string(&mut self, val: CompiledValue) -> Result<Value, String> {
        if val.type_id == TypeId::STRING {
            return Ok(val.value);
        }

        // Handle arrays
        if self.arena().is_array(val.type_id) {
            return self.call_runtime(RuntimeFn::ArrayI64ToString, &[val.value]);
        }

        // Handle nil type directly
        if val.type_id.is_nil() {
            return self.call_runtime(RuntimeFn::NilToString, &[]);
        }

        // Handle optionals (unions with nil variant)
        if let Some(nil_idx) = self.find_nil_variant(val.type_id) {
            let arena = self.arena();
            if let Some(variants) = arena.unwrap_union(val.type_id) {
                let variants_vec: Vec<TypeId> = variants.to_vec();
                drop(arena);
                return self.optional_to_string_by_id(val.value, &variants_vec, nil_idx);
            }
        }

        let (runtime, call_val) = if val.ty == types::F64 {
            (RuntimeFn::F64ToString, val.value)
        } else if val.ty == types::I8 {
            (RuntimeFn::BoolToString, val.value)
        } else {
            let extended = if val.ty.is_int() && val.ty != types::I64 {
                self.builder.ins().sextend(types::I64, val.value)
            } else {
                val.value
            };
            (RuntimeFn::I64ToString, extended)
        };

        self.call_runtime(runtime, &[call_val])
    }

    /// Convert an optional (union with nil) to string using TypeId variants
    fn optional_to_string_by_id(
        &mut self,
        ptr: Value,
        variants: &[TypeId],
        nil_idx: usize,
    ) -> Result<Value, String> {
        // Check if the tag equals nil
        let is_nil = self.tag_eq(ptr, nil_idx as i64);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let some_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add block param for the result string
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], some_block, &[]);

        // Nil case: return "nil"
        self.builder.switch_to_block(nil_block);
        let nil_str = self.call_runtime(RuntimeFn::NilToString, &[])?;
        self.builder.ins().jump(merge_block, &[nil_str.into()]);

        // Some case: extract inner value and convert to string
        self.builder.switch_to_block(some_block);
        // Find the non-nil variant using arena
        let arena = self.arena();
        let inner_type_id = variants
            .iter()
            .find(|&&v| !arena.is_nil(v))
            .copied()
            .unwrap_or(TypeId::NIL);
        let inner_cr_type = type_id_to_cranelift(inner_type_id, &arena, self.ptr_type());
        drop(arena);

        let inner_val = self
            .builder
            .ins()
            .load(inner_cr_type, MemFlags::new(), ptr, 8);

        let inner_compiled = CompiledValue {
            value: inner_val,
            ty: inner_cr_type,
            type_id: inner_type_id,
        };
        let some_str = self.value_to_string(inner_compiled)?;
        self.builder.ins().jump(merge_block, &[some_str.into()]);

        // Merge and return result
        self.builder.switch_to_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Compile a function call
    #[tracing::instrument(skip(self, call))]
    pub fn call(
        &mut self,
        call: &CallExpr,
        call_line: u32,
        call_expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        let callee_sym = match &call.callee.kind {
            ExprKind::Identifier(sym) => *sym,
            _ => return self.indirect_call(call),
        };

        let callee_name = self.interner().resolve(callee_sym);

        // Handle builtins
        match callee_name {
            "print" | "println" => return self.call_println(call, callee_name == "println"),
            "print_char" => return self.call_print_char(call),
            "assert" => return self.call_assert(call, call_line),
            _ => {}
        }

        // Check if it's a closure variable
        if let Some((var, type_id)) = self.vars.get(&callee_sym)
            && self.arena().is_function(*type_id)
        {
            return self.call_closure(*var, *type_id, call);
        }

        // Check if it's a captured closure (e.g., recursive lambda or captured function)
        if self.has_captures()
            && let Some(binding) = self.get_capture(&callee_sym).copied()
            && self.arena().is_function(binding.vole_type)
        {
            let captured = self.load_capture(&binding)?;
            return self.call_closure_value(captured.value, binding.vole_type, call);
        }

        // Check if it's a functional interface variable
        if let Some((var, type_id)) = self.vars.get(&callee_sym)
            && let Some(iface_type_def_id) = self.interface_type_def_id(*type_id)
            && let Some(method_id) = self.query().is_functional_interface(iface_type_def_id)
        {
            let method = self.query().get_method(method_id);
            let func_type_id = method.signature_id;
            let method_name_id = method.name_id;
            let value = self.builder.use_var(*var);
            let obj = CompiledValue {
                value,
                ty: self.cranelift_type(*type_id),
                type_id: *type_id,
            };
            return self.interface_dispatch_call_args_by_type_def_id(
                &obj,
                &call.args,
                iface_type_def_id,
                method_name_id,
                func_type_id,
            );
        }

        // Check if it's a global lambda or global functional interface
        if let Some(init_expr) = self.global_init(callee_sym).cloned() {
            // Compile the global's initializer to get its value
            let lambda_val = self.expr(&init_expr)?;

            // Get declared type from GlobalDef (uses sema-resolved type, not TypeExpr)
            // Scope the name_table borrow to avoid conflicts with later mutable borrows
            let global_type_id = {
                let name_table = self.name_table();
                let module_id = self
                    .current_module()
                    .unwrap_or_else(|| name_table.main_module());
                name_table
                    .name_id(module_id, &[callee_sym], self.interner())
                    .and_then(|name_id| self.query().global(name_id))
                    .map(|global_def| global_def.type_id)
            };

            if let Some(declared_type_id) = global_type_id {
                // If declared as functional interface, call via vtable dispatch
                let iface_info = {
                    let arena = self.arena();
                    arena
                        .unwrap_interface(declared_type_id)
                        .map(|(type_def_id, _type_args)| type_def_id)
                };
                if let Some(type_def_id) = iface_info
                    && let Some(method_id) = self.query().is_functional_interface(type_def_id)
                {
                    let method = self.query().get_method(method_id);
                    let func_type_id = method.signature_id;
                    let method_name_id = method.name_id;
                    // Box the lambda value to create the interface representation
                    let boxed = self.box_interface_value(lambda_val, declared_type_id)?;
                    return self.interface_dispatch_call_args_by_type_def_id(
                        &boxed,
                        &call.args,
                        type_def_id,
                        method_name_id,
                        func_type_id,
                    );
                }
            }

            // If it's a function type, call as closure
            if self.arena().is_function(lambda_val.type_id) {
                return self.call_closure_value(lambda_val.value, lambda_val.type_id, call);
            }

            // If it's an interface type (functional interface), call via vtable
            if let Some(type_def_id) = self.interface_type_def_id(lambda_val.type_id)
                && let Some(method_id) = self.query().is_functional_interface(type_def_id)
            {
                let method = self.query().get_method(method_id);
                let func_type_id = method.signature_id;
                let method_name_id = method.name_id;
                return self.interface_dispatch_call_args_by_type_def_id(
                    &lambda_val,
                    &call.args,
                    type_def_id,
                    method_name_id,
                    func_type_id,
                );
            }
        }

        // Check if this is a call to a generic function (via monomorphization)
        let monomorph_key = self.query().monomorph_for(call_expr_id);
        tracing::trace!(
            call_expr_id = ?call_expr_id,
            callee = callee_name,
            has_monomorph = monomorph_key.is_some(),
            "checking for generic function call"
        );
        if let Some(monomorph_key) = monomorph_key {
            // Extract what we need from the monomorph cache before any mutable borrows
            let instance_data = self.monomorph_cache().get(monomorph_key).map(|inst| {
                (
                    inst.original_name,
                    inst.mangled_name,
                    inst.func_type.return_type_id,
                )
            });

            if let Some((original_name, mangled_name, return_type_id)) = instance_data {
                tracing::trace!(
                    instance_name = ?original_name,
                    mangled_name = ?mangled_name,
                    "found monomorph instance"
                );
                let func_key = self.funcs().intern_name_id(mangled_name);
                if let Some(func_id) = self.funcs().func_id(func_key) {
                    tracing::trace!("found func_id, using regular path");
                    return self.call_func_id(func_key, func_id, call);
                }
                tracing::trace!("no func_id, checking for external function");

                // For generic external functions, call them directly with type erasure
                // They don't have compiled func_id, but we can look them up in native_registry
                if let Some(ext_info) = self
                    .analyzed()
                    .implement_registry()
                    .get_external_func(callee_name)
                {
                    let name_table = self.name_table();
                    let module_path = name_table.last_segment_str(ext_info.module_path);
                    let native_name = name_table.last_segment_str(ext_info.native_name);
                    drop(name_table);
                    if let (Some(module_path), Some(native_name)) = (module_path, native_name)
                        && let Some(native_func) =
                            self.native_funcs().lookup(&module_path, &native_name)
                    {
                        // The func_type from the monomorph instance may have TypeParams that weren't
                        // inferred from arguments (like return type params). Apply class type
                        // substitutions to fully resolve the type.
                        let return_type_id = self.substitute_type(return_type_id);
                        return self.compile_native_call_with_types(
                            native_func,
                            call,
                            return_type_id,
                        );
                    }
                }
            }
        }

        // Regular function call - handle module context
        // 1. Try direct function lookup
        // 2. If in module context, try mangled name
        // 3. If in module context, try FFI call
        let main_module = self.funcs_ref().main_module();
        let interner = self.interner();
        let func_key = self
            .funcs()
            .intern_qualified(main_module, &[callee_sym], interner);
        if let Some(func_id) = self.funcs_ref().func_id(func_key) {
            return self.call_func_id(func_key, func_id, call);
        }

        // Check module context for mangled name or FFI
        if let Some(module_id) = self.current_module() {
            let module_path = self.name_table().module_path(module_id).to_string();
            let name_id = crate::types::module_name_id(self.analyzed(), module_id, callee_name);
            if let Some(name_id) = name_id {
                let func_key = self.funcs().intern_name_id(name_id);
                if let Some(func_id) = self.funcs().func_id(func_key) {
                    // Found module function with qualified name
                    return self.call_func_id(func_key, func_id, call);
                }
            }

            // Try FFI call for external module functions
            if let Some(native_func) = self.native_funcs().lookup(&module_path, callee_name) {
                // Compile arguments first
                let mut args = Vec::new();
                for arg in &call.args {
                    let compiled = self.expr(arg)?;
                    args.push(compiled.value);
                }

                // Build the Cranelift signature from NativeSignature
                let mut sig = self.jit_module().make_signature();
                for param_type in &native_func.signature.params {
                    sig.params.push(AbiParam::new(native_type_to_cranelift(
                        param_type,
                        self.ptr_type(),
                    )));
                }
                if native_func.signature.return_type != NativeType::Nil {
                    sig.returns.push(AbiParam::new(native_type_to_cranelift(
                        &native_func.signature.return_type,
                        self.ptr_type(),
                    )));
                }

                // Import the signature and emit an indirect call
                let sig_ref = self.builder.import_signature(sig);
                let func_ptr = native_func.ptr;
                let ptr_type = self.ptr_type();
                let func_ptr_val = self.builder.ins().iconst(ptr_type, func_ptr as i64);

                let call_inst = self
                    .builder
                    .ins()
                    .call_indirect(sig_ref, func_ptr_val, &args);
                let results = self.builder.inst_results(call_inst);

                if results.is_empty() {
                    return Ok(self.void_value());
                } else {
                    // For generic external functions, use sema-inferred type first.
                    // Fall back to declared type for non-generic externals.
                    let type_id = self.get_expr_type(&call_expr_id).unwrap_or_else(|| {
                        native_type_to_type_id(
                            &native_func.signature.return_type,
                            &self.arena(),
                            &self.update(),
                        )
                    });
                    // Convert Iterator<T> to RuntimeIterator(T) since external functions
                    // return raw iterator pointers, not boxed interface values
                    let type_id = self.maybe_convert_iterator_return_type(type_id);
                    return Ok(CompiledValue {
                        value: results[0],
                        ty: native_type_to_cranelift(
                            &native_func.signature.return_type,
                            self.ptr_type(),
                        ),
                        type_id,
                    });
                }
            }

            // Fall through to try prelude external functions
        }

        // Try prelude external functions (works in module context too)
        // Look up the external info (module path and native name) from implement_registry
        let ext_info = self
            .analyzed()
            .implement_registry()
            .get_external_func(callee_name);
        let native_func = ext_info.and_then(|info| {
            let name_table = self.name_table();
            let module_path = name_table.last_segment_str(info.module_path)?;
            let native_name = name_table.last_segment_str(info.native_name)?;
            self.native_funcs().lookup(&module_path, &native_name)
        });
        if let Some(native_func) = native_func {
            // Compile arguments first
            let mut args = Vec::new();
            for arg in &call.args {
                let compiled = self.expr(arg)?;
                args.push(compiled.value);
            }

            // Build the Cranelift signature from NativeSignature
            let mut sig = self.jit_module().make_signature();
            for param_type in &native_func.signature.params {
                sig.params.push(AbiParam::new(native_type_to_cranelift(
                    param_type,
                    self.ptr_type(),
                )));
            }
            if native_func.signature.return_type != NativeType::Nil {
                sig.returns.push(AbiParam::new(native_type_to_cranelift(
                    &native_func.signature.return_type,
                    self.ptr_type(),
                )));
            }

            // Import the signature and emit an indirect call
            let sig_ref = self.builder.import_signature(sig);
            let func_ptr = native_func.ptr;
            let ptr_type = self.ptr_type();
            let func_ptr_val = self.builder.ins().iconst(ptr_type, func_ptr as i64);

            let call_inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_val, &args);
            let results = self.builder.inst_results(call_inst);

            if results.is_empty() {
                return Ok(self.void_value());
            } else {
                // For generic external functions, the sema analyzer stores the inferred
                // concrete return type in expr_types. Use that first.
                // Fall back to declared type for non-generic externals.
                let type_id = self.get_expr_type(&call_expr_id).unwrap_or_else(|| {
                    native_type_to_type_id(
                        &native_func.signature.return_type,
                        &self.arena(),
                        &self.update(),
                    )
                });
                // Convert Iterator<T> to RuntimeIterator(T) since external functions
                // return raw iterator pointers, not boxed interface values
                let type_id = self.maybe_convert_iterator_return_type(type_id);
                return Ok(CompiledValue {
                    value: results[0],
                    ty: native_type_to_cranelift(
                        &native_func.signature.return_type,
                        self.ptr_type(),
                    ),
                    type_id,
                });
            }
        }

        Err(CodegenError::not_found("function", callee_name).into())
    }

    /// Helper to call a function by its FuncId
    fn call_func_id(
        &mut self,
        func_key: FunctionKey,
        func_id: FuncId,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        // Get expected parameter types from the function's signature
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let sig = &self.builder.func.dfg.signatures[sig_ref];
        let expected_types: Vec<Type> = sig.params.iter().map(|p| p.value_type).collect();

        // Compile arguments with type narrowing
        let mut args = Vec::new();
        for (i, arg) in call.args.iter().enumerate() {
            let compiled = self.expr(arg)?;
            let expected_ty = expected_types.get(i).copied();

            // Narrow/extend integer types if needed
            let arg_value = if let Some(expected) = expected_ty {
                if compiled.ty.is_int() && expected.is_int() && expected.bits() < compiled.ty.bits()
                {
                    // Truncate to narrower type
                    self.builder.ins().ireduce(expected, compiled.value)
                } else if compiled.ty.is_int()
                    && expected.is_int()
                    && expected.bits() > compiled.ty.bits()
                {
                    // Extend to wider type
                    self.builder.ins().sextend(expected, compiled.value)
                } else {
                    compiled.value
                }
            } else {
                compiled.value
            };
            args.push(arg_value);
        }

        let call_inst = self.builder.ins().call(func_ref, &args);

        // Get return type
        let return_type_id = self
            .codegen_ctx
            .funcs()
            .return_type(func_key)
            .unwrap_or_else(|| self.env.analyzed.type_arena().void());

        Ok(self.call_result(call_inst, return_type_id))
    }

    /// Compile an indirect call (closure or function value)
    fn indirect_call(&mut self, call: &CallExpr) -> Result<CompiledValue, String> {
        let callee = self.expr(&call.callee)?;

        if self.arena().is_function(callee.type_id) {
            return self.call_closure_value(callee.value, callee.type_id, call);
        }

        Err(CodegenError::type_mismatch("call expression", "function", "non-function").into())
    }

    /// Compile print/println - dispatches to correct vole_println_* based on argument type
    fn call_println(&mut self, call: &CallExpr, newline: bool) -> Result<CompiledValue, String> {
        if call.args.len() != 1 {
            let fn_name = if newline { "println" } else { "print" };
            return Err(CodegenError::arg_count(fn_name, 1, call.args.len()).into());
        }

        let arg = self.expr(&call.args[0])?;

        // Dispatch based on argument type
        let (runtime, call_arg) = if arg.type_id == TypeId::STRING {
            (
                if newline {
                    RuntimeFn::PrintlnString
                } else {
                    RuntimeFn::PrintString
                },
                arg.value,
            )
        } else if arg.ty == types::F64 {
            (
                if newline {
                    RuntimeFn::PrintlnF64
                } else {
                    RuntimeFn::PrintF64
                },
                arg.value,
            )
        } else if arg.ty == types::I8 {
            (
                if newline {
                    RuntimeFn::PrintlnBool
                } else {
                    RuntimeFn::PrintBool
                },
                arg.value,
            )
        } else {
            // Extend smaller integer types to I64
            let extended = if arg.ty.is_int() && arg.ty != types::I64 {
                self.builder.ins().sextend(types::I64, arg.value)
            } else {
                arg.value
            };
            (
                if newline {
                    RuntimeFn::PrintlnI64
                } else {
                    RuntimeFn::PrintI64
                },
                extended,
            )
        };

        self.call_runtime_void(runtime, &[call_arg])?;
        Ok(self.void_value())
    }

    /// Compile print_char builtin for ASCII output
    fn call_print_char(&mut self, call: &CallExpr) -> Result<CompiledValue, String> {
        if call.args.len() != 1 {
            return Err(CodegenError::arg_count("print_char", 1, call.args.len()).into());
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
            )
            .into());
        };

        self.call_runtime_void(RuntimeFn::PrintChar, &[char_val])?;
        Ok(self.void_value())
    }

    /// Compile assert
    fn call_assert(&mut self, call: &CallExpr, call_line: u32) -> Result<CompiledValue, String> {
        if call.args.is_empty() {
            return Err(CodegenError::arg_count("assert", 1, 0).into());
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
            RuntimeFn::AssertFail,
            &[file_ptr_val, file_len_val, line_val],
        )?;
        self.builder.ins().jump(pass_block, &[]);

        self.switch_and_seal(pass_block);

        Ok(self.void_value())
    }

    /// Call a function via variable (dispatches to closure or pure function call)
    fn call_closure(
        &mut self,
        func_var: Variable,
        func_type_id: TypeId,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let func_ptr_or_closure = self.builder.use_var(func_var);
        self.call_closure_value(func_ptr_or_closure, func_type_id, call)
    }

    /// Call a function via value (always uses closure calling convention now that
    /// all lambdas are wrapped in Closure structs for consistent behavior)
    fn call_closure_value(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        // Always use closure calling convention since all lambdas are now
        // wrapped in Closure structs for consistency with interface dispatch
        self.call_actual_closure(func_ptr_or_closure, func_type_id, call)
    }

    /// Call an actual closure (with closure pointer)
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_type_id: TypeId,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let func_ptr = self.call_runtime(RuntimeFn::ClosureGetFunc, &[closure_ptr])?;

        // Get function components from arena
        let (params, ret, _is_closure) = {
            let arena = self.arena();
            let (params, ret, is_closure) = arena
                .unwrap_function(func_type_id)
                .ok_or_else(|| "call_actual_closure called with non-function type".to_string())?;
            (params.clone(), ret, is_closure)
        };

        // Build signature (closure ptr + params)
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr
        for &param_type_id in params.iter() {
            sig.params
                .push(AbiParam::new(self.cranelift_type(param_type_id)));
        }
        let arena = self.arena();
        if ret != arena.void() {
            sig.returns.push(AbiParam::new(type_id_to_cranelift(
                ret,
                &arena,
                self.ptr_type(),
            )));
        }
        drop(arena);

        let sig_ref = self.builder.import_signature(sig);

        let mut args: ArgVec = smallvec![closure_ptr];
        for (arg, &param_type_id) in call.args.iter().zip(params.iter()) {
            let compiled = self.expr(arg)?;
            let compiled = self.coerce_to_type(compiled, param_type_id)?;
            args.push(compiled.value);
        }

        let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            Ok(self.compiled(results[0], ret))
        }
    }

    /// Compile a native function call with known Vole types (for generic external functions)
    /// This uses the concrete types from the monomorphized FunctionType rather than
    /// inferring types from the native signature.
    fn compile_native_call_with_types(
        &mut self,
        native_func: &NativeFunction,
        call: &CallExpr,
        return_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        // Compile arguments
        let mut args = Vec::new();
        for arg in &call.args {
            let compiled = self.expr(arg)?;
            args.push(compiled.value);
        }

        // Build the Cranelift signature from NativeSignature
        let mut sig = self.jit_module().make_signature();
        for param_type in &native_func.signature.params {
            sig.params.push(AbiParam::new(native_type_to_cranelift(
                param_type,
                self.ptr_type(),
            )));
        }
        if native_func.signature.return_type != NativeType::Nil {
            sig.returns.push(AbiParam::new(native_type_to_cranelift(
                &native_func.signature.return_type,
                self.ptr_type(),
            )));
        }

        // Import the signature and emit an indirect call
        let sig_ref = self.builder.import_signature(sig);
        let ptr_type = self.ptr_type();
        let func_ptr_val = self.builder.ins().iconst(ptr_type, native_func.ptr as i64);

        let call_inst = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, &args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            // Apply class type substitutions if available (for calls inside monomorphized methods)
            let type_id = self.substitute_type(return_type_id);
            let type_id = self.maybe_convert_iterator_return_type(type_id);
            Ok(CompiledValue {
                value: results[0],
                ty: native_type_to_cranelift(&native_func.signature.return_type, self.ptr_type()),
                type_id,
            })
        }
    }
}

/// Convert NativeType to TypeId.
fn native_type_to_type_id(
    nt: &NativeType,
    arena: &TypeArena,
    update: &vole_sema::ProgramUpdate,
) -> TypeId {
    match nt {
        NativeType::I8 => arena.primitives.i8,
        NativeType::I16 => arena.primitives.i16,
        NativeType::I32 => arena.primitives.i32,
        NativeType::I64 => arena.primitives.i64,
        NativeType::I128 => arena.primitives.i128,
        NativeType::U8 => arena.primitives.u8,
        NativeType::U16 => arena.primitives.u16,
        NativeType::U32 => arena.primitives.u32,
        NativeType::U64 => arena.primitives.u64,
        NativeType::F32 => arena.primitives.f32,
        NativeType::F64 => arena.primitives.f64,
        NativeType::Bool => arena.primitives.bool,
        NativeType::String => arena.primitives.string,
        NativeType::Nil => arena.primitives.nil,
        NativeType::Optional(inner) => {
            let inner_id = native_type_to_type_id(inner, arena, update);
            update.optional(inner_id)
        }
        NativeType::Array(inner) => {
            let inner_id = native_type_to_type_id(inner, arena, update);
            update.array(inner_id)
        }
    }
}
