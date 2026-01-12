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
use crate::frontend::{CallExpr, ExprKind, LetInit, NodeId, StringPart};
use crate::runtime::native_registry::NativeType;
use crate::sema::{FunctionType, Type};

use super::context::Cg;
use super::interface_vtable::box_interface_value;
use super::types::{CompiledValue, native_type_to_cranelift, resolve_type_expr, type_to_cranelift};
use super::{FunctionKey, FunctionRegistry, RuntimeFn};

/// Compile a string literal by calling vole_string_new
pub(crate) fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: types::Type,
    module: &mut JITModule,
    func_registry: &FunctionRegistry,
) -> Result<CompiledValue, String> {
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
    let result = builder.inst_results(call)[0];

    Ok(CompiledValue {
        value: result,
        ty: pointer_type,
        vole_type: Type::String,
    })
}

/// Convert a compiled value to a string by calling the appropriate vole_*_to_string function
#[allow(dead_code)] // Used by compiler.rs during migration
pub(crate) fn value_to_string(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    _pointer_type: types::Type,
    module: &mut JITModule,
    func_registry: &FunctionRegistry,
) -> Result<Value, String> {
    // If already a string, return as-is
    if matches!(val.vole_type, Type::String) {
        return Ok(val.value);
    }

    let (runtime, call_val) = if val.ty == types::F64 {
        (RuntimeFn::F64ToString, val.value)
    } else if val.ty == types::I8 {
        (RuntimeFn::BoolToString, val.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if val.ty.is_int() && val.ty != types::I64 {
            builder.ins().sextend(types::I64, val.value)
        } else {
            val.value
        };
        (RuntimeFn::I64ToString, extended)
    };

    let func_id = func_registry
        .runtime_key(runtime)
        .and_then(|key| func_registry.func_id(key))
        .ok_or_else(|| format!("{} not found", runtime.name()))?;
    let func_ref = module.declare_func_in_func(func_id, builder.func);

    let call = builder.ins().call(func_ref, &[call_val]);
    Ok(builder.inst_results(call)[0])
}

impl Cg<'_, '_, '_> {
    /// Compile a string literal
    pub fn string_literal(&mut self, s: &str) -> Result<CompiledValue, String> {
        compile_string_literal(
            self.builder,
            s,
            self.ctx.pointer_type,
            self.ctx.module,
            self.ctx.func_registry,
        )
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
            .ctx
            .func_registry
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
        if matches!(val.vole_type, Type::String) {
            return Ok(val.value);
        }

        // Handle arrays
        if matches!(val.vole_type, Type::Array(_)) {
            return self.call_runtime(RuntimeFn::ArrayI64ToString, &[val.value]);
        }

        // Handle nil type directly
        if matches!(val.vole_type, Type::Nil) {
            return self.call_runtime(RuntimeFn::NilToString, &[]);
        }

        // Handle optionals (unions with nil variant)
        if let Type::Union(variants) = &val.vole_type
            && let Some(nil_idx) = variants.iter().position(|v| matches!(v, Type::Nil))
        {
            return self.optional_to_string(val.value, variants, nil_idx);
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

    /// Convert an optional (union with nil) to string
    fn optional_to_string(
        &mut self,
        ptr: Value,
        variants: &[Type],
        nil_idx: usize,
    ) -> Result<Value, String> {
        use crate::codegen::types::type_to_cranelift;

        // Load the tag from offset 0
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let nil_tag = self.builder.ins().iconst(types::I8, nil_idx as i64);
        let is_nil = self.builder.ins().icmp(IntCC::Equal, tag, nil_tag);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let some_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add block param for the result string
        self.builder
            .append_block_param(merge_block, self.ctx.pointer_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], some_block, &[]);

        // Nil case: return "nil"
        self.builder.switch_to_block(nil_block);
        let nil_str = self.call_runtime(RuntimeFn::NilToString, &[])?;
        self.builder.ins().jump(merge_block, &[nil_str.into()]);

        // Some case: extract inner value and convert to string
        self.builder.switch_to_block(some_block);
        // Find the non-nil variant
        let inner_type = variants
            .iter()
            .find(|v| !matches!(v, Type::Nil))
            .cloned()
            .unwrap_or(Type::Nil);
        let inner_cr_type = type_to_cranelift(&inner_type, self.ctx.pointer_type);
        let inner_val = self
            .builder
            .ins()
            .load(inner_cr_type, MemFlags::new(), ptr, 8);

        let inner_compiled = CompiledValue {
            value: inner_val,
            ty: inner_cr_type,
            vole_type: inner_type,
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

        let callee_name = self.ctx.interner.resolve(callee_sym);

        // Handle builtins
        match callee_name {
            "print" | "println" => return self.call_println(call, callee_name == "println"),
            "print_char" => return self.call_print_char(call),
            "assert" => return self.call_assert(call, call_line),
            _ => {}
        }

        // Check if it's a closure variable
        if let Some((var, vole_type)) = self.vars.get(&callee_sym)
            && let Type::Function(func_type) = vole_type
        {
            return self.call_closure(*var, func_type.clone(), call);
        }

        // Check if it's a functional interface variable
        if let Some((var, vole_type)) = self.vars.get(&callee_sym)
            && let Type::Interface(iface) = vole_type
            && let Some(type_def_id) = self
                .ctx
                .analyzed
                .entity_registry
                .type_by_name(iface.name_id)
            && let Some(method_id) = self.ctx.analyzed.entity_registry.is_functional(type_def_id)
        {
            let method = self.ctx.analyzed.entity_registry.get_method(method_id);
            let func_type = FunctionType {
                params: method.signature.params.clone(),
                return_type: method.signature.return_type.clone(),
                is_closure: false,
            };
            let method_name_id = method.name_id;
            let value = self.builder.use_var(*var);
            let obj = CompiledValue {
                value,
                ty: type_to_cranelift(vole_type, self.ctx.pointer_type),
                vole_type: vole_type.clone(),
            };
            return self.interface_dispatch_call_args_by_type_def_id(
                &obj,
                &call.args,
                type_def_id,
                method_name_id,
                func_type,
            );
        }

        // Check if it's a global lambda or global functional interface
        if let Some(global) = self.ctx.globals.iter().find(|g| g.name == callee_sym) {
            // First, compile the global to get its value (skip type aliases)
            let init_expr = match &global.init {
                LetInit::Expr(e) => e,
                LetInit::TypeAlias(_) => return Err("cannot call a type alias".to_string()),
            };
            let lambda_val = self.expr(init_expr)?;

            // Check if the global has a declared type (e.g., `let x: Predicate = ...`)
            if let Some(ref ty_expr) = global.ty {
                let declared_type = resolve_type_expr(ty_expr, self.ctx);

                // If declared as functional interface, call via vtable dispatch
                if let Type::Interface(iface) = &declared_type
                    && let Some(type_def_id) = self
                        .ctx
                        .analyzed
                        .entity_registry
                        .type_by_name(iface.name_id)
                    && let Some(method_id) =
                        self.ctx.analyzed.entity_registry.is_functional(type_def_id)
                {
                    let method = self.ctx.analyzed.entity_registry.get_method(method_id);
                    let func_type = FunctionType {
                        params: method.signature.params.clone(),
                        return_type: method.signature.return_type.clone(),
                        is_closure: false,
                    };
                    let method_name_id = method.name_id;
                    // Box the lambda value to create the interface representation
                    let boxed =
                        box_interface_value(self.builder, self.ctx, lambda_val, &declared_type)?;
                    return self.interface_dispatch_call_args_by_type_def_id(
                        &boxed,
                        &call.args,
                        type_def_id,
                        method_name_id,
                        func_type,
                    );
                }
            }

            // If it's a function type, call as closure
            if let Type::Function(func_type) = &lambda_val.vole_type {
                return self.call_closure_value(lambda_val.value, func_type.clone(), call);
            }

            // If it's an interface type (functional interface), call via vtable
            if let Type::Interface(iface) = &lambda_val.vole_type
                && let Some(type_def_id) = self
                    .ctx
                    .analyzed
                    .entity_registry
                    .type_by_name(iface.name_id)
                && let Some(method_id) =
                    self.ctx.analyzed.entity_registry.is_functional(type_def_id)
            {
                let method = self.ctx.analyzed.entity_registry.get_method(method_id);
                let func_type = FunctionType {
                    params: method.signature.params.clone(),
                    return_type: method.signature.return_type.clone(),
                    is_closure: false,
                };
                let method_name_id = method.name_id;
                return self.interface_dispatch_call_args_by_type_def_id(
                    &lambda_val,
                    &call.args,
                    type_def_id,
                    method_name_id,
                    func_type,
                );
            }
        }

        // Check if this is a call to a generic function (via monomorphization)
        if let Some(monomorph_key) = self.ctx.analyzed.query().monomorph_for(call_expr_id)
            && let Some(instance) = self.ctx.monomorph_cache.get(monomorph_key)
        {
            let func_key = self.ctx.func_registry.intern_name_id(instance.mangled_name);
            if let Some(func_id) = self.ctx.func_registry.func_id(func_key) {
                return self.call_func_id(func_key, func_id, call);
            }
        }

        // Regular function call - handle module context
        // 1. Try direct function lookup
        // 2. If in module context, try mangled name
        // 3. If in module context, try FFI call
        let func_key = self.ctx.func_registry.intern_qualified(
            self.ctx.func_registry.main_module(),
            &[callee_sym],
            self.ctx.interner,
        );
        if let Some(func_id) = self.ctx.func_registry.func_id(func_key) {
            return self.call_func_id(func_key, func_id, call);
        }

        // Check module context for mangled name or FFI
        if let Some(module_path) = self.ctx.current_module {
            let module_id = self
                .ctx
                .analyzed
                .name_table
                .module_id_if_known(module_path)
                .unwrap_or_else(|| self.ctx.analyzed.name_table.main_module());
            let name_id =
                crate::codegen::types::module_name_id(self.ctx.analyzed, module_id, callee_name);
            if let Some(name_id) = name_id {
                let func_key = self.ctx.func_registry.intern_name_id(name_id);
                if let Some(func_id) = self.ctx.func_registry.func_id(func_key) {
                    // Found module function with qualified name
                    return self.call_func_id(func_key, func_id, call);
                }
            }

            // Try FFI call for external module functions
            if let Some(native_func) = self.ctx.native_registry.lookup(module_path, callee_name) {
                // Compile arguments first
                let mut args = Vec::new();
                for arg in &call.args {
                    let compiled = self.expr(arg)?;
                    args.push(compiled.value);
                }

                // Build the Cranelift signature from NativeSignature
                let mut sig = self.ctx.module.make_signature();
                for param_type in &native_func.signature.params {
                    sig.params.push(AbiParam::new(native_type_to_cranelift(
                        param_type,
                        self.ctx.pointer_type,
                    )));
                }
                if native_func.signature.return_type != NativeType::Nil {
                    sig.returns.push(AbiParam::new(native_type_to_cranelift(
                        &native_func.signature.return_type,
                        self.ctx.pointer_type,
                    )));
                }

                // Import the signature and emit an indirect call
                let sig_ref = self.builder.import_signature(sig);
                let func_ptr = native_func.ptr;
                let func_ptr_val = self
                    .builder
                    .ins()
                    .iconst(self.ctx.pointer_type, func_ptr as i64);

                let call_inst = self
                    .builder
                    .ins()
                    .call_indirect(sig_ref, func_ptr_val, &args);
                let results = self.builder.inst_results(call_inst);

                if results.is_empty() {
                    return Ok(self.void_value());
                } else {
                    // Try to get declared Vole return type from implement_registry
                    // Fall back to native type conversion
                    let ext_info = self
                        .ctx
                        .analyzed
                        .implement_registry
                        .get_external_func(callee_name);
                    let vole_type = ext_info
                        .and_then(|info| info.return_type.as_ref().map(|t| (**t).clone()))
                        .unwrap_or_else(|| {
                            native_type_to_vole_type(&native_func.signature.return_type)
                        });
                    // Convert Iterator<T> to RuntimeIterator(T) since external functions
                    // return raw iterator pointers, not boxed interface values
                    let vole_type = self.maybe_convert_iterator_return_type(vole_type);
                    return Ok(CompiledValue {
                        value: results[0],
                        ty: native_type_to_cranelift(
                            &native_func.signature.return_type,
                            self.ctx.pointer_type,
                        ),
                        vole_type,
                    });
                }
            }

            // Fall through to try prelude external functions
        }

        // Try prelude external functions (works in module context too)
        // Look up the external info (module path and native name) from implement_registry
        let ext_info = self
            .ctx
            .analyzed
            .implement_registry
            .get_external_func(callee_name);
        let native_func = ext_info.and_then(|info| {
            self.ctx
                .native_registry
                .lookup(&info.module_path, &info.native_name)
        });
        if let Some(native_func) = native_func {
            // Compile arguments first
            let mut args = Vec::new();
            for arg in &call.args {
                let compiled = self.expr(arg)?;
                args.push(compiled.value);
            }

            // Build the Cranelift signature from NativeSignature
            let mut sig = self.ctx.module.make_signature();
            for param_type in &native_func.signature.params {
                sig.params.push(AbiParam::new(native_type_to_cranelift(
                    param_type,
                    self.ctx.pointer_type,
                )));
            }
            if native_func.signature.return_type != NativeType::Nil {
                sig.returns.push(AbiParam::new(native_type_to_cranelift(
                    &native_func.signature.return_type,
                    self.ctx.pointer_type,
                )));
            }

            // Import the signature and emit an indirect call
            let sig_ref = self.builder.import_signature(sig);
            let func_ptr = native_func.ptr;
            let func_ptr_val = self
                .builder
                .ins()
                .iconst(self.ctx.pointer_type, func_ptr as i64);

            let call_inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_val, &args);
            let results = self.builder.inst_results(call_inst);

            if results.is_empty() {
                return Ok(self.void_value());
            } else {
                // Use declared Vole return type if available (e.g., Iterator<i64>)
                // Fall back to native type conversion (e.g., I64 -> i64)
                let vole_type = ext_info
                    .and_then(|info| info.return_type.as_ref().map(|t| (**t).clone()))
                    .unwrap_or_else(|| {
                        native_type_to_vole_type(&native_func.signature.return_type)
                    });
                // Convert Iterator<T> to RuntimeIterator(T) since external functions
                // return raw iterator pointers, not boxed interface values
                let vole_type = self.maybe_convert_iterator_return_type(vole_type);
                return Ok(CompiledValue {
                    value: results[0],
                    ty: native_type_to_cranelift(
                        &native_func.signature.return_type,
                        self.ctx.pointer_type,
                    ),
                    vole_type,
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
            .ctx
            .module
            .declare_func_in_func(func_id, self.builder.func);

        // Get expected parameter types from the function's signature
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let sig = &self.builder.func.dfg.signatures[sig_ref];
        let expected_types: Vec<types::Type> = sig.params.iter().map(|p| p.value_type).collect();

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
        let results = self.builder.inst_results(call_inst);

        let return_type = self
            .ctx
            .func_registry
            .return_type(func_key)
            .cloned()
            .unwrap_or(Type::Void);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            Ok(self.typed_value(results[0], return_type))
        }
    }

    /// Compile an indirect call (closure or function value)
    fn indirect_call(&mut self, call: &CallExpr) -> Result<CompiledValue, String> {
        let callee = self.expr(&call.callee)?;

        if let Type::Function(func_type) = &callee.vole_type {
            return self.call_closure_value(callee.value, func_type.clone(), call);
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
        let (runtime, call_arg) = if matches!(arg.vole_type, Type::String) {
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

        self.builder.switch_to_block(fail_block);
        self.builder.seal_block(fail_block);

        // vole_assert_fail(file_ptr, file_len, line)
        let (file_ptr, file_len) = self.ctx.source_file_ptr;
        let file_ptr_val = self
            .builder
            .ins()
            .iconst(self.ctx.pointer_type, file_ptr as i64);
        let file_len_val = self
            .builder
            .ins()
            .iconst(self.ctx.pointer_type, file_len as i64);
        let line_val = self.builder.ins().iconst(types::I32, call_line as i64);

        self.call_runtime_void(
            RuntimeFn::AssertFail,
            &[file_ptr_val, file_len_val, line_val],
        )?;
        self.builder.ins().jump(pass_block, &[]);

        self.builder.switch_to_block(pass_block);
        self.builder.seal_block(pass_block);

        Ok(self.void_value())
    }

    /// Call a function via variable (dispatches to closure or pure function call)
    fn call_closure(
        &mut self,
        func_var: Variable,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let func_ptr_or_closure = self.builder.use_var(func_var);
        self.call_closure_value(func_ptr_or_closure, func_type, call)
    }

    /// Call a function via value (always uses closure calling convention now that
    /// all lambdas are wrapped in Closure structs for consistent behavior)
    fn call_closure_value(
        &mut self,
        func_ptr_or_closure: Value,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        // Always use closure calling convention since all lambdas are now
        // wrapped in Closure structs for consistency with interface dispatch
        self.call_actual_closure(func_ptr_or_closure, func_type, call)
    }

    /// Call a pure function (no closure)
    /// Call an actual closure (with closure pointer)
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let func_ptr = self.call_runtime(RuntimeFn::ClosureGetFunc, &[closure_ptr])?;

        // Build signature (closure ptr + params)
        let mut sig = self.ctx.module.make_signature();
        sig.params.push(AbiParam::new(self.ctx.pointer_type)); // closure ptr
        for param_type in &func_type.params {
            sig.params.push(AbiParam::new(type_to_cranelift(
                param_type,
                self.ctx.pointer_type,
            )));
        }
        if func_type.return_type.as_ref() != &Type::Void {
            sig.returns.push(AbiParam::new(type_to_cranelift(
                &func_type.return_type,
                self.ctx.pointer_type,
            )));
        }

        let sig_ref = self.builder.import_signature(sig);

        let mut args: ArgVec = smallvec![closure_ptr];
        for (arg, param_type) in call.args.iter().zip(func_type.params.iter()) {
            let compiled = self.expr(arg)?;
            let compiled = if matches!(param_type, Type::Interface(_)) {
                box_interface_value(self.builder, self.ctx, compiled, param_type)?
            } else if matches!(param_type, Type::Union(_))
                && !matches!(&compiled.vole_type, Type::Union(_))
            {
                // Box concrete type into union representation
                self.construct_union(compiled, param_type)?
            } else {
                compiled
            };
            args.push(compiled.value);
        }

        let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            Ok(self.typed_value(results[0], func_type.return_type.as_ref().clone()))
        }
    }
}

/// Convert NativeType to Vole Type
fn native_type_to_vole_type(nt: &NativeType) -> Type {
    match nt {
        NativeType::I8 => Type::I8,
        NativeType::I16 => Type::I16,
        NativeType::I32 => Type::I32,
        NativeType::I64 => Type::I64,
        NativeType::I128 => Type::I128,
        NativeType::U8 => Type::U8,
        NativeType::U16 => Type::U16,
        NativeType::U32 => Type::U32,
        NativeType::U64 => Type::U64,
        NativeType::F32 => Type::F32,
        NativeType::F64 => Type::F64,
        NativeType::Bool => Type::Bool,
        NativeType::String => Type::String,
        NativeType::Nil => Type::Nil,
        NativeType::Optional(inner) => {
            Type::Union(vec![native_type_to_vole_type(inner), Type::Nil])
        }
        NativeType::Array(inner) => Type::Array(Box::new(native_type_to_vole_type(inner))),
    }
}
