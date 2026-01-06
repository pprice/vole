// src/codegen/calls.rs
//
// Call-related codegen - impl Cg methods and standalone helpers.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};

use crate::frontend::{CallExpr, ExprKind, NodeId, StringPart};
use crate::runtime::native_registry::NativeType;
use crate::sema::{FunctionType, Type};

use super::context::Cg;
use super::types::{CompiledValue, native_type_to_cranelift, resolve_type_expr, type_to_cranelift};

/// Compile a string literal by calling vole_string_new
pub(crate) fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: types::Type,
    module: &mut JITModule,
    func_ids: &HashMap<String, FuncId>,
) -> Result<CompiledValue, String> {
    // Get the vole_string_new function
    let func_id = func_ids
        .get("vole_string_new")
        .ok_or_else(|| "vole_string_new not found".to_string())?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

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
    func_ids: &HashMap<String, FuncId>,
) -> Result<Value, String> {
    // If already a string, return as-is
    if matches!(val.vole_type, Type::String) {
        return Ok(val.value);
    }

    let (func_name, call_val) = if val.ty == types::F64 {
        ("vole_f64_to_string", val.value)
    } else if val.ty == types::I8 {
        ("vole_bool_to_string", val.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if val.ty.is_int() && val.ty != types::I64 {
            builder.ins().sextend(types::I64, val.value)
        } else {
            val.value
        };
        ("vole_i64_to_string", extended)
    };

    let func_id = func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

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
            self.ctx.func_ids,
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

        let concat_func_ref = self.func_ref("vole_string_concat")?;
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

        let (func_name, call_val) = if val.ty == types::F64 {
            ("vole_f64_to_string", val.value)
        } else if val.ty == types::I8 {
            ("vole_bool_to_string", val.value)
        } else {
            let extended = if val.ty.is_int() && val.ty != types::I64 {
                self.builder.ins().sextend(types::I64, val.value)
            } else {
                val.value
            };
            ("vole_i64_to_string", extended)
        };

        self.call_runtime(func_name, &[call_val])
    }

    /// Compile a function call
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
            && let Some(method_def) = self
                .ctx
                .interface_registry
                .is_functional(iface.name, self.ctx.interner)
        {
            let func_type = FunctionType {
                params: method_def.params.clone(),
                return_type: Box::new(method_def.return_type.clone()),
                is_closure: true,
            };
            return self.call_closure(*var, func_type, call);
        }

        // Check if it's a global lambda or global functional interface
        if let Some(global) = self.ctx.globals.iter().find(|g| g.name == callee_sym) {
            // First, compile the global to get its value
            let lambda_val = self.expr(&global.init)?;

            // Check if the global has a declared type (e.g., `let x: Predicate = ...`)
            if let Some(ref ty_expr) = global.ty {
                let declared_type = resolve_type_expr(ty_expr, self.ctx);

                // If declared as functional interface, call using the lambda's actual type
                // (the lambda might be a pure function or a closure depending on captures)
                if let Type::Interface(iface) = &declared_type
                    && let Some(method_def) = self
                        .ctx
                        .interface_registry
                        .is_functional(iface.name, self.ctx.interner)
                {
                    // Use the lambda's actual is_closure status from compilation
                    let is_closure = if let Type::Function(ft) = &lambda_val.vole_type {
                        ft.is_closure
                    } else {
                        true // Fallback to closure if unknown
                    };
                    let func_type = FunctionType {
                        params: method_def.params.clone(),
                        return_type: Box::new(method_def.return_type.clone()),
                        is_closure,
                    };
                    return self.call_closure_value(lambda_val.value, func_type, call);
                }
            }

            // If it's a function type, call as closure
            if let Type::Function(func_type) = &lambda_val.vole_type {
                return self.call_closure_value(lambda_val.value, func_type.clone(), call);
            }

            // If it's an interface type (functional interface), call as closure
            if let Type::Interface(iface) = &lambda_val.vole_type
                && let Some(method_def) = self
                    .ctx
                    .interface_registry
                    .is_functional(iface.name, self.ctx.interner)
            {
                let func_type = FunctionType {
                    params: method_def.params.clone(),
                    return_type: Box::new(method_def.return_type.clone()),
                    is_closure: true,
                };
                return self.call_closure_value(lambda_val.value, func_type, call);
            }
        }

        // Check if this is a call to a generic function (via monomorphization)
        if let Some(monomorph_key) = self.ctx.generic_calls.get(&call_expr_id)
            && let Some(instance) = self.ctx.monomorph_cache.get(monomorph_key)
        {
            // Use the mangled function name
            let mangled_name = format!(
                "{}__mono_{}",
                self.ctx.interner.resolve(instance.original_name),
                instance.instance_id
            );
            if let Some(func_id) = self.ctx.func_ids.get(&mangled_name) {
                return self.call_func_id(*func_id, &mangled_name, call);
            }
        }

        // Regular function call - handle module context
        // 1. Try direct function lookup
        // 2. If in module context, try mangled name
        // 3. If in module context, try FFI call
        if let Some(func_id) = self.ctx.func_ids.get(callee_name) {
            // Direct function found
            return self.call_func_id(*func_id, callee_name, call);
        }

        // Check module context for mangled name or FFI
        if let Some(module_path) = self.ctx.current_module {
            let mangled_name = format!("{}::{}", module_path, callee_name);
            if let Some(func_id) = self.ctx.func_ids.get(&mangled_name) {
                // Found module function with mangled name
                return self.call_func_id(*func_id, &mangled_name, call);
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
                    let vole_type = native_type_to_vole_type(&native_func.signature.return_type);
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

            return Err(format!("{} not found", callee_name));
        }

        // No module context - just fail
        Err(format!("undefined function: {}", callee_name))
    }

    /// Helper to call a function by its FuncId
    fn call_func_id(
        &mut self,
        func_id: FuncId,
        func_name: &str,
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
            .func_return_types
            .get(func_name)
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

        Err("Cannot call non-function value".to_string())
    }

    /// Compile print/println - dispatches to correct vole_println_* based on argument type
    fn call_println(&mut self, call: &CallExpr, newline: bool) -> Result<CompiledValue, String> {
        let prefix = if newline {
            "vole_println"
        } else {
            "vole_print"
        };

        if call.args.len() != 1 {
            return Err(format!(
                "{} expects exactly one argument",
                if newline { "println" } else { "print" }
            ));
        }

        let arg = self.expr(&call.args[0])?;

        // Dispatch based on argument type
        let (func_name, call_arg) = if matches!(arg.vole_type, Type::String) {
            (format!("{}_string", prefix), arg.value)
        } else if arg.ty == types::F64 {
            (format!("{}_f64", prefix), arg.value)
        } else if arg.ty == types::I8 {
            (format!("{}_bool", prefix), arg.value)
        } else {
            // Extend smaller integer types to I64
            let extended = if arg.ty.is_int() && arg.ty != types::I64 {
                self.builder.ins().sextend(types::I64, arg.value)
            } else {
                arg.value
            };
            (format!("{}_i64", prefix), extended)
        };

        self.call_runtime_void(&func_name, &[call_arg])?;
        Ok(self.void_value())
    }

    /// Compile print_char builtin for ASCII output
    fn call_print_char(&mut self, call: &CallExpr) -> Result<CompiledValue, String> {
        if call.args.len() != 1 {
            return Err("print_char expects exactly one argument".to_string());
        }

        let arg = self.expr(&call.args[0])?;

        // Convert to u8 if needed (truncate from i64)
        let char_val = if arg.ty == types::I64 {
            self.builder.ins().ireduce(types::I8, arg.value)
        } else if arg.ty == types::I8 {
            arg.value
        } else {
            return Err("print_char expects an integer argument".to_string());
        };

        self.call_runtime_void("vole_print_char", &[char_val])?;
        Ok(self.void_value())
    }

    /// Compile assert
    fn call_assert(&mut self, call: &CallExpr, call_line: u32) -> Result<CompiledValue, String> {
        if call.args.is_empty() {
            return Err("assert requires at least one argument".to_string());
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

        self.call_runtime_void("vole_assert_fail", &[file_ptr_val, file_len_val, line_val])?;
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

    /// Call a function via value (dispatches to closure or pure function call)
    fn call_closure_value(
        &mut self,
        func_ptr_or_closure: Value,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        if func_type.is_closure {
            self.call_actual_closure(func_ptr_or_closure, func_type, call)
        } else {
            self.call_pure_function(func_ptr_or_closure, func_type, call)
        }
    }

    /// Call a pure function (no closure)
    fn call_pure_function(
        &mut self,
        func_ptr: Value,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        // Build signature for pure function call
        let mut sig = self.ctx.module.make_signature();
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

        let mut args = Vec::new();
        for arg in &call.args {
            let compiled = self.expr(arg)?;
            args.push(compiled.value);
        }

        let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            Ok(self.typed_value(results[0], (*func_type.return_type).clone()))
        }
    }

    /// Call an actual closure (with closure pointer)
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let func_ptr = self.call_runtime("vole_closure_get_func", &[closure_ptr])?;

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

        let mut args = vec![closure_ptr];
        for arg in &call.args {
            let compiled = self.expr(arg)?;
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
