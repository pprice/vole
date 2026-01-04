// src/codegen/calls.rs
//
// Call-related codegen - impl Cg methods and standalone helpers.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};

use crate::frontend::{CallExpr, ExprKind, StringPart};
use crate::sema::{FunctionType, Type};

use super::context::Cg;
use super::types::{type_to_cranelift, CompiledValue};

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
            return Ok(CompiledValue {
                value: string_values[0],
                ty: self.ctx.pointer_type,
                vole_type: Type::String,
            });
        }

        let concat_func_id = self
            .ctx
            .func_ids
            .get("vole_string_concat")
            .ok_or_else(|| "vole_string_concat not found".to_string())?;
        let concat_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*concat_func_id, self.builder.func);

        let mut result = string_values[0];
        for &next in &string_values[1..] {
            let call = self.builder.ins().call(concat_func_ref, &[result, next]);
            result = self.builder.inst_results(call)[0];
        }

        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::String,
        })
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

        let func_id = self
            .ctx
            .func_ids
            .get(func_name)
            .ok_or_else(|| format!("{} not found", func_name))?;
        let func_ref = self
            .ctx
            .module
            .declare_func_in_func(*func_id, self.builder.func);

        let call = self.builder.ins().call(func_ref, &[call_val]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Compile a function call
    pub fn call(&mut self, call: &CallExpr, call_line: u32) -> Result<CompiledValue, String> {
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
        if let Some((var, vole_type)) = self.vars.get(&callee_sym) {
            if let Type::Function(func_type) = vole_type {
                return self.call_closure(*var, func_type.clone(), call);
            }
        }

        // Check if it's a global lambda
        if let Some(global) = self.ctx.globals.iter().find(|g| g.name == callee_sym) {
            if matches!(&global.init.kind, ExprKind::Lambda(_)) {
                // Compile the lambda to get a function value and call it indirectly
                let lambda_val = self.expr(&global.init)?;
                if let Type::Function(func_type) = &lambda_val.vole_type {
                    return self.call_closure_value(lambda_val.value, func_type.clone(), call);
                }
            }
        }

        // Regular function call
        let func_id = self.ctx.func_ids.get(callee_name).ok_or_else(|| {
            format!("undefined function: {}", callee_name)
        })?;
        let func_ref = self
            .ctx
            .module
            .declare_func_in_func(*func_id, self.builder.func);

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
            .get(callee_name)
            .cloned()
            .unwrap_or(Type::Void);

        if results.is_empty() {
            Ok(CompiledValue {
                value: self.builder.ins().iconst(types::I64, 0),
                ty: types::I64,
                vole_type: Type::Void,
            })
        } else {
            Ok(CompiledValue {
                value: results[0],
                ty: type_to_cranelift(&return_type, self.ctx.pointer_type),
                vole_type: return_type,
            })
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
        let prefix = if newline { "vole_println" } else { "vole_print" };

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

        let func_id = self
            .ctx
            .func_ids
            .get(&func_name)
            .ok_or_else(|| format!("{} not found", func_name))?;
        let func_ref = self
            .ctx
            .module
            .declare_func_in_func(*func_id, self.builder.func);
        self.builder.ins().call(func_ref, &[call_arg]);

        // println returns void, but we need to return something
        Ok(CompiledValue {
            value: self.builder.ins().iconst(types::I64, 0),
            ty: types::I64,
            vole_type: Type::Void,
        })
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

        let func_id = self
            .ctx
            .func_ids
            .get("vole_print_char")
            .ok_or_else(|| "vole_print_char not found".to_string())?;
        let func_ref = self
            .ctx
            .module
            .declare_func_in_func(*func_id, self.builder.func);
        self.builder.ins().call(func_ref, &[char_val]);

        // Return void (as i64 zero)
        Ok(CompiledValue {
            value: self.builder.ins().iconst(types::I64, 0),
            ty: types::I64,
            vole_type: Type::Void,
        })
    }

    /// Compile assert
    fn call_assert(&mut self, call: &CallExpr, call_line: u32) -> Result<CompiledValue, String> {
        if call.args.is_empty() {
            return Err("assert requires at least one argument".to_string());
        }

        let cond = self.expr(&call.args[0])?;
        let cond_i32 = self.builder.ins().uextend(types::I32, cond.value);

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

        let func_id = self
            .ctx
            .func_ids
            .get("vole_assert_fail")
            .ok_or_else(|| "vole_assert_fail not found".to_string())?;
        let func_ref = self
            .ctx
            .module
            .declare_func_in_func(*func_id, self.builder.func);
        self.builder
            .ins()
            .call(func_ref, &[file_ptr_val, file_len_val, line_val]);
        self.builder.ins().jump(pass_block, &[]);

        self.builder.switch_to_block(pass_block);
        self.builder.seal_block(pass_block);

        Ok(CompiledValue {
            value: self.builder.ins().iconst(types::I64, 0),
            ty: types::I64,
            vole_type: Type::Void,
        })
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
            sig.params
                .push(AbiParam::new(type_to_cranelift(param_type, self.ctx.pointer_type)));
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
            Ok(CompiledValue {
                value: self.builder.ins().iconst(types::I64, 0),
                ty: types::I64,
                vole_type: Type::Void,
            })
        } else {
            Ok(CompiledValue {
                value: results[0],
                ty: type_to_cranelift(&func_type.return_type, self.ctx.pointer_type),
                vole_type: (*func_type.return_type).clone(),
            })
        }
    }

    /// Call an actual closure (with closure pointer)
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_type: FunctionType,
        call: &CallExpr,
    ) -> Result<CompiledValue, String> {
        let get_func_id = self
            .ctx
            .func_ids
            .get("vole_closure_get_func")
            .ok_or_else(|| "vole_closure_get_func not found".to_string())?;
        let get_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*get_func_id, self.builder.func);
        let func_call = self.builder.ins().call(get_func_ref, &[closure_ptr]);
        let func_ptr = self.builder.inst_results(func_call)[0];

        // Build signature (closure ptr + params)
        let mut sig = self.ctx.module.make_signature();
        sig.params.push(AbiParam::new(self.ctx.pointer_type)); // closure ptr
        for param_type in &func_type.params {
            sig.params
                .push(AbiParam::new(type_to_cranelift(param_type, self.ctx.pointer_type)));
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
            Ok(CompiledValue {
                value: self.builder.ins().iconst(types::I64, 0),
                ty: types::I64,
                vole_type: Type::Void,
            })
        } else {
            Ok(CompiledValue {
                value: results[0],
                ty: type_to_cranelift(&func_type.return_type, self.ctx.pointer_type),
                vole_type: func_type.return_type.as_ref().clone(),
            })
        }
    }
}
