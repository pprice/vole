// src/codegen/compiler/calls.rs
//
// Function call codegen helpers.

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::patterns::compile_expr;
use crate::codegen::lambda::CaptureBinding;
use crate::codegen::types::{
    CompileCtx, CompiledValue, cranelift_to_vole_type, native_type_to_cranelift, type_to_cranelift,
};
use crate::frontend::{CallExpr, Expr, ExprKind, Symbol};
use crate::runtime::native_registry::{NativeFunction, NativeType};
use crate::sema::{FunctionType, Type};

pub(crate) fn compile_call_with_captures(
    builder: &mut FunctionBuilder,
    call: &CallExpr,
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    _capture_bindings: &HashMap<Symbol, CaptureBinding>,
    _closure_var: Option<Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // For now, delegate to regular call compilation
    // The callee might be a closure, but we handle that in compile_indirect_call_value
    compile_call(builder, call, call_line, variables, ctx)
}

/// Compile a function call expression
pub(crate) fn compile_call(
    builder: &mut FunctionBuilder,
    call: &CallExpr,
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Get the callee symbol - must be an identifier for now
    let callee_sym = match &call.callee.kind {
        ExprKind::Identifier(sym) => *sym,
        _ => return Err("only simple function calls are supported".to_string()),
    };

    let callee_name = ctx.interner.resolve(callee_sym);

    // Handle builtin functions first
    match callee_name {
        "println" => return compile_println(builder, &call.args, variables, ctx),
        "print_char" => return compile_print_char(builder, &call.args, variables, ctx),
        "assert" => return compile_assert(builder, &call.args, call_line, variables, ctx),
        _ => {}
    }

    // Check if callee is a variable with function type (for indirect calls)
    if let Some((var, Type::Function(ft))) = variables.get(&callee_sym) {
        // Clone what we need to avoid borrow conflicts
        let var = *var;
        let ft = ft.clone();
        return compile_indirect_call(builder, var, &ft, &call.args, variables, ctx);
    }

    // Check if callee is a variable with interface type (functional interface)
    if let Some((var, Type::Interface(iface))) = variables.get(&callee_sym) {
        // Look up the functional interface's function type
        if let Some(method_def) = ctx
            .interface_registry
            .is_functional(iface.name, ctx.interner)
        {
            let ft = FunctionType {
                params: method_def.params.clone(),
                return_type: Box::new(method_def.return_type.clone()),
                is_closure: true, // Interface variables hold closures
            };
            let var = *var;
            return compile_indirect_call(builder, var, &ft, &call.args, variables, ctx);
        }
    }

    // Check if callee is a global variable with function type
    if let Some(global) = ctx.globals.iter().find(|g| g.name == callee_sym) {
        // Compile the global's initializer to get the function pointer
        let callee_value = compile_expr(builder, &global.init, variables, ctx)?;
        if let Type::Function(ft) = &callee_value.vole_type {
            return compile_indirect_call_value(
                builder,
                callee_value.value,
                ft,
                &call.args,
                variables,
                ctx,
            );
        }
        // Check if global is a functional interface
        if let Type::Interface(iface) = &callee_value.vole_type
            && let Some(method_def) = ctx
                .interface_registry
                .is_functional(iface.name, ctx.interner)
        {
            let ft = FunctionType {
                params: method_def.params.clone(),
                return_type: Box::new(method_def.return_type.clone()),
                is_closure: true,
            };
            return compile_indirect_call_value(
                builder,
                callee_value.value,
                &ft,
                &call.args,
                variables,
                ctx,
            );
        }
    }

    // Fall back to named function call
    compile_user_function_call(builder, callee_name, &call.args, variables, ctx)
}

/// Compile an indirect call through a function pointer variable
pub(crate) fn compile_indirect_call(
    builder: &mut FunctionBuilder,
    var: Variable,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let func_ptr_or_closure = builder.use_var(var);
    compile_indirect_call_value(builder, func_ptr_or_closure, ft, args, variables, ctx)
}

/// Compile an indirect call through a function pointer value or closure pointer
pub(crate) fn compile_indirect_call_value(
    builder: &mut FunctionBuilder,
    func_ptr_or_closure: Value,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if ft.is_closure {
        // This is a closure - we need to extract the function pointer and pass the closure
        compile_closure_call(builder, func_ptr_or_closure, ft, args, variables, ctx)
    } else {
        // Pure function pointer - call directly
        compile_pure_function_call(builder, func_ptr_or_closure, ft, args, variables, ctx)
    }
}

/// Compile a call to a pure function (no closure)
pub(crate) fn compile_pure_function_call(
    builder: &mut FunctionBuilder,
    func_ptr: Value,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Build the Cranelift signature for the indirect call
    let mut sig = ctx.module.make_signature();
    for param_type in &ft.params {
        sig.params.push(AbiParam::new(type_to_cranelift(
            param_type,
            ctx.pointer_type,
        )));
    }
    sig.returns.push(AbiParam::new(type_to_cranelift(
        &ft.return_type,
        ctx.pointer_type,
    )));

    let sig_ref = builder.import_signature(sig);

    // Compile arguments
    let mut arg_values = Vec::new();
    for arg in args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        arg_values.push(compiled.value);
    }

    // Perform the indirect call
    let call_inst = builder.ins().call_indirect(sig_ref, func_ptr, &arg_values);
    let results = builder.inst_results(call_inst);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type: (*ft.return_type).clone(),
        })
    }
}

/// Compile a call to a closure (lambda with captures)
pub(crate) fn compile_closure_call(
    builder: &mut FunctionBuilder,
    closure_ptr: Value,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Extract the function pointer from the closure
    let get_func_id = ctx
        .func_ids
        .get("vole_closure_get_func")
        .ok_or_else(|| "vole_closure_get_func not found".to_string())?;
    let get_func_ref = ctx.module.declare_func_in_func(*get_func_id, builder.func);
    let get_func_call = builder.ins().call(get_func_ref, &[closure_ptr]);
    let func_ptr = builder.inst_results(get_func_call)[0];

    // Build the Cranelift signature for the closure call
    // First param is the closure pointer, then the user params
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(ctx.pointer_type)); // Closure pointer
    for param_type in &ft.params {
        sig.params.push(AbiParam::new(type_to_cranelift(
            param_type,
            ctx.pointer_type,
        )));
    }
    sig.returns.push(AbiParam::new(type_to_cranelift(
        &ft.return_type,
        ctx.pointer_type,
    )));

    let sig_ref = builder.import_signature(sig);

    // Compile arguments - closure pointer first, then user args
    let mut arg_values = vec![closure_ptr];
    for arg in args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        arg_values.push(compiled.value);
    }

    // Perform the indirect call
    let call_inst = builder.ins().call_indirect(sig_ref, func_ptr, &arg_values);
    let results = builder.inst_results(call_inst);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type: (*ft.return_type).clone(),
        })
    }
}

/// Compile println builtin - dispatches to correct vole_println_* based on argument type
pub(crate) fn compile_println(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("println expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Dispatch based on argument type
    // We use vole_type to distinguish strings from regular I64 values
    let (func_name, call_arg) = if matches!(arg.vole_type, Type::String) {
        ("vole_println_string", arg.value)
    } else if arg.ty == types::F64 {
        ("vole_println_f64", arg.value)
    } else if arg.ty == types::I8 {
        ("vole_println_bool", arg.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if arg.ty.is_int() && arg.ty != types::I64 {
            builder.ins().sextend(types::I64, arg.value)
        } else {
            arg.value
        };
        ("vole_println_i64", extended)
    };

    let func_id = ctx
        .func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[call_arg]);

    // println returns void, but we need to return something
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile print_char builtin for mandelbrot ASCII output
pub(crate) fn compile_print_char(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("print_char expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Convert to u8 if needed (truncate from i64)
    let char_val = if arg.ty == types::I64 {
        builder.ins().ireduce(types::I8, arg.value)
    } else if arg.ty == types::I8 {
        arg.value
    } else {
        return Err("print_char expects an integer argument".to_string());
    };

    let func_id = ctx
        .func_ids
        .get("vole_print_char")
        .ok_or_else(|| "vole_print_char not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[char_val]);

    // Return void (as i64 zero)
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile assert builtin - checks condition and calls vole_assert_fail if false
pub(crate) fn compile_assert(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("assert expects exactly one argument".to_string());
    }

    // Compile the condition
    let cond = compile_expr(builder, &args[0], variables, ctx)?;

    // Create pass and fail blocks
    let pass_block = builder.create_block();
    let fail_block = builder.create_block();

    // Branch on condition (extend bool to i32 for brif)
    let cond_i32 = builder.ins().uextend(types::I32, cond.value);
    builder
        .ins()
        .brif(cond_i32, pass_block, &[], fail_block, &[]);

    // Fail block: call vole_assert_fail and trap
    builder.switch_to_block(fail_block);
    {
        // Get vole_assert_fail function
        let func_id = ctx
            .func_ids
            .get("vole_assert_fail")
            .ok_or_else(|| "vole_assert_fail not found".to_string())?;
        let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

        // Pass source file pointer and length from JitContext
        // The source_file_ptr points to memory in JitContext that lives as long as the JIT code
        let (file_ptr, file_len) = ctx.source_file_ptr;
        let line = call_line as i32;

        let file_ptr_val = builder.ins().iconst(ctx.pointer_type, file_ptr as i64);
        let file_len_val = builder.ins().iconst(types::I64, file_len as i64);
        let line_val = builder.ins().iconst(types::I32, line as i64);

        builder
            .ins()
            .call(func_ref, &[file_ptr_val, file_len_val, line_val]);

        // Trap after calling assert_fail (this should not be reached due to longjmp, but
        // we need to terminate the block)
        // Note: TrapCode::user(0) returns None because TrapCode uses NonZeroU8, so we use 1
        builder.ins().trap(TrapCode::unwrap_user(1));
    }

    // Seal fail block
    builder.seal_block(fail_block);

    // Pass block: continue execution
    builder.switch_to_block(pass_block);
    builder.seal_block(pass_block);

    // Assert returns void (as i64 zero)
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile a call to a user-defined function
pub(crate) fn compile_user_function_call(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Try to find the function directly first
    let func_id = if let Some(id) = ctx.func_ids.get(name) {
        *id
    } else if let Some(module_path) = ctx.current_module {
        // We're compiling module code - try mangled name for module functions
        let mangled_name = format!("{}::{}", module_path, name);
        if let Some(id) = ctx.func_ids.get(&mangled_name) {
            *id
        } else {
            // Try FFI call for external module functions
            if let Some(native_func) = ctx.native_registry.lookup(module_path, name) {
                // Compile arguments
                let mut arg_values = Vec::new();
                for arg in args {
                    let compiled = compile_expr(builder, arg, variables, ctx)?;
                    arg_values.push(compiled.value);
                }
                return compile_ffi_call(builder, ctx, native_func, &arg_values);
            }
            return Err(format!("{} not found", name));
        }
    } else {
        return Err(format!("undefined function: {}", name));
    };
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

    // Get expected parameter types from the function's signature
    let sig_ref = builder.func.dfg.ext_funcs[func_ref].signature;
    let sig = &builder.func.dfg.signatures[sig_ref];
    let expected_types: Vec<types::Type> = sig.params.iter().map(|p| p.value_type).collect();

    // Compile arguments with type narrowing
    let mut arg_values = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        let expected_ty = expected_types.get(i).copied();

        // Narrow integer types if needed
        let arg_value = if let Some(expected) = expected_ty {
            if compiled.ty.is_int() && expected.is_int() && expected.bits() < compiled.ty.bits() {
                // Truncate to narrower type
                builder.ins().ireduce(expected, compiled.value)
            } else if compiled.ty.is_int()
                && expected.is_int()
                && expected.bits() > compiled.ty.bits()
            {
                // Extend to wider type
                builder.ins().sextend(expected, compiled.value)
            } else {
                compiled.value
            }
        } else {
            compiled.value
        };
        arg_values.push(arg_value);
    }

    let call = builder.ins().call(func_ref, &arg_values);
    let results = builder.inst_results(call);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        // Infer vole_type from Cranelift type
        let vole_type = cranelift_to_vole_type(ty);
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type,
        })
    }
}

/// Compile an FFI call to a native function
pub(crate) fn compile_ffi_call(
    builder: &mut FunctionBuilder,
    ctx: &mut CompileCtx,
    native_func: &NativeFunction,
    args: &[Value],
) -> Result<CompiledValue, String> {
    // Build the Cranelift signature from NativeSignature
    let mut sig = ctx.module.make_signature();
    for param_type in &native_func.signature.params {
        sig.params.push(AbiParam::new(native_type_to_cranelift(
            param_type,
            ctx.pointer_type,
        )));
    }
    if native_func.signature.return_type != NativeType::Nil {
        sig.returns.push(AbiParam::new(native_type_to_cranelift(
            &native_func.signature.return_type,
            ctx.pointer_type,
        )));
    }

    // Import the signature and emit an indirect call
    let sig_ref = builder.import_signature(sig);
    let func_ptr = native_func.ptr;

    // Load the function pointer as a constant
    let func_ptr_val = builder.ins().iconst(ctx.pointer_type, func_ptr as i64);

    // Emit the indirect call
    let call_inst = builder.ins().call_indirect(sig_ref, func_ptr_val, args);
    let results = builder.inst_results(call_inst);

    if results.is_empty() {
        Ok(CompiledValue::void(builder))
    } else {
        // Infer vole_type from native return type
        let vole_type = native_type_to_vole_type(&native_func.signature.return_type);
        Ok(CompiledValue {
            value: results[0],
            ty: native_type_to_cranelift(&native_func.signature.return_type, ctx.pointer_type),
            vole_type,
        })
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
