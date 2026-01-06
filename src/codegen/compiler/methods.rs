// src/codegen/compiler/methods.rs
//
// Method call and try/error propagation codegen.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::calls::compile_closure_call;
use super::patterns::compile_expr;
use crate::codegen::structs::get_type_name_symbol;
use crate::codegen::types::{
    CompileCtx, CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, FALLIBLE_TAG_OFFSET,
    native_type_to_cranelift, type_to_cranelift,
};
use crate::frontend::{Expr, MethodCallExpr, NodeId, Symbol};
use crate::runtime::native_registry::NativeType;
use crate::sema::Type;
use crate::sema::implement_registry::{ExternalMethodInfo, TypeId};
use crate::sema::resolution::ResolvedMethod;

pub(crate) fn compile_try_propagate(
    builder: &mut FunctionBuilder,
    inner: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Compile the inner fallible expression
    let fallible = compile_expr(builder, inner, variables, ctx)?;

    // Get type info
    let success_type = match &fallible.vole_type {
        Type::Fallible(ft) => (*ft.success_type).clone(),
        _ => return Err("try on non-fallible type".to_string()),
    };

    // Load the tag
    let tag = builder.ins().load(
        types::I64,
        MemFlags::new(),
        fallible.value,
        FALLIBLE_TAG_OFFSET,
    );

    // Check if success (tag == 0)
    let is_success = builder
        .ins()
        .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

    // Create blocks
    let success_block = builder.create_block();
    let error_block = builder.create_block();
    let merge_block = builder.create_block();

    // Get payload type for success
    let payload_ty = type_to_cranelift(&success_type, ctx.pointer_type);
    builder.append_block_param(merge_block, payload_ty);

    // Branch based on tag
    builder
        .ins()
        .brif(is_success, success_block, &[], error_block, &[]);

    // Error block: propagate by returning the fallible value
    builder.switch_to_block(error_block);
    builder.seal_block(error_block);
    builder.ins().return_(&[fallible.value]);

    // Success block: extract payload and jump to merge
    builder.switch_to_block(success_block);
    builder.seal_block(success_block);
    let payload = builder.ins().load(
        payload_ty,
        MemFlags::new(),
        fallible.value,
        FALLIBLE_PAYLOAD_OFFSET,
    );
    let payload_arg = BlockArg::from(payload);
    builder.ins().jump(merge_block, &[payload_arg]);

    // Merge block: continue with extracted value
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    let result = builder.block_params(merge_block)[0];

    Ok(CompiledValue {
        value: result,
        ty: payload_ty,
        vole_type: success_type,
    })
}

/// Compile a method call: point.distance()
pub(crate) fn compile_method_call(
    builder: &mut FunctionBuilder,
    mc: &MethodCallExpr,
    expr_id: NodeId,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, &mc.object, variables, ctx)?;
    let method_name_str = ctx.interner.resolve(mc.method);

    // Handle module method calls (e.g., math.sqrt(16.0))
    // These can be either external native functions (FFI) or pure Vole functions
    if let Type::Module(ref module_type) = obj.vole_type {
        // Get the method resolution
        let resolution = ctx.method_resolutions.get(expr_id);
        if let Some(ResolvedMethod::Implemented {
            external_info,
            func_type,
            ..
        }) = resolution
        {
            // Compile arguments (no receiver for module functions)
            let mut args = Vec::new();
            for arg in &mc.args {
                let compiled = compile_expr(builder, arg, variables, ctx)?;
                args.push(compiled.value);
            }

            let return_type = (*func_type.return_type).clone();

            if let Some(ext_info) = external_info {
                // External function - use FFI call
                return compile_external_call(builder, ctx, ext_info, &args, &return_type);
            } else {
                // Pure Vole function - call by mangled name
                let mangled_name = format!("{}::{}", module_type.path, method_name_str);
                let func_id = ctx
                    .func_ids
                    .get(&mangled_name)
                    .ok_or_else(|| format!("Module function {} not found", mangled_name))?;
                let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

                let call = builder.ins().call(func_ref, &args);
                let results = builder.inst_results(call);

                if results.is_empty() {
                    return Ok(CompiledValue::void(builder));
                } else {
                    return Ok(CompiledValue {
                        value: results[0],
                        ty: type_to_cranelift(&return_type, ctx.pointer_type),
                        vole_type: return_type,
                    });
                }
            }
        } else {
            return Err(format!(
                "Module method {}::{} has no resolution",
                module_type.path, method_name_str
            ));
        }
    }

    // Handle built-in methods for primitive types
    if let Some(result) = compile_builtin_method(builder, &obj, method_name_str, ctx)? {
        return Ok(result);
    }

    // Look up method resolution to determine naming convention and return type
    // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
    let resolution = ctx.method_resolutions.get(expr_id);

    // Determine the method function name based on resolution type
    let (full_name, return_type) = if let Some(resolution) = resolution {
        match resolution {
            ResolvedMethod::Direct { func_type } => {
                // Direct method on class/record: use TypeName_methodName
                let type_name = get_type_name_symbol(&obj.vole_type)?;
                let type_name_str = ctx.interner.resolve(type_name);
                let name = format!("{}_{}", type_name_str, method_name_str);
                (name, (*func_type.return_type).clone())
            }
            ResolvedMethod::Implemented {
                func_type,
                is_builtin,
                external_info,
                ..
            } => {
                if *is_builtin {
                    // Built-in methods should have been handled above
                    return Err(format!("Unhandled builtin method: {}", method_name_str));
                }

                // Check if this is an external native method
                if let Some(ext_info) = external_info {
                    // Compile the receiver and arguments
                    let mut args = vec![obj.value];
                    for arg in &mc.args {
                        let compiled = compile_expr(builder, arg, variables, ctx)?;
                        args.push(compiled.value);
                    }

                    // Call the external native function
                    let return_type = (*func_type.return_type).clone();
                    return compile_external_call(builder, ctx, ext_info, &args, &return_type);
                }

                // Implement block method: use TypeName::methodName
                let type_id = TypeId::from_type(&obj.vole_type)
                    .ok_or_else(|| format!("Cannot get TypeId for {:?}", obj.vole_type))?;
                let type_name_str = type_id.type_name(ctx.interner);
                let name = format!("{}::{}", type_name_str, method_name_str);
                (name, (*func_type.return_type).clone())
            }
            ResolvedMethod::FunctionalInterface { func_type } => {
                // For functional interfaces, the object IS the closure pointer
                // Call it as a closure
                return compile_closure_call(
                    builder, obj.value, func_type, &mc.args, variables, ctx,
                );
            }
            ResolvedMethod::DefaultMethod {
                type_name,
                func_type,
                ..
            } => {
                // Default method from interface, monomorphized for the concrete type
                // Name format is TypeName_methodName (same as direct methods)
                let type_name_str = ctx.interner.resolve(*type_name);
                let name = format!("{}_{}", type_name_str, method_name_str);
                (name, (*func_type.return_type).clone())
            }
        }
    } else {
        // No resolution found - try to resolve directly from object type
        // This handles method calls inside default method bodies where sema
        // doesn't analyze the interface body
        let type_name = get_type_name_symbol(&obj.vole_type)?;
        let type_name_str = ctx.interner.resolve(type_name);

        // Look up method return type from type metadata
        let return_type = ctx
            .type_metadata
            .get(&type_name)
            .and_then(|meta| meta.method_return_types.get(&mc.method).cloned())
            .ok_or_else(|| {
                format!(
                    "Method {} not found on type {}",
                    method_name_str, type_name_str
                )
            })?;

        let name = format!("{}_{}", type_name_str, method_name_str);
        (name, return_type)
    };

    let method_func_id = ctx
        .func_ids
        .get(&full_name)
        .ok_or_else(|| format!("Unknown method: {}", full_name))?;
    let method_func_ref = ctx
        .module
        .declare_func_in_func(*method_func_id, builder.func);

    // Args: self first, then user args
    let mut args = vec![obj.value];
    for arg in &mc.args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        args.push(compiled.value);
    }

    let call = builder.ins().call(method_func_ref, &args);
    let results = builder.inst_results(call);

    if results.is_empty() {
        Ok(CompiledValue {
            value: builder.ins().iconst(types::I64, 0),
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        Ok(CompiledValue {
            value: results[0],
            ty: type_to_cranelift(&return_type, ctx.pointer_type),
            vole_type: return_type,
        })
    }
}

/// Compile a built-in method call for primitive types
/// Returns Some(CompiledValue) if handled, None if not a built-in
pub(crate) fn compile_builtin_method(
    builder: &mut FunctionBuilder,
    obj: &CompiledValue,
    method_name: &str,
    ctx: &mut CompileCtx,
) -> Result<Option<CompiledValue>, String> {
    match (&obj.vole_type, method_name) {
        // Array.length() -> i64
        (Type::Array(_), "length") => {
            let func_id = ctx
                .func_ids
                .get("vole_array_len")
                .ok_or_else(|| "vole_array_len not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        // Array.iter() -> Iterator<T>
        (Type::Array(elem_ty), "iter") => {
            let func_id = ctx
                .func_ids
                .get("vole_array_iter")
                .ok_or_else(|| "vole_array_iter not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: ctx.pointer_type,
                vole_type: Type::Iterator(elem_ty.clone()),
            }))
        }
        // String.length() -> i64
        (Type::String, "length") => {
            let func_id = ctx
                .func_ids
                .get("vole_string_len")
                .ok_or_else(|| "vole_string_len not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        _ => Ok(None),
    }
}

/// Compile a call to an external native function.
/// This is used for methods marked with external blocks.
pub(crate) fn compile_external_call(
    builder: &mut FunctionBuilder,
    ctx: &mut CompileCtx,
    external_info: &ExternalMethodInfo,
    args: &[Value],
    return_type: &Type,
) -> Result<CompiledValue, String> {
    // Look up the native function in the registry
    let native_func = ctx
        .native_registry
        .lookup(&external_info.module_path, &external_info.native_name)
        .ok_or_else(|| {
            format!(
                "Native function {}::{} not found in registry",
                external_info.module_path, external_info.native_name
            )
        })?;

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
        Ok(CompiledValue {
            value: results[0],
            ty: type_to_cranelift(return_type, ctx.pointer_type),
            vole_type: return_type.clone(),
        })
    }
}
