use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::builtin::compile_builtin_method;
use super::external::compile_external_call;
use crate::codegen::RuntimeFn;
use crate::codegen::interface_vtable::{
    box_interface_value, iface_debug_enabled, interface_method_slot,
};
use crate::codegen::method_resolution::{
    MethodResolutionInput, MethodTarget, resolve_method_target,
};
use crate::codegen::types::{
    CompileCtx, CompiledValue, method_name_id, module_name_id, type_to_cranelift, value_to_word,
    word_to_value,
};
use crate::frontend::{Expr, MethodCallExpr, NodeId, Symbol};
use crate::sema::resolution::ResolvedMethod;
use crate::sema::{FunctionType, Type};

use super::super::calls::compile_closure_call;
use super::super::patterns::compile_expr;

/// Compile a method call: point.distance()
pub(crate) fn compile_method_call(
    builder: &mut FunctionBuilder,
    mc: &MethodCallExpr,
    expr_id: NodeId,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let display_type_symbol = |sym: Symbol| {
        ctx.type_metadata
            .get(&sym)
            .and_then(|meta| match &meta.vole_type {
                Type::Class(class_type) => Some(class_type.name_id),
                Type::Record(record_type) => Some(record_type.name_id),
                _ => None,
            })
            .map(|name_id| ctx.analyzed.name_table.display(name_id, ctx.interner))
            .unwrap_or_else(|| ctx.interner.resolve(sym).to_string())
    };

    let obj = compile_expr(builder, &mc.object, variables, ctx)?;
    let method_name_str = ctx.interner.resolve(mc.method);

    // Handle module method calls (e.g., math.sqrt(16.0))
    // These can be either external native functions (FFI) or pure Vole functions
    if let Type::Module(ref module_type) = obj.vole_type {
        let module_path = ctx.analyzed.name_table.module_path(module_type.module_id);
        // Get the method resolution
        let resolution = ctx.analyzed.method_resolutions.get(expr_id);
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
                // Pure Vole function - call by qualified name
                let name_id = module_name_id(ctx.analyzed, module_type.module_id, method_name_str)
                    .ok_or_else(|| {
                        format!(
                            "Module method {}::{} not interned",
                            module_path, method_name_str
                        )
                    })?;
                let func_key = ctx.func_registry.intern_name_id(name_id);
                let func_id = ctx.func_registry.func_id(func_key).ok_or_else(|| {
                    format!(
                        "Module function {}::{} not found",
                        module_path, method_name_str
                    )
                })?;
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

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
                module_path, method_name_str
            ));
        }
    }

    let method_id = method_name_id(ctx.analyzed, ctx.interner, mc.method).ok_or_else(|| {
        format!(
            "codegen error: method name not interned (method: {})",
            method_name_str
        )
    })?;

    let resolution = ctx.analyzed.method_resolutions.get(expr_id);
    if matches!(
        resolution,
        Some(ResolvedMethod::Implemented {
            is_builtin: true,
            ..
        })
    ) && let Some(result) = compile_builtin_method(builder, &obj, method_name_str, ctx)?
    {
        return Ok(result);
    }

    // Look up method resolution to determine naming convention and return type
    // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
    let target = resolve_method_target(MethodResolutionInput {
        analyzed: ctx.analyzed,
        type_metadata: ctx.type_metadata,
        impl_method_infos: ctx.impl_method_infos,
        method_name_str,
        object_type: &obj.vole_type,
        method_id,
        resolution,
        display_type_symbol,
    })?;

    let (method_info, return_type) = match target {
        MethodTarget::FunctionalInterface { func_type } => {
            if let Type::Interface(interface_type) = &obj.vole_type {
                return compile_interface_dispatch_args(
                    builder,
                    &mc.args,
                    variables,
                    ctx,
                    &obj,
                    interface_type.name,
                    mc.method,
                    func_type,
                );
            }
            return compile_closure_call(builder, obj.value, &func_type, &mc.args, variables, ctx);
        }
        MethodTarget::External {
            external_info,
            return_type,
        } => {
            let param_types = resolution.map(|resolved| resolved.func_type().params.clone());
            let mut args = vec![obj.value];
            if let Some(param_types) = &param_types {
                for (arg, param_type) in mc.args.iter().zip(param_types.iter()) {
                    let compiled = compile_expr(builder, arg, variables, ctx)?;
                    let compiled = if matches!(param_type, Type::Interface(_)) {
                        box_interface_value(builder, ctx, compiled, param_type)?
                    } else {
                        compiled
                    };
                    args.push(compiled.value);
                }
            } else {
                for arg in &mc.args {
                    let compiled = compile_expr(builder, arg, variables, ctx)?;
                    args.push(compiled.value);
                }
            }
            return compile_external_call(builder, ctx, &external_info, &args, &return_type);
        }
        MethodTarget::InterfaceDispatch {
            interface_name,
            method_name,
            func_type,
        } => {
            return compile_interface_dispatch(
                builder,
                mc,
                variables,
                ctx,
                &obj,
                interface_name,
                method_name,
                func_type,
            );
        }
        MethodTarget::Direct {
            method_info,
            return_type,
        }
        | MethodTarget::Implemented {
            method_info,
            return_type,
        }
        | MethodTarget::Default {
            method_info,
            return_type,
        } => (method_info, return_type),
    };
    let method_func_id = ctx
        .func_registry
        .func_id(method_info.func_key)
        .ok_or_else(|| "Unknown method function id".to_string())?;
    let method_func_ref = ctx
        .module
        .declare_func_in_func(method_func_id, builder.func);

    // Args: self first, then user args
    let param_types = resolution.map(|resolved| resolved.func_type().params.clone());
    let mut args = vec![obj.value];
    if let Some(param_types) = &param_types {
        for (arg, param_type) in mc.args.iter().zip(param_types.iter()) {
            let compiled = compile_expr(builder, arg, variables, ctx)?;
            let compiled = if matches!(param_type, Type::Interface(_)) {
                box_interface_value(builder, ctx, compiled, param_type)?
            } else {
                compiled
            };
            args.push(compiled.value);
        }
    } else {
        for arg in &mc.args {
            let compiled = compile_expr(builder, arg, variables, ctx)?;
            args.push(compiled.value);
        }
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

#[allow(clippy::too_many_arguments)]
fn compile_interface_dispatch(
    builder: &mut FunctionBuilder,
    mc: &MethodCallExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
    obj: &CompiledValue,
    interface_name: Symbol,
    method_name: Symbol,
    func_type: FunctionType,
) -> Result<CompiledValue, String> {
    compile_interface_dispatch_args(
        builder,
        &mc.args,
        variables,
        ctx,
        obj,
        interface_name,
        method_name,
        func_type,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn compile_interface_dispatch_args(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
    obj: &CompiledValue,
    interface_name: Symbol,
    method_name: Symbol,
    func_type: FunctionType,
) -> Result<CompiledValue, String> {
    let word_type = ctx.pointer_type;
    let word_bytes = word_type.bytes() as i32;

    let data_word = builder.ins().load(word_type, MemFlags::new(), obj.value, 0);
    let vtable_ptr = builder
        .ins()
        .load(word_type, MemFlags::new(), obj.value, word_bytes);
    let slot = interface_method_slot(
        interface_name,
        method_name,
        &ctx.analyzed.interface_registry,
        ctx.interner,
    )?;
    let func_ptr = builder.ins().load(
        word_type,
        MemFlags::new(),
        vtable_ptr,
        (slot as i32) * word_bytes,
    );

    if iface_debug_enabled() {
        let print_key = ctx
            .func_registry
            .runtime_key(RuntimeFn::PrintlnI64)
            .ok_or_else(|| "println_i64 not registered".to_string())?;
        let print_id = ctx
            .func_registry
            .func_id(print_key)
            .ok_or_else(|| "println_i64 func id missing".to_string())?;
        let print_ref = ctx.module.declare_func_in_func(print_id, builder.func);
        let to_i64 = |builder: &mut FunctionBuilder, val: Value| {
            if word_type == types::I64 {
                val
            } else {
                builder.ins().uextend(types::I64, val)
            }
        };
        let slot_val = builder.ins().iconst(types::I64, slot as i64);
        let data_i64 = to_i64(builder, data_word);
        let vtable_i64 = to_i64(builder, vtable_ptr);
        let func_i64 = to_i64(builder, func_ptr);
        builder.ins().call(print_ref, &[slot_val]);
        builder.ins().call(print_ref, &[data_i64]);
        builder.ins().call(print_ref, &[vtable_i64]);
        builder.ins().call(print_ref, &[func_i64]);
    }

    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(word_type));
    for _ in &func_type.params {
        sig.params.push(AbiParam::new(word_type));
    }
    if func_type.return_type.as_ref() != &Type::Void {
        sig.returns.push(AbiParam::new(word_type));
    }
    let sig_ref = builder.import_signature(sig);

    let heap_alloc_ref = {
        let key = ctx
            .func_registry
            .runtime_key(RuntimeFn::HeapAlloc)
            .ok_or_else(|| "heap allocator not registered".to_string())?;
        let func_id = ctx
            .func_registry
            .func_id(key)
            .ok_or_else(|| "heap allocator function id missing".to_string())?;
        ctx.module.declare_func_in_func(func_id, builder.func)
    };

    let mut call_args = vec![data_word];
    for arg in args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        let word = value_to_word(builder, &compiled, word_type, Some(heap_alloc_ref))?;
        call_args.push(word);
    }

    let call = builder.ins().call_indirect(sig_ref, func_ptr, &call_args);
    let results = builder.inst_results(call);

    if func_type.return_type.as_ref() == &Type::Void {
        return Ok(CompiledValue::void(builder));
    }

    let word = results
        .first()
        .copied()
        .ok_or_else(|| "interface call missing return value".to_string())?;
    let value = word_to_value(builder, word, &func_type.return_type, word_type);
    Ok(CompiledValue {
        value,
        ty: type_to_cranelift(&func_type.return_type, word_type),
        vole_type: (*func_type.return_type).clone(),
    })
}
