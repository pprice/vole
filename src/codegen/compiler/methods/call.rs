use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::builtin::compile_builtin_method;
use super::external::compile_external_call;
use super::iterators::{
    compile_iterator_filter, compile_iterator_for_each, compile_iterator_map,
    compile_iterator_reduce, compile_iterator_skip, compile_iterator_take,
};
use crate::codegen::structs::get_type_name_symbol;
use crate::codegen::types::{
    CompileCtx, CompiledValue, display_type, method_name_id, module_name_id, type_to_cranelift,
};
use crate::frontend::{MethodCallExpr, NodeId, Symbol};
use crate::sema::Type;
use crate::sema::implement_registry::TypeId;
use crate::sema::resolution::ResolvedMethod;

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
    let display_type = |ty: &Type| display_type(ctx.analyzed, ctx.interner, ty);
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

    // Handle built-in methods for primitive types
    if let Some(result) = compile_builtin_method(builder, &obj, method_name_str, ctx)? {
        return Ok(result);
    }

    let method_id = method_name_id(ctx.analyzed, ctx.interner, mc.method).ok_or_else(|| {
        format!(
            "codegen error: method name not interned (method: {})",
            method_name_str
        )
    })?;

    // Handle iterator.map(fn) -> creates a MapIterator
    // Also handle MapIterator.map(fn), FilterIterator.map(fn), TakeIterator.map(fn), SkipIterator.map(fn) for chained maps
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "map"
    {
        return compile_iterator_map(builder, &obj, elem_ty.as_ref(), &mc.args, variables, ctx);
    }

    // Handle iterator.filter(fn) -> creates a FilterIterator
    // Also handle MapIterator.filter(fn), FilterIterator.filter(fn), TakeIterator.filter(fn), SkipIterator.filter(fn) for chained filters
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "filter"
    {
        return compile_iterator_filter(builder, &obj, elem_ty.as_ref(), &mc.args, variables, ctx);
    }

    // Handle iterator.take(n) -> creates a TakeIterator
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "take"
    {
        return compile_iterator_take(builder, &obj, elem_ty.as_ref(), &mc.args, variables, ctx);
    }

    // Handle iterator.skip(n) -> creates a SkipIterator
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "skip"
    {
        return compile_iterator_skip(builder, &obj, elem_ty.as_ref(), &mc.args, variables, ctx);
    }

    // Handle iterator.for_each(fn) -> calls function for each element
    if let Type::Iterator(_)
    | Type::MapIterator(_)
    | Type::FilterIterator(_)
    | Type::TakeIterator(_)
    | Type::SkipIterator(_) = &obj.vole_type
        && method_name_str == "for_each"
    {
        return compile_iterator_for_each(builder, &obj, &mc.args, variables, ctx);
    }

    // Handle iterator.reduce(init, fn) -> reduces iterator to single value
    if let Type::Iterator(_)
    | Type::MapIterator(_)
    | Type::FilterIterator(_)
    | Type::TakeIterator(_)
    | Type::SkipIterator(_) = &obj.vole_type
        && method_name_str == "reduce"
    {
        return compile_iterator_reduce(builder, &obj, &mc.args, variables, ctx);
    }

    // Look up method resolution to determine naming convention and return type
    // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
    let resolution = ctx.analyzed.method_resolutions.get(expr_id);

    // Determine the method function target based on resolution type
    let (method_info, return_type) = if let Some(resolution) = resolution {
        match resolution {
            ResolvedMethod::Direct { func_type } => {
                // Direct method on class/record: use TypeName_methodName
                let type_name = get_type_name_symbol(&obj.vole_type)?;
                let info = ctx
                    .type_metadata
                    .get(&type_name)
                    .and_then(|meta| meta.method_infos.get(&method_id))
                    .cloned()
                    .ok_or_else(|| {
                        format!(
                            "Method {} not found on type {}",
                            method_name_str,
                            display_type_symbol(type_name)
                        )
                    })?;
                (Some(info), (*func_type.return_type).clone())
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
                let type_id = TypeId::from_type(&obj.vole_type, &ctx.analyzed.type_table);
                let info = type_id
                    .and_then(|type_id| ctx.impl_method_infos.get(&(type_id, method_id)).cloned());
                (info, (*func_type.return_type).clone())
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
                let info = ctx
                    .type_metadata
                    .get(type_name)
                    .and_then(|meta| meta.method_infos.get(&method_id))
                    .cloned()
                    .ok_or_else(|| {
                        format!(
                            "Method {} not found on type {}",
                            method_name_str,
                            display_type_symbol(*type_name)
                        )
                    })?;
                (Some(info), (*func_type.return_type).clone())
            }
        }
    } else {
        // No resolution found - try to resolve directly from object type
        // This handles method calls inside default method bodies where sema
        // doesn't analyze the interface body
        let type_name = get_type_name_symbol(&obj.vole_type)?;

        let info = ctx
            .type_metadata
            .get(&type_name)
            .and_then(|meta| meta.method_infos.get(&method_id))
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Method {} not found on type {}",
                    method_name_str,
                    display_type_symbol(type_name)
                )
            })?;
        let return_type = info.return_type.clone();
        (Some(info), return_type)
    };

    let method_info = method_info.ok_or_else(|| {
        format!(
            "Unknown method {} on {}",
            method_name_str,
            display_type(&obj.vole_type)
        )
    })?;
    let method_func_id = ctx
        .func_registry
        .func_id(method_info.func_key)
        .ok_or_else(|| "Unknown method function id".to_string())?;
    let method_func_ref = ctx
        .module
        .declare_func_in_func(method_func_id, builder.func);

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
