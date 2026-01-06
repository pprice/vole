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

    // Handle iterator.map(fn) -> creates a MapIterator
    // Also handle MapIterator.map(fn), FilterIterator.map(fn), TakeIterator.map(fn), SkipIterator.map(fn) for chained maps
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "map"
    {
        return compile_iterator_map(builder, &obj, elem_ty, &mc.args, variables, ctx);
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
        return compile_iterator_filter(builder, &obj, elem_ty, &mc.args, variables, ctx);
    }

    // Handle iterator.take(n) -> creates a TakeIterator
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "take"
    {
        return compile_iterator_take(builder, &obj, elem_ty, &mc.args, variables, ctx);
    }

    // Handle iterator.skip(n) -> creates a SkipIterator
    if let Type::Iterator(elem_ty)
    | Type::MapIterator(elem_ty)
    | Type::FilterIterator(elem_ty)
    | Type::TakeIterator(elem_ty)
    | Type::SkipIterator(elem_ty) = &obj.vole_type
        && method_name_str == "skip"
    {
        return compile_iterator_skip(builder, &obj, elem_ty, &mc.args, variables, ctx);
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
        // Iterator.next() -> T | Done
        (Type::Iterator(elem_ty), "next") => {
            // Create stack slot for output value (8 bytes for i64)
            let out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                8,
                0,
            ));
            let out_ptr = builder.ins().stack_addr(ctx.pointer_type, out_slot, 0);

            // Call runtime: has_value = vole_array_iter_next(iter, out_ptr)
            let func_id = ctx
                .func_ids
                .get("vole_array_iter_next")
                .ok_or_else(|| "vole_array_iter_next not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value, out_ptr]);
            let has_value = builder.inst_results(call)[0];

            // Load value from out_slot
            let value = builder.ins().stack_load(types::I64, out_slot, 0);

            // Build union result: T | Done
            // Union layout: [tag:1][padding:7][payload:8] = 16 bytes
            // Tag 0 = element type (T), Tag 1 = Done
            let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
            let union_size = 16u32; // tag(1) + padding(7) + payload(8)
            let union_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                union_size,
                0,
            ));

            // Determine tag based on has_value:
            // has_value != 0 => tag = 0 (element type)
            // has_value == 0 => tag = 1 (Done)
            let zero = builder.ins().iconst(types::I64, 0);
            let is_done = builder.ins().icmp(IntCC::Equal, has_value, zero);
            let tag_done = builder.ins().iconst(types::I8, 1);
            let tag_value = builder.ins().iconst(types::I8, 0);
            let tag = builder.ins().select(is_done, tag_done, tag_value);

            // Store tag at offset 0
            builder.ins().stack_store(tag, union_slot, 0);

            // Store payload at offset 8 (value if has_value, 0 if done)
            builder.ins().stack_store(value, union_slot, 8);

            let union_ptr = builder.ins().stack_addr(ctx.pointer_type, union_slot, 0);
            Ok(Some(CompiledValue {
                value: union_ptr,
                ty: ctx.pointer_type,
                vole_type: union_type,
            }))
        }
        // Iterator.collect() -> [T]
        (Type::Iterator(elem_ty), "collect") => {
            let func_id = ctx
                .func_ids
                .get("vole_array_iter_collect")
                .ok_or_else(|| "vole_array_iter_collect not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: ctx.pointer_type,
                vole_type: Type::Array(elem_ty.clone()),
            }))
        }
        // MapIterator.next() -> T | Done
        (Type::MapIterator(elem_ty), "next") => {
            // Create stack slot for output value (8 bytes for i64)
            let out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                8,
                0,
            ));
            let out_ptr = builder.ins().stack_addr(ctx.pointer_type, out_slot, 0);

            // Call runtime: has_value = vole_map_iter_next(iter, out_ptr)
            let func_id = ctx
                .func_ids
                .get("vole_map_iter_next")
                .ok_or_else(|| "vole_map_iter_next not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value, out_ptr]);
            let has_value = builder.inst_results(call)[0];

            // Load value from out_slot
            let value = builder.ins().stack_load(types::I64, out_slot, 0);

            // Build union result: T | Done
            // Union layout: [tag:1][padding:7][payload:8] = 16 bytes
            // Tag 0 = element type (T), Tag 1 = Done
            let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
            let union_size = 16u32; // tag(1) + padding(7) + payload(8)
            let union_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                union_size,
                0,
            ));

            // Determine tag based on has_value:
            // has_value != 0 => tag = 0 (element type)
            // has_value == 0 => tag = 1 (Done)
            let zero = builder.ins().iconst(types::I64, 0);
            let is_done = builder.ins().icmp(IntCC::Equal, has_value, zero);
            let tag_done = builder.ins().iconst(types::I8, 1);
            let tag_value = builder.ins().iconst(types::I8, 0);
            let tag = builder.ins().select(is_done, tag_done, tag_value);

            // Store tag at offset 0
            builder.ins().stack_store(tag, union_slot, 0);

            // Store payload at offset 8 (value if has_value, 0 if done)
            builder.ins().stack_store(value, union_slot, 8);

            let union_ptr = builder.ins().stack_addr(ctx.pointer_type, union_slot, 0);
            Ok(Some(CompiledValue {
                value: union_ptr,
                ty: ctx.pointer_type,
                vole_type: union_type,
            }))
        }
        // MapIterator.collect() -> [T]
        (Type::MapIterator(elem_ty), "collect") => {
            let func_id = ctx
                .func_ids
                .get("vole_map_iter_collect")
                .ok_or_else(|| "vole_map_iter_collect not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: ctx.pointer_type,
                vole_type: Type::Array(elem_ty.clone()),
            }))
        }
        // FilterIterator.next() -> T | Done
        (Type::FilterIterator(elem_ty), "next") => {
            // Create stack slot for output value (8 bytes for i64)
            let out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                8,
                0,
            ));
            let out_ptr = builder.ins().stack_addr(ctx.pointer_type, out_slot, 0);

            // Call runtime: has_value = vole_filter_iter_next(iter, out_ptr)
            let func_id = ctx
                .func_ids
                .get("vole_filter_iter_next")
                .ok_or_else(|| "vole_filter_iter_next not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value, out_ptr]);
            let has_value = builder.inst_results(call)[0];

            // Load value from out_slot
            let value = builder.ins().stack_load(types::I64, out_slot, 0);

            // Build union result: T | Done
            // Union layout: [tag:1][padding:7][payload:8] = 16 bytes
            // Tag 0 = element type (T), Tag 1 = Done
            let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
            let union_size = 16u32; // tag(1) + padding(7) + payload(8)
            let union_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                union_size,
                0,
            ));

            // Determine tag based on has_value:
            // has_value != 0 => tag = 0 (element type)
            // has_value == 0 => tag = 1 (Done)
            let zero = builder.ins().iconst(types::I64, 0);
            let is_done = builder.ins().icmp(IntCC::Equal, has_value, zero);
            let tag_done = builder.ins().iconst(types::I8, 1);
            let tag_value = builder.ins().iconst(types::I8, 0);
            let tag = builder.ins().select(is_done, tag_done, tag_value);

            // Store tag at offset 0
            builder.ins().stack_store(tag, union_slot, 0);

            // Store payload at offset 8 (value if has_value, 0 if done)
            builder.ins().stack_store(value, union_slot, 8);

            let union_ptr = builder.ins().stack_addr(ctx.pointer_type, union_slot, 0);
            Ok(Some(CompiledValue {
                value: union_ptr,
                ty: ctx.pointer_type,
                vole_type: union_type,
            }))
        }
        // FilterIterator.collect() -> [T]
        (Type::FilterIterator(elem_ty), "collect") => {
            let func_id = ctx
                .func_ids
                .get("vole_filter_iter_collect")
                .ok_or_else(|| "vole_filter_iter_collect not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: ctx.pointer_type,
                vole_type: Type::Array(elem_ty.clone()),
            }))
        }
        // TakeIterator.next() -> T | Done
        (Type::TakeIterator(elem_ty), "next") => {
            // Create stack slot for output value (8 bytes for i64)
            let out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                8,
                0,
            ));
            let out_ptr = builder.ins().stack_addr(ctx.pointer_type, out_slot, 0);

            // Call runtime: has_value = vole_take_iter_next(iter, out_ptr)
            let func_id = ctx
                .func_ids
                .get("vole_take_iter_next")
                .ok_or_else(|| "vole_take_iter_next not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value, out_ptr]);
            let has_value = builder.inst_results(call)[0];

            // Load value from out_slot
            let value = builder.ins().stack_load(types::I64, out_slot, 0);

            // Build union result: T | Done
            let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
            let union_size = 16u32;
            let union_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                union_size,
                0,
            ));

            let zero = builder.ins().iconst(types::I64, 0);
            let is_done = builder.ins().icmp(IntCC::Equal, has_value, zero);
            let tag_done = builder.ins().iconst(types::I8, 1);
            let tag_value = builder.ins().iconst(types::I8, 0);
            let tag = builder.ins().select(is_done, tag_done, tag_value);

            builder.ins().stack_store(tag, union_slot, 0);
            builder.ins().stack_store(value, union_slot, 8);

            let union_ptr = builder.ins().stack_addr(ctx.pointer_type, union_slot, 0);
            Ok(Some(CompiledValue {
                value: union_ptr,
                ty: ctx.pointer_type,
                vole_type: union_type,
            }))
        }
        // TakeIterator.collect() -> [T]
        (Type::TakeIterator(elem_ty), "collect") => {
            let func_id = ctx
                .func_ids
                .get("vole_take_iter_collect")
                .ok_or_else(|| "vole_take_iter_collect not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: ctx.pointer_type,
                vole_type: Type::Array(elem_ty.clone()),
            }))
        }
        // SkipIterator.next() -> T | Done
        (Type::SkipIterator(elem_ty), "next") => {
            // Create stack slot for output value (8 bytes for i64)
            let out_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                8,
                0,
            ));
            let out_ptr = builder.ins().stack_addr(ctx.pointer_type, out_slot, 0);

            // Call runtime: has_value = vole_skip_iter_next(iter, out_ptr)
            let func_id = ctx
                .func_ids
                .get("vole_skip_iter_next")
                .ok_or_else(|| "vole_skip_iter_next not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value, out_ptr]);
            let has_value = builder.inst_results(call)[0];

            // Load value from out_slot
            let value = builder.ins().stack_load(types::I64, out_slot, 0);

            // Build union result: T | Done
            let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
            let union_size = 16u32;
            let union_slot = builder.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                union_size,
                0,
            ));

            let zero = builder.ins().iconst(types::I64, 0);
            let is_done = builder.ins().icmp(IntCC::Equal, has_value, zero);
            let tag_done = builder.ins().iconst(types::I8, 1);
            let tag_value = builder.ins().iconst(types::I8, 0);
            let tag = builder.ins().select(is_done, tag_done, tag_value);

            builder.ins().stack_store(tag, union_slot, 0);
            builder.ins().stack_store(value, union_slot, 8);

            let union_ptr = builder.ins().stack_addr(ctx.pointer_type, union_slot, 0);
            Ok(Some(CompiledValue {
                value: union_ptr,
                ty: ctx.pointer_type,
                vole_type: union_type,
            }))
        }
        // SkipIterator.collect() -> [T]
        (Type::SkipIterator(elem_ty), "collect") => {
            let func_id = ctx
                .func_ids
                .get("vole_skip_iter_collect")
                .ok_or_else(|| "vole_skip_iter_collect not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: ctx.pointer_type,
                vole_type: Type::Array(elem_ty.clone()),
            }))
        }
        // Iterator.count() -> i64 (works on any iterator type)
        (Type::Iterator(_), "count")
        | (Type::MapIterator(_), "count")
        | (Type::FilterIterator(_), "count")
        | (Type::TakeIterator(_), "count")
        | (Type::SkipIterator(_), "count") => {
            let func_id = ctx
                .func_ids
                .get("vole_iter_count")
                .ok_or_else(|| "vole_iter_count not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        // Iterator.sum() -> i64 (works on numeric iterators)
        (Type::Iterator(_), "sum")
        | (Type::MapIterator(_), "sum")
        | (Type::FilterIterator(_), "sum")
        | (Type::TakeIterator(_), "sum")
        | (Type::SkipIterator(_), "sum") => {
            let func_id = ctx
                .func_ids
                .get("vole_iter_sum")
                .ok_or_else(|| "vole_iter_sum not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
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

/// Compile Iterator.map(fn) -> creates a MapIterator
fn compile_iterator_map(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    _elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("map expects 1 argument, got {}", args.len()));
    }

    // Compile the transform function (should be a lambda/closure)
    let transform = compile_expr(builder, &args[0], variables, ctx)?;

    // The transform should be a function
    let (output_type, is_closure) = match &transform.vole_type {
        Type::Function(ft) => ((*ft.return_type).clone(), ft.is_closure),
        _ => {
            return Err(format!(
                "map argument must be a function, got {:?}",
                transform.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        transform.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = ctx
            .func_ids
            .get("vole_closure_alloc")
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_ref = ctx.module.declare_func_in_func(*alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[transform.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_map_iter(source_iter, transform_closure)
    let func_id = ctx
        .func_ids
        .get("vole_map_iter")
        .ok_or_else(|| "vole_map_iter not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, closure_ptr]);
    let result = builder.inst_results(call)[0];

    // MapIterator is stored as IteratorKind::Map internally
    // For now, we track that it's a mapped iterator in the vole_type
    // The collect method will need to check which kind of iterator it is
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::MapIterator(Box::new(output_type)),
    })
}

/// Compile Iterator.filter(fn) -> creates a FilterIterator
fn compile_iterator_filter(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("filter expects 1 argument, got {}", args.len()));
    }

    // Compile the predicate function (should be a lambda/closure)
    let predicate = compile_expr(builder, &args[0], variables, ctx)?;

    // The predicate should be a function returning bool
    let is_closure = match &predicate.vole_type {
        Type::Function(ft) => ft.is_closure,
        _ => {
            return Err(format!(
                "filter argument must be a function, got {:?}",
                predicate.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        predicate.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = ctx
            .func_ids
            .get("vole_closure_alloc")
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_ref = ctx.module.declare_func_in_func(*alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[predicate.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_filter_iter(source_iter, predicate_closure)
    let func_id = ctx
        .func_ids
        .get("vole_filter_iter")
        .ok_or_else(|| "vole_filter_iter not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, closure_ptr]);
    let result = builder.inst_results(call)[0];

    // FilterIterator preserves element type
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::FilterIterator(Box::new(elem_ty.clone())),
    })
}

/// Compile Iterator.take(n) -> creates a TakeIterator
fn compile_iterator_take(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("take expects 1 argument, got {}", args.len()));
    }

    // Compile the count argument (should be an integer)
    let count = compile_expr(builder, &args[0], variables, ctx)?;

    // Call vole_take_iter(source_iter, count)
    let func_id = ctx
        .func_ids
        .get("vole_take_iter")
        .ok_or_else(|| "vole_take_iter not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, count.value]);
    let result = builder.inst_results(call)[0];

    // TakeIterator preserves element type
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::TakeIterator(Box::new(elem_ty.clone())),
    })
}

/// Compile Iterator.skip(n) -> creates a SkipIterator
fn compile_iterator_skip(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("skip expects 1 argument, got {}", args.len()));
    }

    // Compile the count argument (should be an integer)
    let count = compile_expr(builder, &args[0], variables, ctx)?;

    // Call vole_skip_iter(source_iter, count)
    let func_id = ctx
        .func_ids
        .get("vole_skip_iter")
        .ok_or_else(|| "vole_skip_iter not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, count.value]);
    let result = builder.inst_results(call)[0];

    // SkipIterator preserves element type
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::SkipIterator(Box::new(elem_ty.clone())),
    })
}

/// Compile Iterator.for_each(fn) -> calls function for each element, returns void
fn compile_iterator_for_each(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("for_each expects 1 argument, got {}", args.len()));
    }

    // Compile the callback function (should be a lambda/closure)
    let callback = compile_expr(builder, &args[0], variables, ctx)?;

    // The callback should be a function
    let is_closure = match &callback.vole_type {
        Type::Function(ft) => ft.is_closure,
        _ => {
            return Err(format!(
                "for_each argument must be a function, got {:?}",
                callback.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        callback.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = ctx
            .func_ids
            .get("vole_closure_alloc")
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_ref = ctx.module.declare_func_in_func(*alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[callback.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_iter_for_each(iter, callback_closure)
    let func_id = ctx
        .func_ids
        .get("vole_iter_for_each")
        .ok_or_else(|| "vole_iter_for_each not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    builder.ins().call(func_ref, &[iter_obj.value, closure_ptr]);

    // for_each returns void
    Ok(CompiledValue {
        value: builder.ins().iconst(types::I64, 0),
        ty: types::I64,
        vole_type: Type::Void,
    })
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
