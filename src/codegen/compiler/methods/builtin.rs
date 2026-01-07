use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use crate::codegen::RuntimeFn;
use crate::codegen::types::{CompileCtx, CompiledValue};
use crate::sema::Type;

fn runtime_func_id(ctx: &CompileCtx, runtime: RuntimeFn) -> Result<FuncId, String> {
    ctx.func_registry
        .runtime_key(runtime)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| format!("{} not found", runtime.name()))
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
            let func_id = runtime_func_id(ctx, RuntimeFn::ArrayLen)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::ArrayIter)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::ArrayIterNext)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::ArrayIterCollect)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::MapIterNext)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::MapIterCollect)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::FilterIterNext)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::FilterIterCollect)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::TakeIterNext)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::TakeIterCollect)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::SkipIterNext)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::SkipIterCollect)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::IterCount)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::IterSum)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
            let func_id = runtime_func_id(ctx, RuntimeFn::StringLen)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
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
