// src/codegen/structs/helpers.rs

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::ops::uextend_const;
use crate::types::CompiledValue;
use vole_identity::{NameId, TypeDefId};
use vole_sema::type_arena::{SemaType as ArenaType, TypeArena, TypeId, TypeIdVec};
use vole_sema::{EntityRegistry, PrimitiveType};

/// Get field slot and type for a field access (Cg API - uses TypeCtx internally).
/// This bridges Cg to the new TypeCtx-based API.
pub(crate) fn get_field_slot_and_type_id_cg(
    type_id: TypeId,
    field_name: &str,
    cg: &crate::context::Cg,
) -> CodegenResult<(usize, TypeId)> {
    let type_ctx = cg.type_ctx();
    let arena = type_ctx.arena();

    // Apply function-level substitutions first (for monomorphized generics)
    // This handles the case where type_id is a TypeParam that needs to be
    // substituted with a concrete type (e.g., in duck typing with structural constraints)
    let resolved_type_id = if let Some(func_subs) = cg.substitutions {
        tracing::debug!(
            ?type_id,
            type_display = %arena.display_basic(type_id),
            ?func_subs,
            "field access: applying substitutions"
        );
        arena.expect_substitute(type_id, func_subs, "field access type substitution")
    } else {
        tracing::debug!(
            ?type_id,
            type_display = %arena.display_basic(type_id),
            "field access: no substitutions available"
        );
        type_id
    };

    tracing::debug!(
        ?resolved_type_id,
        resolved_display = %arena.display_basic(resolved_type_id),
        "field access: resolved type"
    );

    let (type_def_id, type_args, _) =
        arena
            .unwrap_class_or_struct(resolved_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch("field access", "class or struct", "other type")
            })?;

    let type_def = type_ctx.query.get_type(type_def_id);
    let generic_info = type_def
        .generic_info
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_info", "type"))?;

    // Build combined substitution map: type params -> type args, plus monomorphization context
    // This allows a single pass through the type tree instead of two.
    let mut combined_subs: FxHashMap<NameId, TypeId> = type_def
        .type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Merge in function-level substitutions (monomorphization context).
    // Prefer concrete function substitutions over placeholder type args from
    // partially-specialized generic instances.
    if let Some(func_subs) = cg.substitutions {
        for (&k, &v) in func_subs {
            let should_override = combined_subs
                .get(&k)
                .is_some_and(|&existing| arena.unwrap_type_param(existing).is_some());
            if should_override || !combined_subs.contains_key(&k) {
                combined_subs.insert(k, v);
            }
        }
    }

    // Compute physical slot: i128 fields use 2 u64 slots, all others use 1.
    // Physical slot is the sum of slot widths for all fields before this one.
    let is_class = arena.unwrap_class(resolved_type_id).is_some();
    let mut physical_slot = 0usize;
    for (idx, field_name_id) in generic_info.field_names.iter().enumerate() {
        let name = type_ctx.query.last_segment(*field_name_id);
        if name.as_deref() == Some(field_name) {
            let base_type_id = generic_info.field_types[idx];
            let field_type_id = if !combined_subs.is_empty() {
                arena.expect_substitute(base_type_id, &combined_subs, "field access substitution")
            } else {
                base_type_id
            };
            // For structs, use the original sema slot (they don't go through instance storage)
            let slot = if is_class { physical_slot } else { idx };
            return Ok((slot, field_type_id));
        }
        // Advance physical slot counter
        let ft = generic_info.field_types[idx];
        let resolved_ft = if !combined_subs.is_empty() {
            arena.expect_substitute(ft, &combined_subs, "field slot width substitution")
        } else {
            ft
        };
        physical_slot += if is_class && crate::types::is_wide_type(resolved_ft, arena) {
            2
        } else {
            1
        };
    }

    Err(CodegenError::not_found(
        "field",
        format!("{} in type", field_name),
    ))
}

/// Convert a raw i64 field value to the appropriate Cranelift type.
pub(crate) fn convert_field_value_id(
    builder: &mut FunctionBuilder,
    raw_value: Value,
    type_id: TypeId,
    arena: &TypeArena,
) -> (Value, Type) {
    match arena.get(type_id) {
        ArenaType::Primitive(PrimitiveType::F64) => {
            let fval = builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_value);
            (fval, types::F64)
        }
        ArenaType::Primitive(PrimitiveType::F32) => {
            let i32_val = builder.ins().ireduce(types::I32, raw_value);
            let fval = builder.ins().bitcast(types::F32, MemFlags::new(), i32_val);
            (fval, types::F32)
        }
        ArenaType::Primitive(PrimitiveType::F128) => {
            panic!("f128 cannot be reconstructed from a single i64 slot")
        }
        ArenaType::Primitive(PrimitiveType::Bool) => {
            let bval = builder.ins().ireduce(types::I8, raw_value);
            (bval, types::I8)
        }
        ArenaType::Primitive(PrimitiveType::I8 | PrimitiveType::U8) => {
            let val = builder.ins().ireduce(types::I8, raw_value);
            (val, types::I8)
        }
        ArenaType::Primitive(PrimitiveType::I16 | PrimitiveType::U16) => {
            let val = builder.ins().ireduce(types::I16, raw_value);
            (val, types::I16)
        }
        ArenaType::Primitive(PrimitiveType::I32 | PrimitiveType::U32) => {
            let val = builder.ins().ireduce(types::I32, raw_value);
            (val, types::I32)
        }
        ArenaType::Primitive(PrimitiveType::String)
        | ArenaType::Array(_)
        | ArenaType::Class { .. } => {
            // Pointers stay as i64
            (raw_value, types::I64)
        }
        _ => (raw_value, types::I64),
    }
}

pub(crate) fn convert_to_i64_for_storage(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
) -> Value {
    match value.ty {
        types::F64 => builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), value.value),
        types::F32 => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            uextend_const(builder, types::I64, i32_val)
        }
        types::I8 => uextend_const(builder, types::I64, value.value),
        types::I16 => uextend_const(builder, types::I64, value.value),
        types::I32 => uextend_const(builder, types::I64, value.value),
        types::I64 => value.value,
        // i128 should not reach here - callers must use store_field_value,
        // split_i128_for_storage, or store_i128_to_stack instead
        types::I128 => panic!("i128 must use store_field_value for 2-slot storage"),
        types::F128 => panic!("f128 must use store_field_value for 2-slot storage"),
        _ => value.value,
    }
}

/// Split an i128 value into (low, high) i64 halves.
/// Used for fallible returns and stack storage of wide types.
pub(crate) fn split_i128_for_storage(
    builder: &mut FunctionBuilder,
    value: Value,
) -> (Value, Value) {
    let low = builder.ins().ireduce(types::I64, value);
    let sixty_four_i64 = builder.ins().iconst(types::I64, 64);
    let sixty_four = uextend_const(builder, types::I128, sixty_four_i64);
    let shifted = builder.ins().ushr(value, sixty_four);
    let high = builder.ins().ireduce(types::I64, shifted);
    (low, high)
}

/// Reconstruct an i128 from (low, high) i64 halves.
/// Reverse of `split_i128_for_storage`.
pub(crate) fn reconstruct_i128(builder: &mut FunctionBuilder, low: Value, high: Value) -> Value {
    let low_ext = uextend_const(builder, types::I128, low);
    let high_ext = uextend_const(builder, types::I128, high);
    let sixty_four_i64 = builder.ins().iconst(types::I64, 64);
    let sixty_four = uextend_const(builder, types::I128, sixty_four_i64);
    let high_shifted = builder.ins().ishl(high_ext, sixty_four);
    builder.ins().bor(high_shifted, low_ext)
}

/// Store an i128 value to a stack slot at the given offset (uses 16 bytes: 2 x 8-byte slots).
pub(crate) fn store_i128_to_stack(
    builder: &mut FunctionBuilder,
    value: Value,
    slot: codegen::ir::StackSlot,
    offset: i32,
) {
    let (low, high) = split_i128_for_storage(builder, value);
    builder.ins().stack_store(low, slot, offset);
    builder.ins().stack_store(high, slot, offset + 8);
}

/// Store a field value to a stack slot, handling i128 which needs 2 x 8-byte slots.
/// For i128: stores low 64 bits at `offset`, high 64 bits at `offset + 8`.
/// For all other types: stores via convert_to_i64_for_storage at `offset`.
/// Returns the number of bytes consumed (8 for normal types, 16 for i128).
pub(crate) fn store_value_to_stack(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    slot: codegen::ir::StackSlot,
    offset: i32,
) -> i32 {
    if value.ty == types::I128 || value.ty == types::F128 {
        let wide = if value.ty == types::F128 {
            builder
                .ins()
                .bitcast(types::I128, MemFlags::new(), value.value)
        } else {
            value.value
        };
        store_i128_to_stack(builder, wide, slot, offset);
        16
    } else {
        let store_val = convert_to_i64_for_storage(builder, value);
        builder.ins().stack_store(store_val, slot, offset);
        8
    }
}

/// Store a field value into a class instance, handling wide types (i128) that need 2 slots.
/// For i128: stores low 64 bits in `slot`, high 64 bits in `slot+1`.
/// For all other types: stores via convert_to_i64_for_storage in a single slot.
pub(crate) fn store_field_value(
    cg: &mut crate::context::Cg,
    set_func_ref: codegen::ir::FuncRef,
    instance_ptr: Value,
    slot: usize,
    value: &CompiledValue,
) {
    let slot_val = cg.iconst_cached(types::I32, slot as i64);

    if value.ty == types::I128 || value.ty == types::F128 {
        // Split wide values into low/high halves and store in 2 consecutive slots.
        let wide = if value.ty == types::F128 {
            cg.builder
                .ins()
                .bitcast(types::I128, MemFlags::new(), value.value)
        } else {
            value.value
        };
        let (low, high) = split_i128_for_storage(cg.builder, wide);
        cg.builder
            .ins()
            .call(set_func_ref, &[instance_ptr, slot_val, low]);
        let high_slot = cg.iconst_cached(types::I32, (slot + 1) as i64);
        cg.builder
            .ins()
            .call(set_func_ref, &[instance_ptr, high_slot, high]);
    } else {
        let store_value = convert_to_i64_for_storage(cg.builder, value);
        cg.builder
            .ins()
            .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
    }
}

/// Load a field value from a class instance, handling wide types (i128) that use 2 slots.
/// For i128: loads low 64 bits from `slot` and high 64 bits from `slot+1`, reconstructs i128.
/// For all other types: loads from a single slot via convert_field_value_id.
pub(crate) fn load_wide_field(
    cg: &mut crate::context::Cg,
    get_func_ref: codegen::ir::FuncRef,
    instance_ptr: Value,
    slot: usize,
) -> Value {
    let slot_val = cg.iconst_cached(types::I32, slot as i64);
    let low_raw = cg
        .builder
        .ins()
        .call(get_func_ref, &[instance_ptr, slot_val]);
    let low = cg.builder.func.dfg.inst_results(low_raw)[0];

    let high_slot = cg.iconst_cached(types::I32, (slot + 1) as i64);
    let high_raw = cg
        .builder
        .ins()
        .call(get_func_ref, &[instance_ptr, high_slot]);
    let high = cg.builder.func.dfg.inst_results(high_raw)[0];

    reconstruct_i128(cg.builder, low, high)
}

// ============================================================================
// Struct flat layout helpers
//
// Structs store all data inline, including nested structs. Each leaf field
// occupies one 8-byte "slot". The "flat slot count" recursively counts all
// leaf slots so that a struct like:
//
//   struct Point { x: i64, y: i64 }            // 2 flat slots
//   struct Rect { tl: Point, br: Point }        // 4 flat slots
//
// allocates enough space for all nested data. Field byte offsets are computed
// by summing the flat sizes of all preceding fields.
// ============================================================================

/// Compute the number of flat 8-byte slots a struct type occupies,
/// recursively expanding nested struct fields.
/// Returns None if the type is not a struct.
pub(crate) fn struct_flat_slot_count(
    type_id: TypeId,
    arena: &TypeArena,
    entities: &EntityRegistry,
) -> Option<usize> {
    let (type_def_id, type_args) = arena.unwrap_struct(type_id)?;
    let type_def = entities.get_type(type_def_id);
    let generic_info = type_def.generic_info.as_ref()?;

    // Build substitution map for generic structs (type param NameId -> concrete TypeId)
    let subs = build_type_arg_subs(type_def_id, type_args, entities);

    let mut total = 0usize;
    for field_type in &generic_info.field_types {
        let concrete_type = substitute_field_type(*field_type, &subs, arena);
        total += field_flat_slots(concrete_type, arena, entities);
    }
    Some(total)
}

/// Compute the number of flat 8-byte slots a single field occupies.
/// Nested struct fields are recursively expanded; i128 uses 2 slots (16 bytes);
/// all other non-struct types use 1 slot.
pub(crate) fn field_flat_slots(
    type_id: TypeId,
    arena: &TypeArena,
    entities: &EntityRegistry,
) -> usize {
    if let Some(count) = struct_flat_slot_count(type_id, arena, entities) {
        return count;
    }
    // i128 needs 2 x 8-byte slots
    crate::types::field_slot_count(type_id, arena)
}

/// Map a leaf TypeId to its Cranelift type for equality comparison.
/// Wide types (i128, f128) map to their 128-bit Cranelift types.
/// Float types map to F32/F64/F128 so callers can use fcmp instead of icmp.
fn leaf_cranelift_type(type_id: TypeId, arena: &TypeArena) -> Type {
    match arena.get(type_id) {
        ArenaType::Primitive(PrimitiveType::F32) => types::F32,
        ArenaType::Primitive(PrimitiveType::F64) => types::F64,
        ArenaType::Primitive(PrimitiveType::F128) => types::F128,
        ArenaType::Primitive(PrimitiveType::I128) => types::I128,
        _ => types::I64,
    }
}

/// Collect (byte_offset, cranelift_type) for every leaf slot in a struct,
/// recursively flattening nested struct fields.
///
/// Wide types (i128, f128) occupy 16 bytes but produce a single entry so
/// callers can issue one wide load+compare rather than two i64 compares.
/// Returns None if `type_id` is not a struct type.
pub(crate) fn struct_flat_field_cranelift_types(
    type_id: TypeId,
    arena: &TypeArena,
    entities: &EntityRegistry,
) -> Option<Vec<(i32, Type)>> {
    let (type_def_id, type_args) = arena.unwrap_struct(type_id)?;
    let type_def = entities.get_type(type_def_id);
    let generic_info = type_def.generic_info.as_ref()?;

    let subs = build_type_arg_subs(type_def_id, type_args, entities);

    let mut result = Vec::new();
    let mut offset = 0i32;
    for field_type in &generic_info.field_types {
        let concrete = substitute_field_type(*field_type, &subs, arena);
        collect_leaf_slots(concrete, arena, entities, &mut offset, &mut result);
    }
    Some(result)
}

/// Recursively collect leaf (offset, cranelift_type) entries for a field type.
/// Nested structs are flattened; leaf types produce a single entry.
fn collect_leaf_slots(
    type_id: TypeId,
    arena: &TypeArena,
    entities: &EntityRegistry,
    offset: &mut i32,
    out: &mut Vec<(i32, Type)>,
) {
    // Recursively flatten nested structs
    if let Some((nested_def, nested_args)) = arena.unwrap_struct(type_id) {
        let nested_def_data = entities.get_type(nested_def);
        if let Some(nested_info) = nested_def_data.generic_info.as_ref() {
            let nested_subs = build_type_arg_subs(nested_def, nested_args, entities);
            for field_type in &nested_info.field_types {
                let concrete = substitute_field_type(*field_type, &nested_subs, arena);
                collect_leaf_slots(concrete, arena, entities, offset, out);
            }
            return;
        }
    }
    // Leaf field: emit one entry and advance offset by the field's byte size
    let cl_type = leaf_cranelift_type(type_id, arena);
    out.push((*offset, cl_type));
    let byte_size = crate::types::field_byte_size(type_id, arena) as i32;
    *offset += byte_size;
}

/// Compute the byte offset of field `slot` within a struct, accounting
/// for nested struct fields that occupy more than one 8-byte slot.
/// Returns None if the type is not a struct or `slot` is out of range.
pub(crate) fn struct_field_byte_offset(
    type_id: TypeId,
    slot: usize,
    arena: &TypeArena,
    entities: &EntityRegistry,
) -> Option<i32> {
    let (type_def_id, type_args) = arena.unwrap_struct(type_id)?;
    let type_def = entities.get_type(type_def_id);
    let generic_info = type_def.generic_info.as_ref()?;

    if slot > generic_info.field_types.len() {
        return None;
    }

    // Build substitution map for generic structs
    let subs = build_type_arg_subs(type_def_id, type_args, entities);

    let mut offset = 0i32;
    for field_type in generic_info.field_types.iter().take(slot) {
        let concrete_type = substitute_field_type(*field_type, &subs, arena);
        let slots = field_flat_slots(concrete_type, arena, entities);
        offset += (slots as i32) * 8;
    }
    Some(offset)
}

/// Total byte size of a struct, accounting for nested struct fields.
pub(crate) fn struct_total_byte_size(
    type_id: TypeId,
    arena: &TypeArena,
    entities: &EntityRegistry,
) -> Option<u32> {
    struct_flat_slot_count(type_id, arena, entities).map(|n| (n as u32) * 8)
}

/// Build a substitution map from a generic struct's type_params and type_args.
/// Returns an empty map for non-generic structs.
fn build_type_arg_subs(
    type_def_id: TypeDefId,
    type_args: &TypeIdVec,
    entities: &EntityRegistry,
) -> FxHashMap<NameId, TypeId> {
    if type_args.is_empty() {
        return FxHashMap::default();
    }
    let type_params = entities.type_params(type_def_id);
    type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect()
}

/// Resolve a field type through type argument substitutions.
/// For non-generic structs (empty subs), returns the original type.
fn substitute_field_type(
    field_type: TypeId,
    subs: &FxHashMap<NameId, TypeId>,
    arena: &TypeArena,
) -> TypeId {
    if subs.is_empty() {
        return field_type;
    }
    arena
        .lookup_substitute(field_type, subs)
        .unwrap_or(field_type)
}
