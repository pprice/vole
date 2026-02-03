// src/codegen/structs/helpers.rs

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, FunctionCtx, TypeCtx};
use vole_sema::type_arena::{SemaType as ArenaType, TypeArena, TypeId};
use vole_sema::{EntityRegistry, PrimitiveType};

/// Get field slot and type for a field access (new context API).
#[allow(dead_code)]
pub(crate) fn get_field_slot_and_type_id(
    type_id: TypeId,
    field_name: &str,
    type_ctx: &TypeCtx,
    func_ctx: &FunctionCtx,
) -> CodegenResult<(usize, TypeId)> {
    let arena = type_ctx.arena();

    // Apply function-level substitutions first (for monomorphized generics)
    // This handles the case where type_id is a TypeParam that needs to be
    // substituted with a concrete type (e.g., in duck typing with structural constraints)
    let resolved_type_id = if let Some(func_subs) = func_ctx.substitutions {
        arena.expect_substitute(type_id, func_subs, "field access type substitution")
    } else {
        type_id
    };

    // Try class first, then struct
    let (type_def_id, type_args) = arena
        .unwrap_class(resolved_type_id)
        .or_else(|| arena.unwrap_struct(resolved_type_id))
        .ok_or_else(|| {
            CodegenError::type_mismatch("field access", "class or struct", "other type").to_string()
        })?;

    let type_def = type_ctx.query.get_type(type_def_id);
    let generic_info = type_def
        .generic_info
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_info", "type").to_string())?;

    // Build combined substitution map: type params -> type args, plus monomorphization context
    // This allows a single pass through the type tree instead of two.
    let mut combined_subs: FxHashMap<vole_identity::NameId, TypeId> = type_def
        .type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Merge in function-level substitutions (monomorphization context)
    if let Some(func_subs) = func_ctx.substitutions {
        for (&k, &v) in func_subs {
            combined_subs.entry(k).or_insert(v);
        }
    }

    for (slot, field_name_id) in generic_info.field_names.iter().enumerate() {
        let name = type_ctx.query.last_segment(*field_name_id);
        if name.as_deref() == Some(field_name) {
            let base_type_id = generic_info.field_types[slot];
            // Apply combined substitutions in a single pass (read-only lookup)
            let field_type_id = if !combined_subs.is_empty() {
                arena.expect_substitute(base_type_id, &combined_subs, "field access substitution")
            } else {
                base_type_id
            };
            return Ok((slot, field_type_id));
        }
    }

    Err(CodegenError::not_found(
        "field",
        format!("{} in type", field_name),
    ))
}

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

    // Try class first, then struct
    let (type_def_id, type_args) = arena
        .unwrap_class(resolved_type_id)
        .or_else(|| arena.unwrap_struct(resolved_type_id))
        .ok_or_else(|| {
            CodegenError::type_mismatch("field access", "class or struct", "other type").to_string()
        })?;

    let type_def = type_ctx.query.get_type(type_def_id);
    let generic_info = type_def
        .generic_info
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_info", "type").to_string())?;

    // Build combined substitution map: type params -> type args, plus monomorphization context
    // This allows a single pass through the type tree instead of two.
    let mut combined_subs: FxHashMap<vole_identity::NameId, TypeId> = type_def
        .type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Merge in function-level substitutions (monomorphization context)
    if let Some(func_subs) = cg.substitutions {
        for (&k, &v) in func_subs {
            combined_subs.entry(k).or_insert(v);
        }
    }

    for (slot, field_name_id) in generic_info.field_names.iter().enumerate() {
        let name = type_ctx.query.last_segment(*field_name_id);
        if name.as_deref() == Some(field_name) {
            let base_type_id = generic_info.field_types[slot];
            // Apply combined substitutions in a single pass (read-only lookup)
            let field_type_id = if !combined_subs.is_empty() {
                arena.expect_substitute(base_type_id, &combined_subs, "field access substitution")
            } else {
                base_type_id
            };
            return Ok((slot, field_type_id));
        }
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
            builder.ins().uextend(types::I64, i32_val)
        }
        types::I8 => builder.ins().uextend(types::I64, value.value),
        types::I16 => builder.ins().uextend(types::I64, value.value),
        types::I32 => builder.ins().uextend(types::I64, value.value),
        types::I64 => value.value,
        _ => value.value,
    }
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
    let (type_def_id, _) = arena.unwrap_struct(type_id)?;
    let type_def = entities.get_type(type_def_id);
    let generic_info = type_def.generic_info.as_ref()?;

    let mut total = 0usize;
    for field_type in &generic_info.field_types {
        total += field_flat_slots(*field_type, arena, entities);
    }
    Some(total)
}

/// Compute the number of flat 8-byte slots a single field occupies.
/// Nested struct fields are recursively expanded; all other types use 1 slot.
pub(crate) fn field_flat_slots(
    type_id: TypeId,
    arena: &TypeArena,
    entities: &EntityRegistry,
) -> usize {
    struct_flat_slot_count(type_id, arena, entities).unwrap_or(1)
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
    let (type_def_id, _) = arena.unwrap_struct(type_id)?;
    let type_def = entities.get_type(type_def_id);
    let generic_info = type_def.generic_info.as_ref()?;

    if slot > generic_info.field_types.len() {
        return None;
    }

    let mut offset = 0i32;
    for field_type in generic_info.field_types.iter().take(slot) {
        let slots = field_flat_slots(*field_type, arena, entities);
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
