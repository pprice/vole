// src/codegen/structs/helpers.rs

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::CodegenError;
use crate::types::{CompiledValue, FunctionCtx, TypeCtx};
use vole_sema::PrimitiveType;
use vole_sema::type_arena::{SemaType as ArenaType, TypeArena, TypeId};

/// Get field slot and type for a field access (new context API).
#[allow(dead_code)]
pub(crate) fn get_field_slot_and_type_id(
    type_id: TypeId,
    field_name: &str,
    type_ctx: &TypeCtx,
    func_ctx: &FunctionCtx,
) -> Result<(usize, TypeId), String> {
    let arena = type_ctx.arena();

    // Try class first, then record
    let (type_def_id, type_args) = arena
        .unwrap_class(type_id)
        .or_else(|| arena.unwrap_record(type_id))
        .ok_or_else(|| {
            CodegenError::type_mismatch("field access", "class or record", "other type").to_string()
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
            // Apply combined substitutions in a single pass
            drop(arena);
            let field_type_id = if !combined_subs.is_empty() {
                type_ctx.update().substitute(base_type_id, &combined_subs)
            } else {
                base_type_id
            };
            return Ok((slot, field_type_id));
        }
    }

    Err(CodegenError::not_found("field", format!("{} in type", field_name)).into())
}

/// Get field slot and type for a field access (Cg API - uses TypeCtx internally).
/// This bridges Cg to the new TypeCtx-based API.
pub(crate) fn get_field_slot_and_type_id_cg(
    type_id: TypeId,
    field_name: &str,
    cg: &crate::context::Cg,
) -> Result<(usize, TypeId), String> {
    let type_ctx = cg.type_ctx();
    let arena = type_ctx.arena();

    // Try class first, then record
    let (type_def_id, type_args) = arena
        .unwrap_class(type_id)
        .or_else(|| arena.unwrap_record(type_id))
        .ok_or_else(|| {
            CodegenError::type_mismatch("field access", "class or record", "other type").to_string()
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
            // Apply combined substitutions in a single pass
            drop(arena);
            let field_type_id = if !combined_subs.is_empty() {
                type_ctx.update().substitute(base_type_id, &combined_subs)
            } else {
                base_type_id
            };
            return Ok((slot, field_type_id));
        }
    }

    Err(CodegenError::not_found("field", format!("{} in type", field_name)).into())
}

/// Get the NameId for a class, record, interface, or generic instance type using TypeId
pub(crate) fn get_type_name_id_from_type_id(
    type_id: TypeId,
    arena: &TypeArena,
    entity_registry: &vole_sema::entity_registry::EntityRegistry,
) -> Result<vole_identity::NameId, String> {
    // Try class
    if let Some((type_def_id, _)) = arena.unwrap_class(type_id) {
        return Ok(entity_registry.name_id(type_def_id));
    }
    // Try record
    if let Some((type_def_id, _)) = arena.unwrap_record(type_id) {
        return Ok(entity_registry.name_id(type_def_id));
    }
    // Try interface
    if let Some((type_def_id, _)) = arena.unwrap_interface(type_id) {
        return Ok(entity_registry.name_id(type_def_id));
    }
    Err(CodegenError::type_mismatch(
        "type name extraction",
        "class, record, interface, or generic instance",
        "other type",
    )
    .into())
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
        | ArenaType::Class { .. }
        | ArenaType::Record { .. } => {
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
