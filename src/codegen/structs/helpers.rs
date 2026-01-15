// src/codegen/structs/helpers.rs

use cranelift::prelude::*;

use crate::codegen::types::CompileCtx;
use crate::codegen::types::CompiledValue;
use crate::errors::CodegenError;
use crate::sema::generic::substitute_type;
use crate::sema::types::NominalType;
use crate::sema::{LegacyType, PrimitiveType};

pub(crate) fn get_field_slot_and_type(
    vole_type: &LegacyType,
    field_name: &str,
    ctx: &CompileCtx,
) -> Result<(usize, LegacyType), String> {
    match vole_type {
        LegacyType::Nominal(NominalType::Class(class_type)) => {
            let type_def = ctx
                .analyzed
                .entity_registry
                .get_type(class_type.type_def_id);
            let generic_info = type_def
                .generic_info
                .as_ref()
                .ok_or_else(|| CodegenError::not_found("generic_info", "class").to_string())?;

            // Build substitution map if there are type args
            let substitutions = ctx
                .analyzed
                .entity_registry
                .substitution_map(class_type.type_def_id, &class_type.type_args);

            for (slot, field_name_id) in generic_info.field_names.iter().enumerate() {
                let name = ctx.analyzed.name_table.last_segment_str(*field_name_id);
                if name.as_deref() == Some(field_name) {
                    let base_type = &generic_info.field_types[slot];
                    // Apply type substitutions from type args, then from monomorphization context
                    let field_type = if !substitutions.is_empty() {
                        substitute_type(base_type, &substitutions)
                    } else {
                        base_type.clone()
                    };
                    let field_type = ctx.substitute_type(&field_type);
                    return Ok((slot, field_type));
                }
            }
            Err(CodegenError::not_found("field", format!("{} in class", field_name)).into())
        }
        LegacyType::Nominal(NominalType::Record(record_type)) => {
            let type_def = ctx
                .analyzed
                .entity_registry
                .get_type(record_type.type_def_id);
            let generic_info = type_def
                .generic_info
                .as_ref()
                .ok_or_else(|| CodegenError::not_found("generic_info", "record").to_string())?;

            // Build substitution map if there are type args
            let substitutions = ctx
                .analyzed
                .entity_registry
                .substitution_map(record_type.type_def_id, &record_type.type_args);

            for (slot, field_name_id) in generic_info.field_names.iter().enumerate() {
                let name = ctx.analyzed.name_table.last_segment_str(*field_name_id);
                if name.as_deref() == Some(field_name) {
                    let base_type = &generic_info.field_types[slot];
                    // Apply type substitutions from type args, then from monomorphization context
                    let field_type = if !substitutions.is_empty() {
                        substitute_type(base_type, &substitutions)
                    } else {
                        base_type.clone()
                    };
                    let field_type = ctx.substitute_type(&field_type);
                    return Ok((slot, field_type));
                }
            }
            Err(CodegenError::not_found("field", format!("{} in record", field_name)).into())
        }
        _ => Err(CodegenError::type_mismatch(
            "field access",
            "class or record",
            format!("{:?}", vole_type),
        )
        .into()),
    }
}

/// Get the NameId for a class, record, interface, or generic instance type
pub(crate) fn get_type_name_id(
    vole_type: &LegacyType,
    entity_registry: &crate::sema::entity_registry::EntityRegistry,
) -> Result<crate::identity::NameId, String> {
    match vole_type {
        LegacyType::Nominal(NominalType::Class(class_type)) => {
            Ok(entity_registry.class_name_id(class_type))
        }
        LegacyType::Nominal(NominalType::Record(record_type)) => {
            Ok(entity_registry.record_name_id(record_type))
        }
        LegacyType::Nominal(NominalType::Interface(interface_type)) => {
            Ok(entity_registry.name_id(interface_type.type_def_id))
        }
        _ => Err(CodegenError::type_mismatch(
            "type name extraction",
            "class, record, interface, or generic instance",
            format!("{:?}", vole_type),
        )
        .into()),
    }
}

pub(crate) fn convert_field_value(
    builder: &mut FunctionBuilder,
    raw_value: Value,
    field_type: &LegacyType,
) -> (Value, Type) {
    match field_type {
        LegacyType::Primitive(PrimitiveType::F64) => {
            let fval = builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_value);
            (fval, types::F64)
        }
        LegacyType::Primitive(PrimitiveType::F32) => {
            // Truncate to i32 first, then bitcast
            let i32_val = builder.ins().ireduce(types::I32, raw_value);
            let fval = builder.ins().bitcast(types::F32, MemFlags::new(), i32_val);
            (fval, types::F32)
        }
        LegacyType::Primitive(PrimitiveType::Bool) => {
            let bval = builder.ins().ireduce(types::I8, raw_value);
            (bval, types::I8)
        }
        LegacyType::Primitive(PrimitiveType::I8) | LegacyType::Primitive(PrimitiveType::U8) => {
            let val = builder.ins().ireduce(types::I8, raw_value);
            (val, types::I8)
        }
        LegacyType::Primitive(PrimitiveType::I16) | LegacyType::Primitive(PrimitiveType::U16) => {
            let val = builder.ins().ireduce(types::I16, raw_value);
            (val, types::I16)
        }
        LegacyType::Primitive(PrimitiveType::I32) | LegacyType::Primitive(PrimitiveType::U32) => {
            let val = builder.ins().ireduce(types::I32, raw_value);
            (val, types::I32)
        }
        LegacyType::Primitive(PrimitiveType::String)
        | LegacyType::Array(_)
        | LegacyType::Nominal(NominalType::Class(_))
        | LegacyType::Nominal(NominalType::Record(_)) => {
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
