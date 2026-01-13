// src/codegen/structs/helpers.rs

use cranelift::prelude::*;
use std::collections::HashMap;

use crate::codegen::types::CompileCtx;
use crate::codegen::types::CompiledValue;
use crate::errors::CodegenError;
use crate::sema::Type;
use crate::sema::generic::substitute_type;

pub(crate) fn get_field_slot_and_type(
    vole_type: &Type,
    field_name: &str,
    ctx: &CompileCtx,
) -> Result<(usize, Type), String> {
    match vole_type {
        Type::Class(class_type) => {
            let type_def = ctx
                .analyzed
                .entity_registry
                .get_type(class_type.type_def_id);
            let generic_info = type_def
                .generic_info
                .as_ref()
                .ok_or_else(|| CodegenError::not_found("generic_info", "class").to_string())?;

            // Build substitution map if there are type args
            let substitutions: HashMap<_, _> = generic_info
                .type_params
                .iter()
                .zip(class_type.type_args.iter())
                .map(|(param, arg)| (param.name_id, arg.clone()))
                .collect();

            for (slot, field_sym) in generic_info.field_names.iter().enumerate() {
                let name = ctx.interner.resolve(*field_sym);
                if name == field_name {
                    let base_type = &generic_info.field_types[slot];
                    // Apply type substitutions from type args, then from monomorphization context
                    let field_type = if !substitutions.is_empty() {
                        substitute_type(base_type, &substitutions)
                    } else {
                        base_type.clone()
                    };
                    let field_type = if let Some(subs) = ctx.type_substitutions {
                        substitute_type(&field_type, subs)
                    } else {
                        field_type
                    };
                    return Ok((slot, field_type));
                }
            }
            Err(CodegenError::not_found("field", format!("{} in class", field_name)).into())
        }
        Type::Record(record_type) => {
            let type_def = ctx
                .analyzed
                .entity_registry
                .get_type(record_type.type_def_id);
            let generic_info = type_def
                .generic_info
                .as_ref()
                .ok_or_else(|| CodegenError::not_found("generic_info", "record").to_string())?;

            // Build substitution map if there are type args
            let substitutions: HashMap<_, _> = generic_info
                .type_params
                .iter()
                .zip(record_type.type_args.iter())
                .map(|(param, arg)| (param.name_id, arg.clone()))
                .collect();

            for (slot, field_sym) in generic_info.field_names.iter().enumerate() {
                let name = ctx.interner.resolve(*field_sym);
                if name == field_name {
                    let base_type = &generic_info.field_types[slot];
                    // Apply type substitutions from type args, then from monomorphization context
                    let field_type = if !substitutions.is_empty() {
                        substitute_type(base_type, &substitutions)
                    } else {
                        base_type.clone()
                    };
                    let field_type = if let Some(subs) = ctx.type_substitutions {
                        substitute_type(&field_type, subs)
                    } else {
                        field_type
                    };
                    return Ok((slot, field_type));
                }
            }
            Err(CodegenError::not_found("field", format!("{} in record", field_name)).into())
        }
        Type::GenericInstance { def, args } => {
            // Look up the type definition
            let type_def_id = ctx
                .analyzed
                .entity_registry
                .type_by_name(*def)
                .ok_or_else(|| {
                    CodegenError::not_found("generic type", format!("{:?}", def)).to_string()
                })?;
            let type_def = ctx.analyzed.entity_registry.get_type(type_def_id);

            // Get the generic info with field names and types
            let generic_info = type_def.generic_info.as_ref().ok_or_else(|| {
                CodegenError::type_mismatch(
                    "field access",
                    "generic type with fields",
                    format!("{:?}", def),
                )
                .to_string()
            })?;

            // Build substitution map: type param NameId -> concrete type
            let mut substitutions = HashMap::new();
            for (param, arg) in generic_info.type_params.iter().zip(args.iter()) {
                substitutions.insert(param.name_id, arg.clone());
            }

            // Find the field by name
            for (slot, field_sym) in generic_info.field_names.iter().enumerate() {
                let name = ctx.interner.resolve(*field_sym);
                if name == field_name {
                    // Substitute type arguments in field type
                    let field_type = &generic_info.field_types[slot];
                    let substituted = substitute_type(field_type, &substitutions);
                    return Ok((slot, substituted));
                }
            }

            Err(CodegenError::not_found("field", format!("{} in generic", field_name)).into())
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
    vole_type: &Type,
    entity_registry: &crate::sema::entity_registry::EntityRegistry,
) -> Result<crate::identity::NameId, String> {
    match vole_type {
        Type::Class(class_type) => Ok(entity_registry.class_name_id(class_type)),
        Type::Record(record_type) => Ok(entity_registry.record_name_id(record_type)),
        Type::Interface(interface_type) => Ok(entity_registry.name_id(interface_type.type_def_id)),
        Type::GenericInstance { def, .. } => Ok(*def),
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
    field_type: &Type,
) -> (Value, types::Type) {
    match field_type {
        Type::F64 => {
            let fval = builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_value);
            (fval, types::F64)
        }
        Type::F32 => {
            // Truncate to i32 first, then bitcast
            let i32_val = builder.ins().ireduce(types::I32, raw_value);
            let fval = builder.ins().bitcast(types::F32, MemFlags::new(), i32_val);
            (fval, types::F32)
        }
        Type::Bool => {
            let bval = builder.ins().ireduce(types::I8, raw_value);
            (bval, types::I8)
        }
        Type::I8 | Type::U8 => {
            let val = builder.ins().ireduce(types::I8, raw_value);
            (val, types::I8)
        }
        Type::I16 | Type::U16 => {
            let val = builder.ins().ireduce(types::I16, raw_value);
            (val, types::I16)
        }
        Type::I32 | Type::U32 => {
            let val = builder.ins().ireduce(types::I32, raw_value);
            (val, types::I32)
        }
        Type::String | Type::Array(_) | Type::Class(_) | Type::Record(_) => {
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
