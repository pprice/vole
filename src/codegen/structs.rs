// src/codegen/structs.rs
//
// Struct/class/record operations for code generation.
// This module contains helper functions for field access, method lookups, and value conversion.

use cranelift::prelude::*;

use super::types::{CompileCtx, CompiledValue};
use crate::frontend::Symbol;
use crate::sema::Type;

/// Get field slot and type from a class/record type
pub(crate) fn get_field_slot_and_type(
    vole_type: &Type,
    field: Symbol,
    ctx: &CompileCtx,
) -> Result<(usize, Type), String> {
    match vole_type {
        Type::Class(class_type) => {
            for sf in &class_type.fields {
                if sf.name == field {
                    return Ok((sf.slot, sf.ty.clone()));
                }
            }
            Err(format!(
                "Field {} not found in class",
                ctx.interner.resolve(field)
            ))
        }
        Type::Record(record_type) => {
            for sf in &record_type.fields {
                if sf.name == field {
                    return Ok((sf.slot, sf.ty.clone()));
                }
            }
            Err(format!(
                "Field {} not found in record",
                ctx.interner.resolve(field)
            ))
        }
        _ => Err(format!(
            "Cannot access field {} on non-class/record type {:?}",
            ctx.interner.resolve(field),
            vole_type
        )),
    }
}

/// Get the type name symbol from a class/record type
pub(crate) fn get_type_name_symbol(vole_type: &Type) -> Result<Symbol, String> {
    match vole_type {
        Type::Class(class_type) => Ok(class_type.name),
        Type::Record(record_type) => Ok(record_type.name),
        _ => Err(format!(
            "Cannot get type name from non-class/record type {:?}",
            vole_type
        )),
    }
}

/// Get the return type of a method
pub(crate) fn get_method_return_type(
    vole_type: &Type,
    method: Symbol,
    ctx: &CompileCtx,
) -> Result<Type, String> {
    let type_name = get_type_name_symbol(vole_type)?;
    let metadata = ctx
        .type_metadata
        .get(&type_name)
        .ok_or_else(|| "Type metadata not found".to_string())?;

    // Look up the method return type from metadata
    metadata
        .method_return_types
        .get(&method)
        .cloned()
        .ok_or_else(|| format!("Method {} not found in type", ctx.interner.resolve(method)))
}

/// Convert a raw i64 field value to the appropriate Cranelift type
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

/// Convert a CompiledValue to i64 for storage in instance fields
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
