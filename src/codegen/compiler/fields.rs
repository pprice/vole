// src/codegen/compiler/fields.rs
//
// Struct literal and field access codegen.

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::patterns::compile_expr;
use crate::codegen::structs::{
    convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type,
};
use crate::codegen::types::{CompileCtx, CompiledValue};
use crate::frontend::{Expr, FieldAccessExpr, StructLiteralExpr, Symbol};
use crate::sema::Type;
use crate::sema::types::ConstantValue;

pub(crate) fn compile_struct_literal(
    builder: &mut FunctionBuilder,
    sl: &StructLiteralExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Look up class or record metadata
    let metadata = ctx
        .type_metadata
        .get(&sl.name)
        .ok_or_else(|| format!("Unknown type: {}", ctx.interner.resolve(sl.name)))?;

    let type_id = metadata.type_id;
    let field_count = metadata.field_slots.len() as u32;
    let vole_type = metadata.vole_type.clone();
    let field_slots = metadata.field_slots.clone();

    // Call vole_instance_new(type_id, field_count, TYPE_INSTANCE)
    let new_func_id = ctx
        .func_ids
        .get("vole_instance_new")
        .ok_or_else(|| "vole_instance_new not found".to_string())?;
    let new_func_ref = ctx.module.declare_func_in_func(*new_func_id, builder.func);

    let type_id_val = builder.ins().iconst(types::I32, type_id as i64);
    let field_count_val = builder.ins().iconst(types::I32, field_count as i64);
    let runtime_type = builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

    let call = builder
        .ins()
        .call(new_func_ref, &[type_id_val, field_count_val, runtime_type]);
    let instance_ptr = builder.inst_results(call)[0];

    // Initialize each field
    let set_func_id = ctx
        .func_ids
        .get("vole_instance_set_field")
        .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
    let set_func_ref = ctx.module.declare_func_in_func(*set_func_id, builder.func);

    for init in &sl.fields {
        let slot = *field_slots.get(&init.name).ok_or_else(|| {
            format!(
                "Unknown field: {} in type {}",
                ctx.interner.resolve(init.name),
                ctx.interner.resolve(sl.name)
            )
        })?;

        let value = compile_expr(builder, &init.value, variables, ctx)?;
        let slot_val = builder.ins().iconst(types::I32, slot as i64);

        // Convert value to i64 for storage
        let store_value = convert_to_i64_for_storage(builder, &value);

        builder
            .ins()
            .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
    }

    Ok(CompiledValue {
        value: instance_ptr,
        ty: ctx.pointer_type,
        vole_type,
    })
}

/// Compile field access: point.x or module.constant
pub(crate) fn compile_field_access(
    builder: &mut FunctionBuilder,
    fa: &FieldAccessExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, &fa.object, variables, ctx)?;

    // Handle module field access for constants (e.g., math.PI)
    if let Type::Module(ref module_type) = obj.vole_type {
        let field_name = ctx.interner.resolve(fa.field);

        // Look up constant value in module
        if let Some(const_val) = module_type.constants.get(field_name) {
            return match const_val {
                ConstantValue::F64(v) => {
                    let val = builder.ins().f64const(*v);
                    Ok(CompiledValue {
                        value: val,
                        ty: types::F64,
                        vole_type: Type::F64,
                    })
                }
                ConstantValue::I64(v) => {
                    let val = builder.ins().iconst(types::I64, *v);
                    Ok(CompiledValue {
                        value: val,
                        ty: types::I64,
                        vole_type: Type::I64,
                    })
                }
                ConstantValue::Bool(v) => {
                    let val = builder.ins().iconst(types::I8, if *v { 1 } else { 0 });
                    Ok(CompiledValue {
                        value: val,
                        ty: types::I8,
                        vole_type: Type::Bool,
                    })
                }
                ConstantValue::String(s) => {
                    // Create string literal
                    crate::codegen::calls::compile_string_literal(
                        builder,
                        s,
                        ctx.pointer_type,
                        ctx.module,
                        ctx.func_ids,
                    )
                }
            };
        }

        // Check if it's a function export (which would be accessed via method call, not field access)
        if let Some(export_type) = module_type.exports.get(field_name) {
            // For function types accessed as fields (e.g., storing a reference),
            // we need a function pointer - but this is typically done via method calls
            if matches!(export_type, Type::Function(_)) {
                return Err(format!(
                    "Module function {} should be called, not accessed as a field. Use {}() instead.",
                    field_name, field_name
                ));
            }

            // Non-constant export that we don't have a value for
            return Err(format!(
                "Module export {} is not a constant literal and cannot be accessed at compile time",
                field_name
            ));
        }

        return Err(format!(
            "Module {} has no export named {}",
            module_type.path, field_name
        ));
    }

    // Get slot and type from object's type (for classes/records)
    let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, fa.field, ctx)?;

    let get_func_id = ctx
        .func_ids
        .get("vole_instance_get_field")
        .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
    let get_func_ref = ctx.module.declare_func_in_func(*get_func_id, builder.func);

    let slot_val = builder.ins().iconst(types::I32, slot as i64);
    let call = builder.ins().call(get_func_ref, &[obj.value, slot_val]);
    let result_raw = builder.inst_results(call)[0];

    // Convert the raw i64 value to the appropriate type
    let (result_val, cranelift_ty) = convert_field_value(builder, result_raw, &field_type);

    Ok(CompiledValue {
        value: result_val,
        ty: cranelift_ty,
        vole_type: field_type,
    })
}

/// Compile field assignment: obj.field = value
pub(crate) fn compile_field_assign(
    builder: &mut FunctionBuilder,
    object: &Expr,
    field: Symbol,
    value_expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, object, variables, ctx)?;
    let value = compile_expr(builder, value_expr, variables, ctx)?;

    // Get slot from object's type
    let (slot, _field_type) = get_field_slot_and_type(&obj.vole_type, field, ctx)?;

    let set_func_id = ctx
        .func_ids
        .get("vole_instance_set_field")
        .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
    let set_func_ref = ctx.module.declare_func_in_func(*set_func_id, builder.func);

    let slot_val = builder.ins().iconst(types::I32, slot as i64);

    // Convert value to i64 for storage
    let store_value = convert_to_i64_for_storage(builder, &value);

    builder
        .ins()
        .call(set_func_ref, &[obj.value, slot_val, store_value]);

    Ok(value)
}

/// Compile index assignment: arr[i] = value
pub(crate) fn compile_index_assign(
    builder: &mut FunctionBuilder,
    object: &Expr,
    index: &Expr,
    value_expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let arr = compile_expr(builder, object, variables, ctx)?;
    let idx = compile_expr(builder, index, variables, ctx)?;
    let value = compile_expr(builder, value_expr, variables, ctx)?;

    // Get element type from array type
    let elem_type = match &arr.vole_type {
        Type::Array(elem) => elem.as_ref().clone(),
        _ => Type::I64,
    };

    // Call vole_array_set(arr, index, tag, value)
    let array_set_id = ctx
        .func_ids
        .get("vole_array_set")
        .ok_or_else(|| "vole_array_set not found".to_string())?;
    let array_set_ref = ctx.module.declare_func_in_func(*array_set_id, builder.func);

    // Convert value to i64 for storage
    let store_value = convert_to_i64_for_storage(builder, &value);

    // Determine tag based on type
    let tag = match &elem_type {
        Type::I64 | Type::I32 => 2i64, // TYPE_I64
        Type::F64 => 3i64,             // TYPE_F64
        Type::Bool => 4i64,            // TYPE_BOOL
        Type::String => 1i64,          // TYPE_STRING
        Type::Array(_) => 5i64,        // TYPE_ARRAY
        _ => 2i64,                     // default to I64
    };
    let tag_val = builder.ins().iconst(types::I64, tag);

    builder
        .ins()
        .call(array_set_ref, &[arr.value, idx.value, tag_val, store_value]);

    Ok(value)
}
