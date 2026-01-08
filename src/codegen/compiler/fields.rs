// src/codegen/compiler/fields.rs
//
// Struct literal and field access codegen.

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::patterns::compile_expr;
use crate::codegen::RuntimeFn;
use crate::codegen::interface_vtable::box_interface_value;
use crate::codegen::stmt::construct_union;
use crate::codegen::structs::{
    convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type,
};
use crate::codegen::types::type_to_cranelift;
use crate::codegen::types::{CompileCtx, CompiledValue, module_name_id};
use crate::errors::CodegenError;
use crate::frontend::{Expr, FieldAccessExpr, OptionalChainExpr, StructLiteralExpr, Symbol};
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
        .func_registry
        .runtime_key(RuntimeFn::InstanceNew)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_instance_new not found".to_string())?;
    let new_func_ref = ctx.module.declare_func_in_func(new_func_id, builder.func);

    let type_id_val = builder.ins().iconst(types::I32, type_id as i64);
    let field_count_val = builder.ins().iconst(types::I32, field_count as i64);
    let runtime_type = builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

    let call = builder
        .ins()
        .call(new_func_ref, &[type_id_val, field_count_val, runtime_type]);
    let instance_ptr = builder.inst_results(call)[0];

    // Initialize each field
    let set_func_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::InstanceSetField)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
    let set_func_ref = ctx.module.declare_func_in_func(set_func_id, builder.func);

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
        let name_id = module_name_id(ctx.analyzed, module_type.module_id, field_name);

        // Look up constant value in module
        if let Some(name_id) = name_id
            && let Some(const_val) = module_type.constants.get(&name_id)
        {
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
                        ctx.func_registry,
                    )
                }
            };
        }

        // Check if it's a function export (which would be accessed via method call, not field access)
        if let Some(name_id) = name_id
            && let Some(export_type) = module_type.exports.get(&name_id)
        {
            // For function types accessed as fields (e.g., storing a reference),
            // we need a function pointer - but this is typically done via method calls
            if matches!(export_type, Type::Function(_)) {
                return Err(CodegenError::unsupported_with_context(
                    "function as field value",
                    format!("use {}() to call the function", field_name),
                )
                .into());
            }

            // Non-constant export that we don't have a value for
            return Err(CodegenError::unsupported_with_context(
                "non-constant module export",
                format!("{} cannot be accessed at compile time", field_name),
            )
            .into());
        }

        let module_path = ctx.analyzed.name_table.module_path(module_type.module_id);
        return Err(CodegenError::not_found(
            "module export",
            format!("{}.{}", module_path, field_name),
        )
        .into());
    }

    // Get slot and type from object's type (for classes/records)
    let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, fa.field, ctx)?;

    let get_func_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::InstanceGetField)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
    let get_func_ref = ctx.module.declare_func_in_func(get_func_id, builder.func);

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

/// Compile optional chaining: obj?.field
/// If obj is nil, returns nil; otherwise returns obj.field wrapped in optional
pub(crate) fn compile_optional_chain(
    builder: &mut FunctionBuilder,
    oc: &OptionalChainExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, &oc.object, variables, ctx)?;

    // The object should be an optional type (union with nil)
    let Type::Union(variants) = &obj.vole_type else {
        return Err(
            CodegenError::type_mismatch("optional chain", "optional type", "non-optional").into(),
        );
    };

    // Find the nil tag
    let nil_tag = variants
        .iter()
        .position(|v| v == &Type::Nil)
        .unwrap_or(usize::MAX);

    // Check if object is nil by reading the tag
    let tag = builder.ins().load(types::I8, MemFlags::new(), obj.value, 0);
    let nil_tag_val = builder.ins().iconst(types::I8, nil_tag as i64);
    let is_nil = builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

    // Create blocks for branching
    let nil_block = builder.create_block();
    let not_nil_block = builder.create_block();
    let merge_block = builder.create_block();

    // Get the inner (non-nil) type for field access
    let inner_type = obj.vole_type.unwrap_optional().unwrap_or(Type::Error);

    // Get the field type from the inner type
    let (slot, field_type) = get_field_slot_and_type(&inner_type, oc.field, ctx)?;

    // Result type is field_type | nil (optional)
    // But if field type is already optional, don't double-wrap
    let result_vole_type = if field_type.is_optional() {
        field_type.clone()
    } else {
        Type::optional(field_type.clone())
    };
    let cranelift_type = type_to_cranelift(&result_vole_type, ctx.pointer_type);
    builder.append_block_param(merge_block, cranelift_type);

    builder
        .ins()
        .brif(is_nil, nil_block, &[], not_nil_block, &[]);

    // Nil block: return nil wrapped in the optional type
    builder.switch_to_block(nil_block);
    builder.seal_block(nil_block);
    let nil_val = CompiledValue {
        value: builder.ins().iconst(types::I8, 0),
        ty: types::I8,
        vole_type: Type::Nil,
    };
    let nil_union = construct_union(builder, nil_val, &result_vole_type, ctx.pointer_type)?;
    builder.ins().jump(merge_block, &[nil_union.value.into()]);

    // Not-nil block: do field access and wrap result in optional
    builder.switch_to_block(not_nil_block);
    builder.seal_block(not_nil_block);

    // Load the actual object from the union payload (offset 8)
    let inner_cranelift_type = type_to_cranelift(&inner_type, ctx.pointer_type);
    let inner_obj = builder
        .ins()
        .load(inner_cranelift_type, MemFlags::new(), obj.value, 8);

    // Get field from the inner object
    let get_func_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::InstanceGetField)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
    let get_func_ref = ctx.module.declare_func_in_func(get_func_id, builder.func);
    let slot_val = builder.ins().iconst(types::I32, slot as i64);
    let call = builder.ins().call(get_func_ref, &[inner_obj, slot_val]);
    let field_raw = builder.inst_results(call)[0];
    let (field_val, field_cranelift_ty) = convert_field_value(builder, field_raw, &field_type);

    // Wrap the field value in an optional (using construct_union)
    // But if field type is already optional, it's already a union - just use it directly
    let field_compiled = CompiledValue {
        value: field_val,
        ty: field_cranelift_ty,
        vole_type: field_type.clone(),
    };
    let final_value = if field_type.is_optional() {
        // Field is already optional, use as-is
        field_compiled
    } else {
        // Wrap non-optional field in optional
        construct_union(builder, field_compiled, &result_vole_type, ctx.pointer_type)?
    };
    builder.ins().jump(merge_block, &[final_value.value.into()]);

    // Merge block
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);

    let result = builder.block_params(merge_block)[0];
    Ok(CompiledValue {
        value: result,
        ty: cranelift_type,
        vole_type: result_vole_type,
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
    let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, field, ctx)?;
    let value = if matches!(field_type, Type::Interface(_)) {
        box_interface_value(builder, ctx, value, &field_type)?
    } else {
        value
    };

    let set_func_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::InstanceSetField)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
    let set_func_ref = ctx.module.declare_func_in_func(set_func_id, builder.func);

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
        .func_registry
        .runtime_key(RuntimeFn::ArraySet)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_array_set not found".to_string())?;
    let array_set_ref = ctx.module.declare_func_in_func(array_set_id, builder.func);

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
