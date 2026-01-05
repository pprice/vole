// src/codegen/compiler/ops.rs
//
// Binary and compound assignment operation codegen.

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::patterns::compile_expr;
use crate::codegen::structs::{
    convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type,
};
use crate::codegen::types::{CompileCtx, CompiledValue, convert_to_type, type_to_cranelift};
use crate::frontend::{BinaryOp, CompoundAssignExpr, Symbol};
use crate::sema::Type;

pub(crate) fn compile_binary_op(
    builder: &mut FunctionBuilder,
    left: CompiledValue,
    right: CompiledValue,
    op: BinaryOp,
    _ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Determine result type (promote to wider type)
    let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
        types::F64
    } else if left.ty == types::F32 || right.ty == types::F32 {
        types::F32
    } else {
        left.ty
    };

    let left_vole_type = left.vole_type.clone();
    let left_val = convert_to_type(builder, left, result_ty);
    let right_val = convert_to_type(builder, right, result_ty);

    let result = match op {
        BinaryOp::Add => {
            if result_ty == types::F64 {
                builder.ins().fadd(left_val, right_val)
            } else {
                builder.ins().iadd(left_val, right_val)
            }
        }
        BinaryOp::Sub => {
            if result_ty == types::F64 {
                builder.ins().fsub(left_val, right_val)
            } else {
                builder.ins().isub(left_val, right_val)
            }
        }
        BinaryOp::Mul => {
            if result_ty == types::F64 {
                builder.ins().fmul(left_val, right_val)
            } else {
                builder.ins().imul(left_val, right_val)
            }
        }
        BinaryOp::Div => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder.ins().fdiv(left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder.ins().udiv(left_val, right_val)
            } else {
                builder.ins().sdiv(left_val, right_val)
            }
        }
        BinaryOp::Mod => {
            if result_ty == types::F64 || result_ty == types::F32 {
                let div = builder.ins().fdiv(left_val, right_val);
                let floor = builder.ins().floor(div);
                let mul = builder.ins().fmul(floor, right_val);
                builder.ins().fsub(left_val, mul)
            } else if left_vole_type.is_unsigned() {
                builder.ins().urem(left_val, right_val)
            } else {
                builder.ins().srem(left_val, right_val)
            }
        }
        BinaryOp::Eq => {
            if result_ty == types::F64 {
                builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
            } else {
                builder.ins().icmp(IntCC::Equal, left_val, right_val)
            }
        }
        BinaryOp::Ne => {
            if result_ty == types::F64 {
                builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val)
            } else {
                builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
            }
        }
        BinaryOp::Lt => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder.ins().fcmp(FloatCC::LessThan, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, left_val, right_val)
            }
        }
        BinaryOp::Gt => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder
                    .ins()
                    .fcmp(FloatCC::GreaterThan, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, left_val, right_val)
            }
        }
        BinaryOp::Le => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder
                    .ins()
                    .fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThanOrEqual, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
            }
        }
        BinaryOp::Ge => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder
                    .ins()
                    .fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThanOrEqual, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
            }
        }
        BinaryOp::And | BinaryOp::Or => {
            return Err("And/Or should be handled with short-circuit evaluation".to_string());
        }
        BinaryOp::BitAnd => builder.ins().band(left_val, right_val),
        BinaryOp::BitOr => builder.ins().bor(left_val, right_val),
        BinaryOp::BitXor => builder.ins().bxor(left_val, right_val),
        BinaryOp::Shl => builder.ins().ishl(left_val, right_val),
        BinaryOp::Shr => {
            if left_vole_type.is_unsigned() {
                builder.ins().ushr(left_val, right_val)
            } else {
                builder.ins().sshr(left_val, right_val)
            }
        }
    };

    let final_ty = match op {
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
            types::I8
        }
        _ => result_ty,
    };

    let vole_type = match op {
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
            Type::Bool
        }
        _ => left_vole_type,
    };

    Ok(CompiledValue {
        value: result,
        ty: final_ty,
        vole_type,
    })
}

/// Compile compound assignment expression: x += 1, arr[i] -= 2
pub(crate) fn compile_compound_assign(
    builder: &mut FunctionBuilder,
    compound: &CompoundAssignExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    use crate::frontend::AssignTarget;

    match &compound.target {
        AssignTarget::Variable(sym) => {
            // 1. Get current value
            let (var, var_type) = variables
                .get(sym)
                .ok_or_else(|| format!("undefined variable: {}", ctx.interner.resolve(*sym)))?;
            let var = *var;
            let var_type = var_type.clone();
            let current_val = builder.use_var(var);

            let current = CompiledValue {
                value: current_val,
                ty: type_to_cranelift(&var_type, ctx.pointer_type),
                vole_type: var_type.clone(),
            };

            // 2. Compile RHS value
            let rhs = compile_expr(builder, &compound.value, variables, ctx)?;

            // 3. Apply the binary operation
            let binary_op = compound.op.to_binary_op();
            let result = compile_binary_op(builder, current, rhs, binary_op, ctx)?;

            // 4. Store back to variable
            builder.def_var(var, result.value);

            Ok(result)
        }
        AssignTarget::Index { object, index } => {
            // 1. Compile array and index ONCE
            let arr = compile_expr(builder, object, variables, ctx)?;
            let idx = compile_expr(builder, index, variables, ctx)?;

            // Get element type from array type
            let elem_type = match &arr.vole_type {
                Type::Array(elem) => elem.as_ref().clone(),
                _ => Type::I64,
            };

            // 2. Load current element value
            let get_value_id = ctx
                .func_ids
                .get("vole_array_get_value")
                .ok_or_else(|| "vole_array_get_value not found".to_string())?;
            let get_value_ref = ctx.module.declare_func_in_func(*get_value_id, builder.func);
            let call = builder.ins().call(get_value_ref, &[arr.value, idx.value]);
            let raw_value = builder.inst_results(call)[0];

            // Convert to proper type
            let (current_val, current_ty) = match &elem_type {
                Type::F64 => {
                    let fval = builder
                        .ins()
                        .bitcast(types::F64, MemFlags::new(), raw_value);
                    (fval, types::F64)
                }
                Type::Bool => {
                    let bval = builder.ins().ireduce(types::I8, raw_value);
                    (bval, types::I8)
                }
                _ => (raw_value, types::I64),
            };

            let current = CompiledValue {
                value: current_val,
                ty: current_ty,
                vole_type: elem_type.clone(),
            };

            // 3. Compile RHS and apply operation
            let rhs = compile_expr(builder, &compound.value, variables, ctx)?;
            let binary_op = compound.op.to_binary_op();
            let result = compile_binary_op(builder, current, rhs, binary_op, ctx)?;

            // 4. Store back to array
            let array_set_id = ctx
                .func_ids
                .get("vole_array_set")
                .ok_or_else(|| "vole_array_set not found".to_string())?;
            let array_set_ref = ctx.module.declare_func_in_func(*array_set_id, builder.func);

            // Convert result to i64 for storage
            let store_value = match result.ty {
                types::F64 => builder
                    .ins()
                    .bitcast(types::I64, MemFlags::new(), result.value),
                types::I8 => builder.ins().uextend(types::I64, result.value),
                _ => result.value,
            };

            // Compute tag based on element type
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

            Ok(result)
        }
        AssignTarget::Field { object, field, .. } => {
            // 1. Compile object to get the instance pointer
            let obj = compile_expr(builder, object, variables, ctx)?;

            // 2. Get field slot and type from the object's type
            let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, *field, ctx)?;

            // 3. Load current field value
            let get_field_id = ctx
                .func_ids
                .get("vole_instance_get_field")
                .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
            let get_field_ref = ctx.module.declare_func_in_func(*get_field_id, builder.func);
            let slot_val = builder.ins().iconst(types::I32, slot as i64);
            let call = builder.ins().call(get_field_ref, &[obj.value, slot_val]);
            let current_raw = builder.inst_results(call)[0];

            // Convert value based on field type
            let (current_val, cranelift_ty) =
                convert_field_value(builder, current_raw, &field_type);

            let current = CompiledValue {
                value: current_val,
                ty: cranelift_ty,
                vole_type: field_type.clone(),
            };

            // 4. Compile RHS value
            let rhs = compile_expr(builder, &compound.value, variables, ctx)?;

            // 5. Apply the binary operation
            let binary_op = compound.op.to_binary_op();
            let result = compile_binary_op(builder, current, rhs, binary_op, ctx)?;

            // 6. Store back to field
            let set_field_id = ctx
                .func_ids
                .get("vole_instance_set_field")
                .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
            let set_field_ref = ctx.module.declare_func_in_func(*set_field_id, builder.func);

            // Convert result to i64 for storage
            let store_value = convert_to_i64_for_storage(builder, &result);

            builder
                .ins()
                .call(set_field_ref, &[obj.value, slot_val, store_value]);

            Ok(result)
        }
    }
}
