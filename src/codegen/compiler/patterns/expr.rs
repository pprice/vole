// src/codegen/compiler/patterns/expr.rs

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::super::calls::compile_call;
use super::super::fields::{
    compile_field_access, compile_field_assign, compile_index_assign, compile_optional_chain,
    compile_struct_literal,
};
use super::super::methods::{compile_method_call, compile_try_propagate};
use super::super::ops::compile_compound_assign;
use super::super::strings::compile_interpolated_string;
use super::type_check::compile_type_pattern_check;
use crate::codegen::RuntimeFn;
use crate::codegen::calls::compile_string_literal;
use crate::codegen::interface_vtable::box_interface_value;
use crate::codegen::lambda::compile_lambda;
use crate::codegen::stmt::construct_union;
use crate::codegen::types::{
    CompileCtx, CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, FALLIBLE_TAG_OFFSET,
    convert_to_type, fallible_error_tag, resolve_type_expr, type_to_cranelift,
};
use crate::errors::CodegenError;
use crate::frontend::{AssignTarget, BinaryOp, Expr, ExprKind, Pattern, Symbol, UnaryOp};
use crate::sema::Type;

pub(crate) fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::IntLiteral(n) => {
            let val = builder.ins().iconst(types::I64, *n);
            Ok(CompiledValue {
                value: val,
                ty: types::I64,
                vole_type: Type::I64,
            })
        }
        ExprKind::FloatLiteral(n) => {
            let val = builder.ins().f64const(*n);
            Ok(CompiledValue {
                value: val,
                ty: types::F64,
                vole_type: Type::F64,
            })
        }
        ExprKind::BoolLiteral(b) => {
            let val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
            Ok(CompiledValue {
                value: val,
                ty: types::I8,
                vole_type: Type::Bool,
            })
        }
        ExprKind::Identifier(sym) => {
            if let Some((var, vole_type)) = variables.get(sym) {
                let val = builder.use_var(*var);
                // Get the type from the variable declaration
                let ty = builder.func.dfg.value_type(val);

                // Check if this expression has a narrowed type from semantic analysis
                // (e.g., inside `if x is i64 { ... }`, x's type is narrowed from i64|nil to i64)
                if let Some(narrowed_type) = ctx.analyzed.expr_types.get(&expr.id) {
                    // If variable is a union but narrowed type is not, extract the payload
                    if matches!(vole_type, Type::Union(_))
                        && !matches!(narrowed_type, Type::Union(_))
                    {
                        // Union layout: [tag:1][padding:7][payload]
                        // Load the payload at offset 8
                        let payload_ty = type_to_cranelift(narrowed_type, ctx.pointer_type);
                        let payload = builder.ins().load(payload_ty, MemFlags::new(), val, 8);
                        return Ok(CompiledValue {
                            value: payload,
                            ty: payload_ty,
                            vole_type: narrowed_type.clone(),
                        });
                    }
                }

                Ok(CompiledValue {
                    value: val,
                    ty,
                    vole_type: vole_type.clone(),
                })
            } else {
                // Check if this is a global variable
                if let Some(global) = ctx.globals.iter().find(|g| g.name == *sym) {
                    // Compile the global's initializer expression inline
                    // This works for constant expressions; for complex expressions,
                    // a more sophisticated approach would be needed
                    compile_expr(builder, &global.init, variables, ctx)
                } else {
                    Err(CodegenError::not_found("variable", ctx.interner.resolve(*sym)).into())
                }
            }
        }
        ExprKind::Binary(bin) => {
            // Handle short-circuit evaluation for And/Or before evaluating both sides
            match bin.op {
                BinaryOp::And => {
                    // Short-circuit AND: if left is false, return false without evaluating right
                    let left = compile_expr(builder, &bin.left, variables, ctx)?;

                    let then_block = builder.create_block();
                    let else_block = builder.create_block();
                    let merge_block = builder.create_block();
                    builder.append_block_param(merge_block, types::I8);

                    builder
                        .ins()
                        .brif(left.value, then_block, &[], else_block, &[]);

                    // Then block: left was true, evaluate right side
                    builder.switch_to_block(then_block);
                    builder.seal_block(then_block);
                    let right = compile_expr(builder, &bin.right, variables, ctx)?;
                    let right_arg = BlockArg::from(right.value);
                    builder.ins().jump(merge_block, &[right_arg]);

                    // Else block: left was false, short-circuit with false
                    builder.switch_to_block(else_block);
                    builder.seal_block(else_block);
                    let false_val = builder.ins().iconst(types::I8, 0);
                    let false_arg = BlockArg::from(false_val);
                    builder.ins().jump(merge_block, &[false_arg]);

                    // Merge block
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let result = builder.block_params(merge_block)[0];

                    return Ok(CompiledValue {
                        value: result,
                        ty: types::I8,
                        vole_type: Type::Bool,
                    });
                }
                BinaryOp::Or => {
                    // Short-circuit OR: if left is true, return true without evaluating right
                    let left = compile_expr(builder, &bin.left, variables, ctx)?;

                    let then_block = builder.create_block();
                    let else_block = builder.create_block();
                    let merge_block = builder.create_block();
                    builder.append_block_param(merge_block, types::I8);

                    builder
                        .ins()
                        .brif(left.value, then_block, &[], else_block, &[]);

                    // Then block: left was true, short-circuit with true
                    builder.switch_to_block(then_block);
                    builder.seal_block(then_block);
                    let true_val = builder.ins().iconst(types::I8, 1);
                    let true_arg = BlockArg::from(true_val);
                    builder.ins().jump(merge_block, &[true_arg]);

                    // Else block: left was false, evaluate right side
                    builder.switch_to_block(else_block);
                    builder.seal_block(else_block);
                    let right = compile_expr(builder, &bin.right, variables, ctx)?;
                    let right_arg = BlockArg::from(right.value);
                    builder.ins().jump(merge_block, &[right_arg]);

                    // Merge block
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let result = builder.block_params(merge_block)[0];

                    return Ok(CompiledValue {
                        value: result,
                        ty: types::I8,
                        vole_type: Type::Bool,
                    });
                }
                _ => {} // Fall through to regular binary handling
            }

            let left = compile_expr(builder, &bin.left, variables, ctx)?;
            let right = compile_expr(builder, &bin.right, variables, ctx)?;

            // Determine result type (promote to wider type)
            let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
                types::F64
            } else if left.ty == types::F32 || right.ty == types::F32 {
                types::F32
            } else {
                left.ty
            };

            // Save the left operand's vole_type before conversion (for signed/unsigned op selection)
            let left_vole_type = left.vole_type.clone();

            // Convert operands if needed
            let left_val = convert_to_type(builder, left, result_ty);
            let right_val = convert_to_type(builder, right, result_ty);

            let result = match bin.op {
                BinaryOp::Add => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fadd(left_val, right_val)
                    } else {
                        builder.ins().iadd(left_val, right_val)
                    }
                }
                BinaryOp::Sub => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fsub(left_val, right_val)
                    } else {
                        builder.ins().isub(left_val, right_val)
                    }
                }
                BinaryOp::Mul => {
                    if result_ty == types::F64 || result_ty == types::F32 {
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
                        // Floating-point modulo: a - (a/b).floor() * b
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
                    if matches!(left_vole_type, Type::String) {
                        // String comparison
                        if let Some(cmp_id) = ctx
                            .func_registry
                            .runtime_key(RuntimeFn::StringEq)
                            .and_then(|key| ctx.func_registry.func_id(key))
                        {
                            let cmp_ref = ctx.module.declare_func_in_func(cmp_id, builder.func);
                            let call = builder.ins().call(cmp_ref, &[left_val, right_val]);
                            builder.inst_results(call)[0]
                        } else {
                            builder.ins().icmp(IntCC::Equal, left_val, right_val)
                        }
                    } else if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::Equal, left_val, right_val)
                    }
                }
                BinaryOp::Ne => {
                    if matches!(left_vole_type, Type::String) {
                        // String comparison (negate the result of eq)
                        if let Some(cmp_id) = ctx
                            .func_registry
                            .runtime_key(RuntimeFn::StringEq)
                            .and_then(|key| ctx.func_registry.func_id(key))
                        {
                            let cmp_ref = ctx.module.declare_func_in_func(cmp_id, builder.func);
                            let call = builder.ins().call(cmp_ref, &[left_val, right_val]);
                            let eq_result = builder.inst_results(call)[0];
                            // Negate: 1 - eq_result (since bool is 0 or 1)
                            let one = builder.ins().iconst(types::I8, 1);
                            builder.ins().isub(one, eq_result)
                        } else {
                            builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
                        }
                    } else if result_ty == types::F64 || result_ty == types::F32 {
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
                // And/Or are handled above with short-circuit evaluation
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                // Bitwise operators
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

            // Comparison operators return I8 (bool)
            let final_ty = match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => types::I8,
                // And/Or are handled above with early return
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                _ => result_ty,
            };

            // Determine vole_type for result
            let vole_type = match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => Type::Bool,
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                _ => left_vole_type,
            };

            Ok(CompiledValue {
                value: result,
                ty: final_ty,
                vole_type,
            })
        }
        ExprKind::Unary(un) => {
            let operand = compile_expr(builder, &un.operand, variables, ctx)?;
            let result = match un.op {
                UnaryOp::Neg => {
                    if operand.ty == types::F64 {
                        builder.ins().fneg(operand.value)
                    } else {
                        builder.ins().ineg(operand.value)
                    }
                }
                UnaryOp::Not => {
                    // Logical not: 1 - x for boolean
                    let one = builder.ins().iconst(types::I8, 1);
                    builder.ins().isub(one, operand.value)
                }
                UnaryOp::BitNot => builder.ins().bnot(operand.value),
            };
            Ok(CompiledValue {
                value: result,
                ty: operand.ty,
                vole_type: operand.vole_type,
            })
        }
        ExprKind::Assign(assign) => {
            match &assign.target {
                AssignTarget::Variable(sym) => {
                    let mut value = compile_expr(builder, &assign.value, variables, ctx)?;
                    if let Some((var, var_type)) = variables.get(sym) {
                        if matches!(var_type, Type::Interface(_))
                            && !matches!(value.vole_type, Type::Interface(_))
                        {
                            value = box_interface_value(builder, ctx, value, var_type)?;
                        }
                        // If variable is a union and value is not, wrap the value
                        let final_value = if matches!(var_type, Type::Union(_))
                            && !matches!(&value.vole_type, Type::Union(_))
                        {
                            let wrapped = construct_union(
                                builder,
                                value.clone(),
                                var_type,
                                ctx.pointer_type,
                            )?;
                            wrapped.value
                        } else {
                            value.value
                        };
                        builder.def_var(*var, final_value);
                        Ok(value)
                    } else {
                        Err(CodegenError::not_found("variable", ctx.interner.resolve(*sym)).into())
                    }
                }
                AssignTarget::Field { object, field, .. } => {
                    compile_field_assign(builder, object, *field, &assign.value, variables, ctx)
                }
                AssignTarget::Index { object, index } => {
                    compile_index_assign(builder, object, index, &assign.value, variables, ctx)
                }
            }
        }
        ExprKind::CompoundAssign(compound) => {
            compile_compound_assign(builder, compound, variables, ctx)
        }
        ExprKind::Grouping(inner) => compile_expr(builder, inner, variables, ctx),
        ExprKind::StringLiteral(s) => {
            compile_string_literal(builder, s, ctx.pointer_type, ctx.module, ctx.func_registry)
        }
        ExprKind::Call(call) => {
            compile_call(builder, call, expr.span.line, expr.id, variables, ctx)
        }
        ExprKind::InterpolatedString(parts) => {
            compile_interpolated_string(builder, parts, variables, ctx)
        }
        ExprKind::Range(_) => {
            // Range expressions are only supported in for-in context
            Err(CodegenError::unsupported("range expressions outside for-in").into())
        }
        ExprKind::ArrayLiteral(elements) => {
            // Call vole_array_new()
            let array_new_id = ctx
                .func_registry
                .runtime_key(RuntimeFn::ArrayNew)
                .and_then(|key| ctx.func_registry.func_id(key))
                .ok_or_else(|| "vole_array_new not found".to_string())?;
            let array_new_ref = ctx.module.declare_func_in_func(array_new_id, builder.func);

            let call = builder.ins().call(array_new_ref, &[]);
            let arr_ptr = builder.inst_results(call)[0];

            // Push each element
            let array_push_id = ctx
                .func_registry
                .runtime_key(RuntimeFn::ArrayPush)
                .and_then(|key| ctx.func_registry.func_id(key))
                .ok_or_else(|| "vole_array_push not found".to_string())?;
            let array_push_ref = ctx.module.declare_func_in_func(array_push_id, builder.func);

            // Track element type from first element
            let mut elem_type = Type::Unknown;

            for (i, elem) in elements.iter().enumerate() {
                let compiled = compile_expr(builder, elem, variables, ctx)?;

                // Track element type from first element
                if i == 0 {
                    elem_type = compiled.vole_type.clone();
                }

                // Determine tag based on type
                let tag = match &compiled.vole_type {
                    Type::I64 | Type::I32 => 2i64, // TYPE_I64
                    Type::F64 => 3i64,             // TYPE_F64
                    Type::Bool => 4i64,            // TYPE_BOOL
                    Type::String => 1i64,          // TYPE_STRING
                    Type::Array(_) => 5i64,        // TYPE_ARRAY
                    _ => 2i64,                     // default to I64
                };

                let tag_val = builder.ins().iconst(types::I64, tag);

                // Convert value to u64 bits
                let value_bits = if compiled.ty == types::F64 {
                    builder
                        .ins()
                        .bitcast(types::I64, MemFlags::new(), compiled.value)
                } else if compiled.ty == types::I8 {
                    // Bool: zero-extend to i64
                    builder.ins().uextend(types::I64, compiled.value)
                } else {
                    compiled.value
                };

                builder
                    .ins()
                    .call(array_push_ref, &[arr_ptr, tag_val, value_bits]);
            }

            Ok(CompiledValue {
                value: arr_ptr,
                ty: ctx.pointer_type,
                vole_type: Type::Array(Box::new(elem_type)),
            })
        }
        ExprKind::Index(idx) => {
            let arr = compile_expr(builder, &idx.object, variables, ctx)?;
            let index = compile_expr(builder, &idx.index, variables, ctx)?;

            // Get element type from array type
            let elem_type = match &arr.vole_type {
                Type::Array(elem) => elem.as_ref().clone(),
                _ => Type::I64, // Default to I64 if type unknown
            };

            // Call vole_array_get_value(arr, index)
            let get_value_id = ctx
                .func_registry
                .runtime_key(RuntimeFn::ArrayGetValue)
                .and_then(|key| ctx.func_registry.func_id(key))
                .ok_or_else(|| "vole_array_get_value not found".to_string())?;
            let get_value_ref = ctx.module.declare_func_in_func(get_value_id, builder.func);

            let call = builder.ins().call(get_value_ref, &[arr.value, index.value]);
            let value = builder.inst_results(call)[0];

            // Convert value based on element type
            let (result_value, result_ty) = match &elem_type {
                Type::F64 => {
                    let fval = builder.ins().bitcast(types::F64, MemFlags::new(), value);
                    (fval, types::F64)
                }
                Type::Bool => {
                    let bval = builder.ins().ireduce(types::I8, value);
                    (bval, types::I8)
                }
                _ => (value, types::I64), // i64, strings, arrays stay as i64/pointer
            };

            Ok(CompiledValue {
                value: result_value,
                ty: result_ty,
                vole_type: elem_type,
            })
        }

        ExprKind::Match(match_expr) => {
            // Compile the scrutinee (value being matched)
            let scrutinee = compile_expr(builder, &match_expr.scrutinee, variables, ctx)?;

            // Create merge block that collects results
            // Use I64 as the result type since it can hold both integers and pointers
            let merge_block = builder.create_block();
            builder.append_block_param(merge_block, types::I64);

            // Create a trap block for non-exhaustive match (should be unreachable)
            let trap_block = builder.create_block();

            // Create blocks for each arm
            let arm_blocks: Vec<Block> = match_expr
                .arms
                .iter()
                .map(|_| builder.create_block())
                .collect();

            // Jump to first arm
            if !arm_blocks.is_empty() {
                builder.ins().jump(arm_blocks[0], &[]);
            } else {
                // No arms - should not happen after sema, but handle gracefully
                let default_val = builder.ins().iconst(types::I64, 0);
                let default_arg = BlockArg::from(default_val);
                builder.ins().jump(merge_block, &[default_arg]);
            }

            // Track the result type from the first arm body
            let mut result_vole_type = Type::Void;

            // Compile each arm
            for (i, arm) in match_expr.arms.iter().enumerate() {
                let arm_block = arm_blocks[i];
                // For the last arm, if pattern fails, go to trap (should be unreachable)
                let next_block = arm_blocks.get(i + 1).copied().unwrap_or(trap_block);

                builder.switch_to_block(arm_block);

                // Create a new variables scope for this arm
                let mut arm_variables = variables.clone();

                // Check pattern
                let pattern_matches = match &arm.pattern {
                    Pattern::Wildcard(_) => {
                        // Always matches
                        None
                    }
                    Pattern::Identifier { name, .. } => {
                        // Check if this identifier is a type name (class/record)
                        if let Some(type_meta) = ctx.type_metadata.get(name) {
                            // Type pattern - compare against union variant tag
                            compile_type_pattern_check(builder, &scrutinee, &type_meta.vole_type)
                        } else {
                            // Bind the scrutinee value to the identifier
                            let var = builder.declare_var(scrutinee.ty);
                            builder.def_var(var, scrutinee.value);
                            arm_variables.insert(*name, (var, scrutinee.vole_type.clone()));
                            None // Always matches
                        }
                    }
                    Pattern::Type { type_expr, .. } => {
                        let pattern_type = resolve_type_expr(type_expr, ctx);
                        compile_type_pattern_check(builder, &scrutinee, &pattern_type)
                    }
                    Pattern::Literal(lit_expr) => {
                        // Compile literal and compare
                        let lit_val = compile_expr(builder, lit_expr, &mut arm_variables, ctx)?;
                        let cmp = match scrutinee.ty {
                            types::I64 | types::I32 | types::I8 => {
                                builder
                                    .ins()
                                    .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                            }
                            types::F64 => {
                                builder
                                    .ins()
                                    .fcmp(FloatCC::Equal, scrutinee.value, lit_val.value)
                            }
                            _ => {
                                // For strings, need to call comparison function
                                if let Some(cmp_id) = ctx
                                    .func_registry
                                    .runtime_key(RuntimeFn::StringEq)
                                    .and_then(|key| ctx.func_registry.func_id(key))
                                {
                                    let cmp_ref =
                                        ctx.module.declare_func_in_func(cmp_id, builder.func);
                                    let call = builder
                                        .ins()
                                        .call(cmp_ref, &[scrutinee.value, lit_val.value]);
                                    builder.inst_results(call)[0]
                                } else {
                                    builder
                                        .ins()
                                        .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                                }
                            }
                        };
                        Some(cmp)
                    }
                    Pattern::Val { name, .. } => {
                        // Val pattern - compare against existing variable's value
                        let (var, var_type) = arm_variables
                            .get(name)
                            .ok_or_else(|| "undefined variable in val pattern".to_string())?
                            .clone();
                        let var_val = builder.use_var(var);

                        let cmp = match var_type {
                            Type::F64 => {
                                builder.ins().fcmp(FloatCC::Equal, scrutinee.value, var_val)
                            }
                            Type::String => {
                                if let Some(cmp_id) = ctx
                                    .func_registry
                                    .runtime_key(RuntimeFn::StringEq)
                                    .and_then(|key| ctx.func_registry.func_id(key))
                                {
                                    let cmp_ref =
                                        ctx.module.declare_func_in_func(cmp_id, builder.func);
                                    let call =
                                        builder.ins().call(cmp_ref, &[scrutinee.value, var_val]);
                                    builder.inst_results(call)[0]
                                } else {
                                    builder.ins().icmp(IntCC::Equal, scrutinee.value, var_val)
                                }
                            }
                            _ => builder.ins().icmp(IntCC::Equal, scrutinee.value, var_val),
                        };
                        Some(cmp)
                    }
                    Pattern::Success { inner, .. } => {
                        // Check if tag == FALLIBLE_SUCCESS_TAG (0)
                        let tag = builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            scrutinee.value,
                            FALLIBLE_TAG_OFFSET,
                        );
                        let is_success =
                            builder
                                .ins()
                                .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

                        // If there's an inner pattern, extract payload and bind it
                        if let Some(inner_pat) = inner
                            && let Type::Fallible(ft) = &scrutinee.vole_type
                        {
                            let success_type = &*ft.success_type;
                            let payload_ty = type_to_cranelift(success_type, ctx.pointer_type);
                            let payload = builder.ins().load(
                                payload_ty,
                                MemFlags::new(),
                                scrutinee.value,
                                FALLIBLE_PAYLOAD_OFFSET,
                            );

                            // Handle inner pattern (usually an identifier binding)
                            if let Pattern::Identifier { name, .. } = inner_pat.as_ref() {
                                let var = builder.declare_var(payload_ty);
                                builder.def_var(var, payload);
                                arm_variables.insert(*name, (var, success_type.clone()));
                            }
                        }
                        Some(is_success)
                    }
                    Pattern::Error { inner, .. } => {
                        // Check if tag != FALLIBLE_SUCCESS_TAG (i.e., it's an error)
                        let tag = builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            scrutinee.value,
                            FALLIBLE_TAG_OFFSET,
                        );

                        if let Some(inner_pat) = inner {
                            match inner_pat.as_ref() {
                                Pattern::Identifier { name, .. } => {
                                    // Check if this is an error type name
                                    if let Some(_error_info) = ctx.analyzed.error_types.get(name) {
                                        // Specific error type: error DivByZero => ...
                                        if let Type::Fallible(ft) = &scrutinee.vole_type {
                                            let error_tag = fallible_error_tag(ft, *name);
                                            if let Some(error_tag) = error_tag {
                                                let is_this_error = builder.ins().icmp_imm(
                                                    IntCC::Equal,
                                                    tag,
                                                    error_tag,
                                                );
                                                Some(is_this_error)
                                            } else {
                                                // Error type not found in fallible - will never match
                                                let never_match =
                                                    builder.ins().iconst(types::I8, 0);
                                                Some(never_match)
                                            }
                                        } else {
                                            let never_match = builder.ins().iconst(types::I8, 0);
                                            Some(never_match)
                                        }
                                    } else {
                                        // Catch-all error binding: error e => ...
                                        let is_error = builder.ins().icmp_imm(
                                            IntCC::NotEqual,
                                            tag,
                                            FALLIBLE_SUCCESS_TAG,
                                        );

                                        // Extract error and bind
                                        if let Type::Fallible(ft) = &scrutinee.vole_type {
                                            let error_type = &*ft.error_type;
                                            let payload_ty =
                                                type_to_cranelift(error_type, ctx.pointer_type);
                                            let payload = builder.ins().load(
                                                payload_ty,
                                                MemFlags::new(),
                                                scrutinee.value,
                                                FALLIBLE_PAYLOAD_OFFSET,
                                            );
                                            let var = builder.declare_var(payload_ty);
                                            builder.def_var(var, payload);
                                            arm_variables.insert(*name, (var, error_type.clone()));
                                        }
                                        Some(is_error)
                                    }
                                }
                                _ => {
                                    // Catch-all for other patterns (like wildcard)
                                    let is_error = builder.ins().icmp_imm(
                                        IntCC::NotEqual,
                                        tag,
                                        FALLIBLE_SUCCESS_TAG,
                                    );
                                    Some(is_error)
                                }
                            }
                        } else {
                            // Bare error pattern: error => ...
                            let is_error =
                                builder
                                    .ins()
                                    .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                            Some(is_error)
                        }
                    }
                };

                // Check guard if present
                let guard_result = if let Some(guard) = &arm.guard {
                    let guard_val = compile_expr(builder, guard, &mut arm_variables, ctx)?;
                    // Guard must be bool (i8)
                    Some(guard_val.value)
                } else {
                    None
                };

                // Combine pattern match and guard
                let should_execute = match (pattern_matches, guard_result) {
                    (None, None) => None, // Always execute (wildcard/identifier, no guard)
                    (Some(p), None) => Some(p),
                    (None, Some(g)) => Some(g),
                    (Some(p), Some(g)) => {
                        // Both must be true: p AND g
                        // icmp returns i8 (bool), guard is also i8
                        Some(builder.ins().band(p, g))
                    }
                };

                // Create body block and skip block
                let body_block = builder.create_block();

                if let Some(cond) = should_execute {
                    // Conditional: branch to body if true, next arm if false
                    let cond_i32 = builder.ins().uextend(types::I32, cond);
                    builder
                        .ins()
                        .brif(cond_i32, body_block, &[], next_block, &[]);
                } else {
                    // Unconditional: always go to body
                    builder.ins().jump(body_block, &[]);
                }

                builder.seal_block(arm_block);

                // Compile body
                builder.switch_to_block(body_block);
                let body_val = compile_expr(builder, &arm.body, &mut arm_variables, ctx)?;

                // Track result type from first arm
                if i == 0 {
                    result_vole_type = body_val.vole_type.clone();
                }

                // Convert body value to I64 if needed (merge block uses I64)
                let result_val = if body_val.ty != types::I64 {
                    match body_val.ty {
                        types::I8 => builder.ins().sextend(types::I64, body_val.value),
                        types::I32 => builder.ins().sextend(types::I64, body_val.value),
                        _ => body_val.value, // Pointers are already I64
                    }
                } else {
                    body_val.value
                };

                let result_arg = BlockArg::from(result_val);
                builder.ins().jump(merge_block, &[result_arg]);
                builder.seal_block(body_block);
            }

            // Note: arm_blocks are sealed inside the loop after their predecessors are known

            // Fill in trap block (should be unreachable if match is exhaustive)
            builder.switch_to_block(trap_block);
            builder.seal_block(trap_block);
            builder.ins().trap(TrapCode::unwrap_user(1));

            // Switch to merge block and get result
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let result = builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: result_vole_type,
            })
        }

        ExprKind::Nil => {
            // Nil has no runtime value - return a zero constant
            // The actual type will be determined by context (union wrapping)
            let zero = builder.ins().iconst(types::I8, 0);
            Ok(CompiledValue {
                value: zero,
                ty: types::I8,
                vole_type: Type::Nil,
            })
        }

        ExprKind::Done => {
            // Done has no runtime value - return a zero constant
            // Like Nil, the actual type will be determined by context (union wrapping)
            let zero = builder.ins().iconst(types::I8, 0);
            Ok(CompiledValue {
                value: zero,
                ty: types::I8,
                vole_type: Type::Done,
            })
        }

        ExprKind::Is(is_expr) => {
            let value = compile_expr(builder, &is_expr.value, variables, ctx)?;
            let tested_type = resolve_type_expr(&is_expr.type_expr, ctx);

            // If value is a union, check the tag
            if let Type::Union(variants) = &value.vole_type {
                let expected_tag = variants
                    .iter()
                    .position(|v| v == &tested_type)
                    .unwrap_or(usize::MAX);

                // Load tag from union (at offset 0)
                let tag = builder
                    .ins()
                    .load(types::I8, MemFlags::new(), value.value, 0);
                let expected = builder.ins().iconst(types::I8, expected_tag as i64);
                let result = builder.ins().icmp(IntCC::Equal, tag, expected);

                Ok(CompiledValue {
                    value: result,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            } else {
                // Not a union, always true if types match, false otherwise
                let result = if value.vole_type == tested_type {
                    1i64
                } else {
                    0i64
                };
                let result_val = builder.ins().iconst(types::I8, result);
                Ok(CompiledValue {
                    value: result_val,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            }
        }

        ExprKind::NullCoalesce(nc) => {
            let value = compile_expr(builder, &nc.value, variables, ctx)?;

            // Get nil tag for this union
            let Type::Union(variants) = &value.vole_type else {
                return Err(CodegenError::type_mismatch(
                    "null coalesce",
                    "optional/union type",
                    "non-union",
                )
                .into());
            };
            let nil_tag = variants
                .iter()
                .position(|v| v == &Type::Nil)
                .unwrap_or(usize::MAX);

            // Load tag
            let tag = builder
                .ins()
                .load(types::I8, MemFlags::new(), value.value, 0);
            let nil_tag_val = builder.ins().iconst(types::I8, nil_tag as i64);
            let is_nil = builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

            // Create blocks
            let nil_block = builder.create_block();
            let not_nil_block = builder.create_block();
            let merge_block = builder.create_block();

            // Determine result type (unwrapped)
            let result_vole_type = value.vole_type.unwrap_optional().unwrap_or(Type::Error);
            let cranelift_type = type_to_cranelift(&result_vole_type, ctx.pointer_type);
            builder.append_block_param(merge_block, cranelift_type);

            builder
                .ins()
                .brif(is_nil, nil_block, &[], not_nil_block, &[]);

            // Nil block: evaluate default
            builder.switch_to_block(nil_block);
            builder.seal_block(nil_block);
            let default_val = compile_expr(builder, &nc.default, variables, ctx)?;
            // Coerce default value to the expected result type if needed
            let default_coerced = if default_val.ty != cranelift_type {
                if default_val.ty.is_int() && cranelift_type.is_int() {
                    if cranelift_type.bytes() < default_val.ty.bytes() {
                        builder.ins().ireduce(cranelift_type, default_val.value)
                    } else {
                        builder.ins().sextend(cranelift_type, default_val.value)
                    }
                } else {
                    default_val.value
                }
            } else {
                default_val.value
            };
            let default_arg = BlockArg::from(default_coerced);
            builder.ins().jump(merge_block, &[default_arg]);

            // Not nil block: extract payload
            builder.switch_to_block(not_nil_block);
            builder.seal_block(not_nil_block);
            let payload = builder
                .ins()
                .load(cranelift_type, MemFlags::new(), value.value, 8);
            let payload_arg = BlockArg::from(payload);
            builder.ins().jump(merge_block, &[payload_arg]);

            // Merge
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let result = builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: cranelift_type,
                vole_type: result_vole_type,
            })
        }

        ExprKind::Lambda(lambda) => compile_lambda(builder, lambda, variables, ctx),

        ExprKind::TypeLiteral(_) => {
            // Type values are compile-time only and have no runtime representation.
            // If we reach here, the semantic analyzer should have caught this.
            Err(CodegenError::unsupported("type expressions as runtime values").into())
        }

        ExprKind::StructLiteral(sl) => compile_struct_literal(builder, sl, variables, ctx),

        ExprKind::FieldAccess(fa) => compile_field_access(builder, fa, variables, ctx),

        ExprKind::OptionalChain(oc) => compile_optional_chain(builder, oc, variables, ctx),

        ExprKind::MethodCall(mc) => compile_method_call(builder, mc, expr.id, variables, ctx),

        ExprKind::Try(inner) => compile_try_propagate(builder, inner, variables, ctx),

        ExprKind::Import(_) => {
            // Import expressions produce a compile-time module value
            // At runtime this is just a placeholder - actual function calls
            // go through the method resolution mechanism
            // We need to retrieve the actual Module type from semantic analysis
            let vole_type = ctx
                .analyzed
                .expr_types
                .get(&expr.id)
                .cloned()
                .unwrap_or(Type::Unknown);
            Ok(CompiledValue {
                value: builder.ins().iconst(types::I64, 0),
                ty: types::I64,
                vole_type,
            })
        }
        ExprKind::Yield(_) => {
            // Yield should be caught in semantic analysis
            Err(CodegenError::unsupported("yield expression outside generator context").into())
        }
    }
}
