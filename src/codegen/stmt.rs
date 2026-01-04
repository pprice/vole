// src/codegen/stmt.rs
//
// Statement and block compilation.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::frontend::{self, ExprKind, Stmt, Symbol};
use crate::sema::Type;

// Import compile_expr from compiler (it will be moved to expr.rs later)
use super::compiler::compile_expr;
use super::lambda::CaptureBinding;
use super::types::{CompileCtx, CompiledValue, resolve_type_expr, type_size, type_to_cranelift};
use super::ControlFlowCtx;

pub(super) fn construct_union(
    builder: &mut FunctionBuilder,
    value: CompiledValue,
    union_type: &Type,
    pointer_type: types::Type,
) -> Result<CompiledValue, String> {
    use cranelift::prelude::StackSlotData;
    use cranelift::prelude::StackSlotKind;

    let Type::Union(variants) = union_type else {
        return Err("Expected union type".to_string());
    };

    // Find the tag for this value's type (with coercion support for integer literals)
    // First try exact match
    let (tag, actual_value, actual_type) =
        if let Some(pos) = variants.iter().position(|v| v == &value.vole_type) {
            (pos, value.value, value.vole_type.clone())
        } else {
            // Try to find a compatible integer type (for literal coercion)
            // When assigning I64 literal to i32?, we need to narrow to I32
            let compatible = variants.iter().enumerate().find(|(_, v)| {
                // Check if value type can narrow to this variant
                value.vole_type.is_integer() && v.is_integer() && value.vole_type.can_widen_to(v)
                    || v.is_integer() && value.vole_type.is_integer()
            });

            match compatible {
                Some((pos, variant_type)) => {
                    // Narrow the integer value to the variant type
                    let target_ty = type_to_cranelift(variant_type, pointer_type);
                    let narrowed = if target_ty.bytes() < value.ty.bytes() {
                        builder.ins().ireduce(target_ty, value.value)
                    } else if target_ty.bytes() > value.ty.bytes() {
                        builder.ins().sextend(target_ty, value.value)
                    } else {
                        value.value
                    };
                    (pos, narrowed, variant_type.clone())
                }
                None => {
                    return Err(format!(
                        "Type {:?} not in union {:?}",
                        value.vole_type, variants
                    ));
                }
            }
        };

    // Allocate stack slot for the union
    let union_size = type_size(union_type, pointer_type);
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        union_size,
        0,
    ));

    // Store tag at offset 0
    let tag_val = builder.ins().iconst(types::I8, tag as i64);
    builder.ins().stack_store(tag_val, slot, 0);

    // Store payload at offset 8 (after alignment padding)
    if actual_type != Type::Nil {
        builder.ins().stack_store(actual_value, slot, 8);
    }

    // Return pointer to the stack slot
    let ptr = builder.ins().stack_addr(pointer_type, slot, 0);
    Ok(CompiledValue {
        value: ptr,
        ty: pointer_type,
        vole_type: union_type.clone(),
    })
}

/// Returns true if a terminating statement (return/break) was compiled
pub(super) fn compile_block(
    builder: &mut FunctionBuilder,
    block: &frontend::Block,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    let mut terminated = false;
    for stmt in &block.stmts {
        if terminated {
            break; // Don't compile unreachable code
        }
        terminated = compile_stmt(builder, stmt, variables, cf_ctx, ctx)?;
    }
    Ok(terminated)
}

/// Returns true if this statement terminates (return/break)
pub(super) fn compile_stmt(
    builder: &mut FunctionBuilder,
    stmt: &Stmt,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    match stmt {
        Stmt::Let(let_stmt) => {
            let init = compile_expr(builder, &let_stmt.init, variables, ctx)?;

            // Check if there's a type annotation
            let (final_value, final_type) = if let Some(ty_expr) = &let_stmt.ty {
                let declared_type = resolve_type_expr(ty_expr, ctx.type_aliases);
                // If declared type is a union and init is not, wrap init into the union
                if matches!(&declared_type, Type::Union(_))
                    && !matches!(&init.vole_type, Type::Union(_))
                {
                    let wrapped = construct_union(builder, init, &declared_type, ctx.pointer_type)?;
                    (wrapped.value, wrapped.vole_type)
                } else if declared_type.is_integer() && init.vole_type.is_integer() {
                    // Handle integer type narrowing (e.g., i64 literal to i32 variable)
                    let declared_cty = type_to_cranelift(&declared_type, ctx.pointer_type);
                    let init_cty = init.ty;
                    if declared_cty.bits() < init_cty.bits() {
                        // Truncate to narrower type
                        let narrowed = builder.ins().ireduce(declared_cty, init.value);
                        (narrowed, declared_type)
                    } else if declared_cty.bits() > init_cty.bits() {
                        // Extend to wider type (sign extend)
                        let widened = builder.ins().sextend(declared_cty, init.value);
                        (widened, declared_type)
                    } else {
                        (init.value, declared_type)
                    }
                } else if declared_type == Type::F32 && init.vole_type == Type::F64 {
                    // Handle f64 to f32 narrowing
                    let narrowed = builder.ins().fdemote(types::F32, init.value);
                    (narrowed, declared_type)
                } else if declared_type == Type::F64 && init.vole_type == Type::F32 {
                    // Handle f32 to f64 promotion
                    let widened = builder.ins().fpromote(types::F64, init.value);
                    (widened, declared_type)
                } else {
                    // Use declared type but keep the value
                    (init.value, declared_type)
                }
            } else {
                (init.value, init.vole_type)
            };

            let cranelift_ty = type_to_cranelift(&final_type, ctx.pointer_type);
            let var = builder.declare_var(cranelift_ty);
            builder.def_var(var, final_value);
            variables.insert(let_stmt.name, (var, final_type));
            Ok(false)
        }
        Stmt::Expr(expr_stmt) => {
            compile_expr(builder, &expr_stmt.expr, variables, ctx)?;
            Ok(false)
        }
        Stmt::Return(ret) => {
            if let Some(value) = &ret.value {
                let compiled = compile_expr(builder, value, variables, ctx)?;
                builder.ins().return_(&[compiled.value]);
            } else {
                builder.ins().return_(&[]);
            }
            Ok(true)
        }
        Stmt::While(while_stmt) => {
            // Create blocks
            let header_block = builder.create_block(); // Condition check
            let body_block = builder.create_block(); // Loop body
            let exit_block = builder.create_block(); // After loop

            // Jump to header
            builder.ins().jump(header_block, &[]);

            // Header block - check condition
            builder.switch_to_block(header_block);
            let cond = compile_expr(builder, &while_stmt.condition, variables, ctx)?;
            // Extend bool to i32 for comparison if needed
            let cond_i32 = builder.ins().uextend(types::I32, cond.value);
            builder
                .ins()
                .brif(cond_i32, body_block, &[], exit_block, &[]);

            // Body block
            builder.switch_to_block(body_block);
            // For while loops, continue jumps to the header (condition check)
            cf_ctx.push_loop(exit_block, header_block);
            let body_terminated = compile_block(builder, &while_stmt.body, variables, cf_ctx, ctx)?;
            cf_ctx.pop_loop();

            // Jump back to header (if not already terminated by break/return)
            if !body_terminated {
                builder.ins().jump(header_block, &[]);
            }

            // Continue in exit block
            builder.switch_to_block(exit_block);

            // Seal blocks
            builder.seal_block(header_block);
            builder.seal_block(body_block);
            builder.seal_block(exit_block);

            Ok(false)
        }
        Stmt::If(if_stmt) => {
            let cond = compile_expr(builder, &if_stmt.condition, variables, ctx)?;
            let cond_i32 = builder.ins().uextend(types::I32, cond.value);

            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();

            builder
                .ins()
                .brif(cond_i32, then_block, &[], else_block, &[]);

            // Then branch
            builder.switch_to_block(then_block);
            let then_terminated =
                compile_block(builder, &if_stmt.then_branch, variables, cf_ctx, ctx)?;
            if !then_terminated {
                builder.ins().jump(merge_block, &[]);
            }

            // Else branch
            builder.switch_to_block(else_block);
            let else_terminated = if let Some(else_branch) = &if_stmt.else_branch {
                compile_block(builder, else_branch, variables, cf_ctx, ctx)?
            } else {
                false
            };
            if !else_terminated {
                builder.ins().jump(merge_block, &[]);
            }

            // Continue after if
            builder.switch_to_block(merge_block);

            builder.seal_block(then_block);
            builder.seal_block(else_block);
            builder.seal_block(merge_block);

            // If both branches terminate, the if statement terminates
            Ok(then_terminated && else_terminated)
        }
        Stmt::For(for_stmt) => {
            if let ExprKind::Range(range) = &for_stmt.iterable.kind {
                // Compile range bounds
                let start_val = compile_expr(builder, &range.start, variables, ctx)?;
                let end_val = compile_expr(builder, &range.end, variables, ctx)?;

                // Create loop variable as Cranelift variable
                let var = builder.declare_var(types::I64);
                builder.def_var(var, start_val.value);
                variables.insert(for_stmt.var_name, (var, Type::I64));

                // Create blocks
                let header = builder.create_block();
                let body_block = builder.create_block();
                let continue_block = builder.create_block();
                let exit_block = builder.create_block();

                builder.ins().jump(header, &[]);

                // Header: load current, compare to end
                builder.switch_to_block(header);
                let current = builder.use_var(var);
                let cmp = if range.inclusive {
                    builder
                        .ins()
                        .icmp(IntCC::SignedLessThanOrEqual, current, end_val.value)
                } else {
                    builder
                        .ins()
                        .icmp(IntCC::SignedLessThan, current, end_val.value)
                };
                builder.ins().brif(cmp, body_block, &[], exit_block, &[]);

                // Body
                builder.switch_to_block(body_block);
                cf_ctx.push_loop(exit_block, continue_block);
                let body_terminated =
                    compile_block(builder, &for_stmt.body, variables, cf_ctx, ctx)?;
                cf_ctx.pop_loop();

                if !body_terminated {
                    builder.ins().jump(continue_block, &[]);
                }

                // Continue: increment and jump to header
                builder.switch_to_block(continue_block);
                let current = builder.use_var(var);
                let next = builder.ins().iadd_imm(current, 1);
                builder.def_var(var, next);
                builder.ins().jump(header, &[]);

                // Exit
                builder.switch_to_block(exit_block);

                // Seal blocks
                builder.seal_block(header);
                builder.seal_block(body_block);
                builder.seal_block(continue_block);
                builder.seal_block(exit_block);

                Ok(false)
            } else {
                // Array iteration
                let arr = compile_expr(builder, &for_stmt.iterable, variables, ctx)?;

                // Get array length
                let len_id = ctx
                    .func_ids
                    .get("vole_array_len")
                    .ok_or_else(|| "vole_array_len not found".to_string())?;
                let len_ref = ctx.module.declare_func_in_func(*len_id, builder.func);
                let len_call = builder.ins().call(len_ref, &[arr.value]);
                let len_val = builder.inst_results(len_call)[0];

                // Create index variable (i = 0)
                let idx_var = builder.declare_var(types::I64);
                let zero = builder.ins().iconst(types::I64, 0);
                builder.def_var(idx_var, zero);

                // Determine element type from array type
                let elem_type = match &arr.vole_type {
                    Type::Array(elem) => elem.as_ref().clone(),
                    _ => Type::I64,
                };

                // Create element variable
                let elem_var = builder.declare_var(types::I64);
                builder.def_var(elem_var, zero); // Initial value doesn't matter
                variables.insert(for_stmt.var_name, (elem_var, elem_type));

                // Loop blocks
                let header = builder.create_block();
                let body_block = builder.create_block();
                let continue_block = builder.create_block();
                let exit_block = builder.create_block();

                builder.ins().jump(header, &[]);

                // Header: check i < len
                builder.switch_to_block(header);
                let current_idx = builder.use_var(idx_var);
                let cmp = builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, current_idx, len_val);
                builder.ins().brif(cmp, body_block, &[], exit_block, &[]);

                // Body: load element, execute body
                builder.switch_to_block(body_block);

                // Get element: arr[i]
                let get_value_id = ctx
                    .func_ids
                    .get("vole_array_get_value")
                    .ok_or_else(|| "vole_array_get_value not found".to_string())?;
                let get_value_ref = ctx.module.declare_func_in_func(*get_value_id, builder.func);
                let current_idx = builder.use_var(idx_var);
                let get_call = builder.ins().call(get_value_ref, &[arr.value, current_idx]);
                let elem_val = builder.inst_results(get_call)[0];
                builder.def_var(elem_var, elem_val);

                // Execute loop body
                cf_ctx.push_loop(exit_block, continue_block);
                let body_terminated =
                    compile_block(builder, &for_stmt.body, variables, cf_ctx, ctx)?;
                cf_ctx.pop_loop();

                // Jump to continue block if not already terminated
                if !body_terminated {
                    builder.ins().jump(continue_block, &[]);
                }

                // Continue: increment and loop
                builder.switch_to_block(continue_block);
                let current_idx = builder.use_var(idx_var);
                let next_idx = builder.ins().iadd_imm(current_idx, 1);
                builder.def_var(idx_var, next_idx);
                builder.ins().jump(header, &[]);

                // Exit
                builder.switch_to_block(exit_block);

                // Seal blocks
                builder.seal_block(header);
                builder.seal_block(body_block);
                builder.seal_block(continue_block);
                builder.seal_block(exit_block);

                Ok(false)
            }
        }
        Stmt::Break(_) => {
            if let Some(exit_block) = cf_ctx.current_loop_exit() {
                builder.ins().jump(exit_block, &[]);
            }
            Ok(true)
        }
        Stmt::Continue(_) => {
            if let Some(continue_block) = cf_ctx.current_loop_continue() {
                builder.ins().jump(continue_block, &[]);
                // Create an unreachable block to continue building
                // (the code after continue is dead but Cranelift still needs a current block)
                let unreachable = builder.create_block();
                builder.switch_to_block(unreachable);
                builder.seal_block(unreachable);
            }
            Ok(true)
        }
    }
}

/// Compile a block with capture awareness
pub(super) fn compile_block_with_captures(
    builder: &mut FunctionBuilder,
    block: &frontend::Block,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    capture_bindings: &HashMap<Symbol, CaptureBinding>,
    closure_var: Option<Variable>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    let mut terminated = false;
    for stmt in &block.stmts {
        if terminated {
            break;
        }
        terminated = compile_stmt_with_captures(
            builder,
            stmt,
            variables,
            capture_bindings,
            closure_var,
            cf_ctx,
            ctx,
        )?;
    }
    Ok(terminated)
}

/// Compile a statement with capture awareness
pub(super) fn compile_stmt_with_captures(
    builder: &mut FunctionBuilder,
    stmt: &Stmt,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    capture_bindings: &HashMap<Symbol, CaptureBinding>,
    closure_var: Option<Variable>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    use super::compiler::compile_expr_with_captures;

    match stmt {
        Stmt::Let(let_stmt) => {
            let init = compile_expr_with_captures(
                builder,
                &let_stmt.init,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )?;
            let cranelift_ty = type_to_cranelift(&init.vole_type, ctx.pointer_type);
            let var = builder.declare_var(cranelift_ty);
            builder.def_var(var, init.value);
            variables.insert(let_stmt.name, (var, init.vole_type));
            Ok(false)
        }
        Stmt::Expr(expr_stmt) => {
            compile_expr_with_captures(
                builder,
                &expr_stmt.expr,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )?;
            Ok(false)
        }
        Stmt::Return(ret) => {
            if let Some(value) = &ret.value {
                let compiled = compile_expr_with_captures(
                    builder,
                    value,
                    variables,
                    capture_bindings,
                    closure_var,
                    ctx,
                )?;
                builder.ins().return_(&[compiled.value]);
            } else {
                builder.ins().return_(&[]);
            }
            Ok(true)
        }
        // For other statements, delegate to regular compilation
        // They don't directly reference captures, only through expressions
        _ => compile_stmt(builder, stmt, variables, cf_ctx, ctx),
    }
}
