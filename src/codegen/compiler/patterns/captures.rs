// src/codegen/compiler/patterns/captures.rs

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::super::calls::compile_call_with_captures;
use super::super::fields::{compile_field_assign, compile_index_assign};
use super::super::ops::compile_binary_op;
use super::expr::compile_expr;
use crate::codegen::RuntimeFn;
use crate::codegen::lambda::CaptureBinding;
use crate::codegen::types::{CompileCtx, CompiledValue, type_to_cranelift};
use crate::frontend::{AssignTarget, Expr, ExprKind, Symbol};
use crate::sema::Type;

pub(crate) fn compile_expr_with_captures(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    capture_bindings: &HashMap<Symbol, CaptureBinding>,
    closure_var: Option<Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::Identifier(sym) => {
            // First check if this is a captured variable
            if let Some(binding) = capture_bindings.get(sym) {
                // Access via closure
                let closure_var = closure_var.ok_or_else(|| {
                    "Closure variable not available for capture access".to_string()
                })?;
                let closure_ptr = builder.use_var(closure_var);

                // Call vole_closure_get_capture(closure, index) -> *mut u8
                let get_capture_id = ctx
                    .func_registry
                    .runtime_key(RuntimeFn::ClosureGetCapture)
                    .and_then(|key| ctx.func_registry.func_id(key))
                    .ok_or_else(|| "vole_closure_get_capture not found".to_string())?;
                let get_capture_ref = ctx
                    .module
                    .declare_func_in_func(get_capture_id, builder.func);
                let index_val = builder.ins().iconst(types::I64, binding.index as i64);
                let call = builder
                    .ins()
                    .call(get_capture_ref, &[closure_ptr, index_val]);
                let heap_ptr = builder.inst_results(call)[0];

                // Load value from heap pointer
                let cranelift_ty = type_to_cranelift(&binding.vole_type, ctx.pointer_type);
                let value = builder
                    .ins()
                    .load(cranelift_ty, MemFlags::new(), heap_ptr, 0);

                return Ok(CompiledValue {
                    value,
                    ty: cranelift_ty,
                    vole_type: binding.vole_type.clone(),
                });
            }

            // Otherwise, regular variable lookup
            if let Some((var, vole_type)) = variables.get(sym) {
                let val = builder.use_var(*var);
                let ty = builder.func.dfg.value_type(val);
                Ok(CompiledValue {
                    value: val,
                    ty,
                    vole_type: vole_type.clone(),
                })
            } else {
                // Check globals
                if let Some(global) = ctx.globals.iter().find(|g| g.name == *sym) {
                    compile_expr_with_captures(
                        builder,
                        &global.init,
                        variables,
                        capture_bindings,
                        closure_var,
                        ctx,
                    )
                } else {
                    Err(format!(
                        "undefined variable: {}",
                        ctx.interner.resolve(*sym)
                    ))
                }
            }
        }
        ExprKind::Assign(assign) => {
            match &assign.target {
                AssignTarget::Variable(sym) => {
                    // Check if assigning to a captured variable
                    if let Some(binding) = capture_bindings.get(sym) {
                        let value = compile_expr_with_captures(
                            builder,
                            &assign.value,
                            variables,
                            capture_bindings,
                            closure_var,
                            ctx,
                        )?;

                        // Get the capture pointer
                        let closure_var = closure_var.ok_or_else(|| {
                            "Closure variable not available for capture access".to_string()
                        })?;
                        let closure_ptr = builder.use_var(closure_var);

                        let get_capture_id = ctx
                            .func_registry
                            .runtime_key(RuntimeFn::ClosureGetCapture)
                            .and_then(|key| ctx.func_registry.func_id(key))
                            .ok_or_else(|| "vole_closure_get_capture not found".to_string())?;
                        let get_capture_ref = ctx
                            .module
                            .declare_func_in_func(get_capture_id, builder.func);
                        let index_val = builder.ins().iconst(types::I64, binding.index as i64);
                        let call = builder
                            .ins()
                            .call(get_capture_ref, &[closure_ptr, index_val]);
                        let heap_ptr = builder.inst_results(call)[0];

                        // Store the new value
                        builder
                            .ins()
                            .store(MemFlags::new(), value.value, heap_ptr, 0);

                        return Ok(value);
                    }

                    // Otherwise, regular assignment
                    let value = compile_expr_with_captures(
                        builder,
                        &assign.value,
                        variables,
                        capture_bindings,
                        closure_var,
                        ctx,
                    )?;
                    if let Some((var, _)) = variables.get(sym) {
                        builder.def_var(*var, value.value);
                        Ok(value)
                    } else {
                        Err(format!(
                            "undefined variable: {}",
                            ctx.interner.resolve(*sym)
                        ))
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
        ExprKind::Binary(bin) => {
            // Compile left and right with capture awareness
            let left = compile_expr_with_captures(
                builder,
                &bin.left,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )?;
            let right = compile_expr_with_captures(
                builder,
                &bin.right,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )?;

            // Use the existing binary operation logic
            compile_binary_op(builder, left, right, bin.op, ctx)
        }
        ExprKind::Call(call) => {
            // For calls, we need to compile with capture awareness
            compile_call_with_captures(
                builder,
                call,
                expr.span.line,
                expr.id,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )
        }
        // For other expression types, delegate to regular compilation
        // They may contain nested expressions that need capture handling
        _ => compile_expr(builder, expr, variables, ctx),
    }
}
