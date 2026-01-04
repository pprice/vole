// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::frontend::{BinaryOp, Expr, ExprKind, LambdaBody, LambdaExpr, Symbol};
use crate::sema::{FunctionType, Type};

use super::context::{Captures, Cg, ControlFlow};
use super::types::{CompileCtx, CompiledValue, resolve_type_expr, type_size, type_to_cranelift};

/// Information about a captured variable for lambda compilation
#[derive(Clone)]
pub(crate) struct CaptureBinding {
    /// Index in the closure's captures array
    pub index: usize,
    /// Vole type of the captured variable
    pub vole_type: Type,
}

impl CaptureBinding {
    pub fn new(index: usize, vole_type: Type) -> Self {
        Self { index, vole_type }
    }
}

/// Build capture bindings from a list of captures and variable types
pub(crate) fn build_capture_bindings(
    captures: &[crate::frontend::Capture],
    variables: &HashMap<Symbol, (Variable, Type)>,
) -> HashMap<Symbol, CaptureBinding> {
    let mut bindings = HashMap::new();
    for (i, capture) in captures.iter().enumerate() {
        let vole_type = variables
            .get(&capture.name)
            .map(|(_, ty)| ty.clone())
            .unwrap_or(Type::I64);
        bindings.insert(capture.name, CaptureBinding::new(i, vole_type));
    }
    bindings
}

/// Infer the return type of a lambda expression body.
pub(crate) fn infer_lambda_return_type(
    body: &LambdaBody,
    param_types: &[(Symbol, Type)],
    ctx: &CompileCtx,
) -> Type {
    match body {
        LambdaBody::Expr(expr) => infer_expr_type(expr, param_types, ctx),
        LambdaBody::Block(_) => Type::I64,
    }
}

/// Infer the type of an expression given parameter types as context.
pub(crate) fn infer_expr_type(
    expr: &Expr,
    param_types: &[(Symbol, Type)],
    ctx: &CompileCtx,
) -> Type {
    match &expr.kind {
        ExprKind::IntLiteral(_) => Type::I64,
        ExprKind::FloatLiteral(_) => Type::F64,
        ExprKind::BoolLiteral(_) => Type::Bool,
        ExprKind::StringLiteral(_) => Type::String,
        ExprKind::InterpolatedString(_) => Type::String,
        ExprKind::Nil => Type::Nil,

        ExprKind::Identifier(sym) => {
            for (name, ty) in param_types {
                if name == sym {
                    return ty.clone();
                }
            }
            for global in ctx.globals {
                if global.name == *sym
                    && let Some(type_expr) = &global.ty
                {
                    return resolve_type_expr(type_expr, ctx.type_aliases);
                }
            }
            Type::I64
        }

        ExprKind::Binary(bin) => {
            let left_ty = infer_expr_type(&bin.left, param_types, ctx);
            let right_ty = infer_expr_type(&bin.right, param_types, ctx);

            match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge
                | BinaryOp::And
                | BinaryOp::Or => Type::Bool,

                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    if left_ty == right_ty {
                        left_ty
                    } else {
                        match (&left_ty, &right_ty) {
                            (Type::I64, _) | (_, Type::I64) => Type::I64,
                            (Type::F64, _) | (_, Type::F64) => Type::F64,
                            (Type::I32, _) | (_, Type::I32) => Type::I32,
                            _ => left_ty,
                        }
                    }
                }

                BinaryOp::BitAnd
                | BinaryOp::BitOr
                | BinaryOp::BitXor
                | BinaryOp::Shl
                | BinaryOp::Shr => left_ty,
            }
        }

        ExprKind::Unary(un) => infer_expr_type(&un.operand, param_types, ctx),

        ExprKind::Call(call) => {
            let callee_ty = infer_expr_type(&call.callee, param_types, ctx);
            match callee_ty {
                Type::Function(ft) => *ft.return_type,
                _ => Type::I64,
            }
        }

        ExprKind::Lambda(lambda) => {
            let lambda_params: Vec<Type> = lambda
                .params
                .iter()
                .map(|p| {
                    p.ty.as_ref()
                        .map(|t| resolve_type_expr(t, ctx.type_aliases))
                        .unwrap_or(Type::I64)
                })
                .collect();
            let return_ty = lambda
                .return_type
                .as_ref()
                .map(|t| resolve_type_expr(t, ctx.type_aliases))
                .unwrap_or(Type::I64);
            Type::Function(FunctionType {
                params: lambda_params,
                return_type: Box::new(return_ty),
                is_closure: !lambda.captures.borrow().is_empty(),
            })
        }

        _ => Type::I64,
    }
}

/// Compile a lambda expression - dispatches to pure or capturing version
pub(super) fn compile_lambda(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    variables: &HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let captures = lambda.captures.borrow();
    let has_captures = !captures.is_empty();

    if has_captures {
        compile_lambda_with_captures(builder, lambda, variables, ctx)
    } else {
        compile_pure_lambda(builder, lambda, ctx)
    }
}

/// Compile a pure lambda (no captures) - returns a function pointer
fn compile_pure_lambda(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let lambda_name = format!("__lambda_{}", *ctx.lambda_counter);
    *ctx.lambda_counter += 1;

    let param_types: Vec<types::Type> = lambda
        .params
        .iter()
        .map(|p| {
            p.ty.as_ref()
                .map(|t| {
                    type_to_cranelift(&resolve_type_expr(t, ctx.type_aliases), ctx.pointer_type)
                })
                .unwrap_or(types::I64)
        })
        .collect();

    let param_vole_types: Vec<Type> = lambda
        .params
        .iter()
        .map(|p| {
            p.ty.as_ref()
                .map(|t| resolve_type_expr(t, ctx.type_aliases))
                .unwrap_or(Type::I64)
        })
        .collect();

    let param_context: Vec<(Symbol, Type)> = lambda
        .params
        .iter()
        .zip(param_vole_types.iter())
        .map(|(p, ty)| (p.name, ty.clone()))
        .collect();

    let return_vole_type = lambda
        .return_type
        .as_ref()
        .map(|t| resolve_type_expr(t, ctx.type_aliases))
        .unwrap_or_else(|| infer_lambda_return_type(&lambda.body, &param_context, ctx));

    let return_type = type_to_cranelift(&return_vole_type, ctx.pointer_type);

    let mut sig = ctx.module.make_signature();
    for &param_ty in &param_types {
        sig.params.push(AbiParam::new(param_ty));
    }
    sig.returns.push(AbiParam::new(return_type));

    let func_id = ctx
        .module
        .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
        .map_err(|e| e.to_string())?;

    ctx.func_ids.insert(lambda_name, func_id);

    let mut lambda_ctx = ctx.module.make_context();
    lambda_ctx.func.signature = sig.clone();

    {
        let mut lambda_builder_ctx = FunctionBuilderContext::new();
        let mut lambda_builder =
            FunctionBuilder::new(&mut lambda_ctx.func, &mut lambda_builder_ctx);

        let entry_block = lambda_builder.create_block();
        lambda_builder.append_block_params_for_function_params(entry_block);
        lambda_builder.switch_to_block(entry_block);

        let mut lambda_variables: HashMap<Symbol, (Variable, Type)> = HashMap::new();
        let block_params = lambda_builder.block_params(entry_block).to_vec();
        for (i, param) in lambda.params.iter().enumerate() {
            let var = lambda_builder.declare_var(param_types[i]);
            lambda_builder.def_var(var, block_params[i]);
            lambda_variables.insert(param.name, (var, param_vole_types[i].clone()));
        }

        let capture_bindings: HashMap<Symbol, CaptureBinding> = HashMap::new();

        let mut lambda_cf = ControlFlow::new();
        let result = compile_lambda_body(
            &mut lambda_builder,
            &lambda.body,
            &mut lambda_variables,
            &capture_bindings,
            None,
            &mut lambda_cf,
            ctx,
        )?;

        if let Some(result_val) = result {
            lambda_builder.ins().return_(&[result_val.value]);
        }
        lambda_builder.seal_all_blocks();
        lambda_builder.finalize();
    }

    ctx.module
        .define_function(func_id, &mut lambda_ctx)
        .map_err(|e| format!("Failed to define lambda: {:?}", e))?;

    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let func_addr = builder.ins().func_addr(ctx.pointer_type, func_ref);

    Ok(CompiledValue {
        value: func_addr,
        ty: ctx.pointer_type,
        vole_type: Type::Function(FunctionType {
            params: param_vole_types,
            return_type: Box::new(return_vole_type),
            is_closure: false,
        }),
    })
}

/// Compile a lambda with captures - returns a closure pointer
fn compile_lambda_with_captures(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    variables: &HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let captures = lambda.captures.borrow();
    let num_captures = captures.len();

    let lambda_name = format!("__lambda_{}", *ctx.lambda_counter);
    *ctx.lambda_counter += 1;

    let param_types: Vec<types::Type> = lambda
        .params
        .iter()
        .map(|p| {
            p.ty.as_ref()
                .map(|t| {
                    type_to_cranelift(&resolve_type_expr(t, ctx.type_aliases), ctx.pointer_type)
                })
                .unwrap_or(types::I64)
        })
        .collect();

    let param_vole_types: Vec<Type> = lambda
        .params
        .iter()
        .map(|p| {
            p.ty.as_ref()
                .map(|t| resolve_type_expr(t, ctx.type_aliases))
                .unwrap_or(Type::I64)
        })
        .collect();

    let param_context: Vec<(Symbol, Type)> = lambda
        .params
        .iter()
        .zip(param_vole_types.iter())
        .map(|(p, ty)| (p.name, ty.clone()))
        .collect();

    let return_vole_type = lambda
        .return_type
        .as_ref()
        .map(|t| resolve_type_expr(t, ctx.type_aliases))
        .unwrap_or_else(|| infer_lambda_return_type(&lambda.body, &param_context, ctx));

    let return_type = type_to_cranelift(&return_vole_type, ctx.pointer_type);

    // First param is the closure pointer
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(ctx.pointer_type));
    for &param_ty in &param_types {
        sig.params.push(AbiParam::new(param_ty));
    }
    sig.returns.push(AbiParam::new(return_type));

    let func_id = ctx
        .module
        .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
        .map_err(|e| e.to_string())?;

    ctx.func_ids.insert(lambda_name, func_id);

    let capture_bindings = build_capture_bindings(&captures, variables);

    let mut lambda_ctx = ctx.module.make_context();
    lambda_ctx.func.signature = sig.clone();

    {
        let mut lambda_builder_ctx = FunctionBuilderContext::new();
        let mut lambda_builder =
            FunctionBuilder::new(&mut lambda_ctx.func, &mut lambda_builder_ctx);

        let entry_block = lambda_builder.create_block();
        lambda_builder.append_block_params_for_function_params(entry_block);
        lambda_builder.switch_to_block(entry_block);

        let block_params = lambda_builder.block_params(entry_block).to_vec();
        let closure_ptr = block_params[0];

        let mut lambda_variables: HashMap<Symbol, (Variable, Type)> = HashMap::new();
        for (i, param) in lambda.params.iter().enumerate() {
            let var = lambda_builder.declare_var(param_types[i]);
            lambda_builder.def_var(var, block_params[i + 1]);
            lambda_variables.insert(param.name, (var, param_vole_types[i].clone()));
        }

        let closure_var = lambda_builder.declare_var(ctx.pointer_type);
        lambda_builder.def_var(closure_var, closure_ptr);

        let mut lambda_cf = ControlFlow::new();
        let result = compile_lambda_body(
            &mut lambda_builder,
            &lambda.body,
            &mut lambda_variables,
            &capture_bindings,
            Some(closure_var),
            &mut lambda_cf,
            ctx,
        )?;

        if let Some(result_val) = result {
            lambda_builder.ins().return_(&[result_val.value]);
        }
        lambda_builder.seal_all_blocks();
        lambda_builder.finalize();
    }

    ctx.module
        .define_function(func_id, &mut lambda_ctx)
        .map_err(|e| format!("Failed to define lambda: {:?}", e))?;

    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let func_addr = builder.ins().func_addr(ctx.pointer_type, func_ref);

    // Allocate closure
    let alloc_id = ctx
        .func_ids
        .get("vole_closure_alloc")
        .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
    let alloc_ref = ctx.module.declare_func_in_func(*alloc_id, builder.func);
    let num_captures_val = builder.ins().iconst(types::I64, num_captures as i64);
    let alloc_call = builder
        .ins()
        .call(alloc_ref, &[func_addr, num_captures_val]);
    let closure_ptr = builder.inst_results(alloc_call)[0];

    // Set up each capture
    let set_capture_id = ctx
        .func_ids
        .get("vole_closure_set_capture")
        .ok_or_else(|| "vole_closure_set_capture not found".to_string())?;
    let set_capture_ref = ctx
        .module
        .declare_func_in_func(*set_capture_id, builder.func);

    let heap_alloc_id = ctx
        .func_ids
        .get("vole_heap_alloc")
        .ok_or_else(|| "vole_heap_alloc not found".to_string())?;
    let heap_alloc_ref = ctx
        .module
        .declare_func_in_func(*heap_alloc_id, builder.func);

    for (i, capture) in captures.iter().enumerate() {
        let (var, vole_type) = variables
            .get(&capture.name)
            .ok_or_else(|| format!("Captured variable not found: {:?}", capture.name))?;
        let current_value = builder.use_var(*var);

        let size = type_size(vole_type, ctx.pointer_type);
        let size_val = builder.ins().iconst(types::I64, size as i64);

        let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = builder.inst_results(alloc_call)[0];

        builder
            .ins()
            .store(MemFlags::new(), current_value, heap_ptr, 0);

        let index_val = builder.ins().iconst(types::I64, i as i64);
        builder
            .ins()
            .call(set_capture_ref, &[closure_ptr, index_val, heap_ptr]);
    }

    Ok(CompiledValue {
        value: closure_ptr,
        ty: ctx.pointer_type,
        vole_type: Type::Function(FunctionType {
            params: param_vole_types,
            return_type: Box::new(return_vole_type),
            is_closure: true,
        }),
    })
}

/// Compile a lambda body (either expression or block)
fn compile_lambda_body(
    builder: &mut FunctionBuilder,
    body: &LambdaBody,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    capture_bindings: &HashMap<Symbol, CaptureBinding>,
    closure_var: Option<Variable>,
    cf: &mut ControlFlow,
    ctx: &mut CompileCtx,
) -> Result<Option<CompiledValue>, String> {
    match body {
        LambdaBody::Expr(expr) => {
            let result = if capture_bindings.is_empty() {
                let mut cg = Cg::new(builder, variables, ctx, cf);
                cg.expr(expr)?
            } else {
                let captures = Captures {
                    bindings: capture_bindings,
                    closure_var: closure_var.expect("closure_var required for captures"),
                };
                let mut cg = Cg::with_captures(builder, variables, ctx, cf, captures);
                cg.expr(expr)?
            };
            Ok(Some(result))
        }
        LambdaBody::Block(block) => {
            let terminated = if capture_bindings.is_empty() {
                let mut cg = Cg::new(builder, variables, ctx, cf);
                cg.block(block)?
            } else {
                let captures = Captures {
                    bindings: capture_bindings,
                    closure_var: closure_var.expect("closure_var required for captures"),
                };
                let mut cg = Cg::with_captures(builder, variables, ctx, cf, captures);
                cg.block(block)?
            };
            if terminated {
                Ok(None)
            } else {
                let zero = builder.ins().iconst(types::I64, 0);
                Ok(Some(CompiledValue {
                    value: zero,
                    ty: types::I64,
                    vole_type: Type::I64,
                }))
            }
        }
    }
}

impl Cg<'_, '_, '_> {
    /// Compile a lambda expression
    pub fn lambda(&mut self, lambda: &LambdaExpr) -> Result<CompiledValue, String> {
        compile_lambda(self.builder, lambda, self.vars, self.ctx)
    }
}
