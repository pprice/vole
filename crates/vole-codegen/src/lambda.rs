// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use vole_frontend::{BinaryOp, Expr, ExprKind, LambdaBody, LambdaExpr, NodeId, Symbol};
use vole_sema::type_arena::{TypeArena, TypeId, TypeIdVec};

use super::RuntimeFn;
use super::context::{Captures, Cg, ControlFlow};
use super::types::{
    CompileCtx, CompiledValue, resolve_type_expr_id, type_id_size, type_id_to_cranelift,
};

/// Information about a captured variable for lambda compilation
#[derive(Clone, Copy)]
pub(crate) struct CaptureBinding {
    /// Index in the closure's captures array
    pub index: usize,
    /// Vole type of the captured variable (interned TypeId)
    pub vole_type: TypeId,
}

impl CaptureBinding {
    pub fn new(index: usize, vole_type: TypeId) -> Self {
        Self { index, vole_type }
    }
}

/// Build capture bindings from a list of captures and variable types
pub(crate) fn build_capture_bindings(
    captures: &[vole_frontend::Capture],
    variables: &HashMap<Symbol, (Variable, TypeId)>,
    arena: &mut TypeArena,
) -> HashMap<Symbol, CaptureBinding> {
    let mut bindings = HashMap::new();
    let default_type_id = arena.primitives.i64;
    for (i, capture) in captures.iter().enumerate() {
        let vole_type_id = variables
            .get(&capture.name)
            .map(|(_, ty)| *ty)
            .unwrap_or(default_type_id);
        bindings.insert(capture.name, CaptureBinding::new(i, vole_type_id));
    }
    bindings
}

/// Infer the return type of a lambda expression body.
pub(crate) fn infer_lambda_return_type(
    body: &LambdaBody,
    param_types: &[(Symbol, TypeId)],
    ctx: &CompileCtx,
) -> TypeId {
    match body {
        LambdaBody::Expr(expr) => infer_expr_type(expr, param_types, ctx),
        LambdaBody::Block(_) => ctx.arena.borrow().primitives.i64,
    }
}

/// Get lambda param and return types from explicit annotations or codegen inference (fallback when sema type unavailable)
fn get_lambda_types_fallback(lambda: &LambdaExpr, ctx: &CompileCtx) -> (Vec<TypeId>, TypeId) {
    let primitives = ctx.arena.borrow().primitives;

    // Build param type ids from AST annotations, defaulting to i64
    let param_type_ids: Vec<TypeId> = lambda
        .params
        .iter()
        .map(|p| {
            p.ty.as_ref()
                .map(|t| resolve_type_expr_id(t, ctx))
                .unwrap_or(primitives.i64)
        })
        .collect();

    // Get return type from annotation or infer from body
    let return_type_id = if let Some(t) = &lambda.return_type {
        resolve_type_expr_id(t, ctx)
    } else {
        let param_context: Vec<(Symbol, TypeId)> = lambda
            .params
            .iter()
            .zip(param_type_ids.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();
        infer_lambda_return_type(&lambda.body, &param_context, ctx)
    };

    (param_type_ids, return_type_id)
}

/// Infer the type of an expression given parameter types as context.
pub(crate) fn infer_expr_type(
    expr: &Expr,
    param_types: &[(Symbol, TypeId)],
    ctx: &CompileCtx,
) -> TypeId {
    let primitives = ctx.arena.borrow().primitives;

    match &expr.kind {
        ExprKind::IntLiteral(_) => primitives.i64,
        ExprKind::FloatLiteral(_) => primitives.f64,
        ExprKind::BoolLiteral(_) => primitives.bool,
        ExprKind::StringLiteral(_) => primitives.string,
        ExprKind::InterpolatedString(_) => primitives.string,
        ExprKind::Nil => ctx.arena.borrow().nil(),
        ExprKind::Done => ctx.arena.borrow().done(),

        ExprKind::Identifier(sym) => {
            for (name, ty_id) in param_types {
                if name == sym {
                    return *ty_id;
                }
            }
            for global in ctx.globals {
                if global.name == *sym
                    && let Some(type_expr) = &global.ty
                {
                    return resolve_type_expr_id(type_expr, ctx);
                }
            }
            primitives.i64
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
                | BinaryOp::Or => primitives.bool,

                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    if left_ty == right_ty {
                        left_ty
                    } else if left_ty == primitives.i64 || right_ty == primitives.i64 {
                        primitives.i64
                    } else if left_ty == primitives.f64 || right_ty == primitives.f64 {
                        primitives.f64
                    } else if left_ty == primitives.i32 || right_ty == primitives.i32 {
                        primitives.i32
                    } else {
                        left_ty
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
            let arena = ctx.arena.borrow();
            if let Some((_, ret_id, _)) = arena.unwrap_function(callee_ty) {
                ret_id
            } else {
                primitives.i64
            }
        }

        ExprKind::Lambda(lambda) => {
            let primitives = ctx.arena.borrow().primitives;
            // Resolve param types directly to TypeIds
            let lambda_param_ids: TypeIdVec = lambda
                .params
                .iter()
                .map(|p| {
                    p.ty.as_ref()
                        .map(|t| resolve_type_expr_id(t, ctx))
                        .unwrap_or(primitives.i64)
                })
                .collect();
            let return_ty_id = lambda
                .return_type
                .as_ref()
                .map(|t| resolve_type_expr_id(t, ctx))
                .unwrap_or(primitives.i64);

            ctx.arena.borrow_mut().function(
                lambda_param_ids,
                return_ty_id,
                !lambda.captures.borrow().is_empty(),
            )
        }

        _ => primitives.i64,
    }
}

/// Compile a lambda expression - dispatches to pure or capturing version
pub(super) fn compile_lambda(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    variables: &HashMap<Symbol, (Variable, TypeId)>,
    ctx: &mut CompileCtx,
    node_id: NodeId,
) -> Result<CompiledValue, String> {
    let captures = lambda.captures.borrow();
    let has_captures = !captures.is_empty();

    tracing::debug!(
        params = lambda.params.len(),
        captures = captures.len(),
        has_captures,
        "compiling lambda"
    );

    if has_captures {
        compile_lambda_with_captures(builder, lambda, variables, ctx, node_id)
    } else {
        compile_pure_lambda(builder, lambda, ctx, node_id)
    }
}

/// Compile a pure lambda (no captures) - returns a function pointer
fn compile_pure_lambda(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    ctx: &mut CompileCtx,
    node_id: NodeId,
) -> Result<CompiledValue, String> {
    *ctx.lambda_counter += 1;

    // Try to get param and return types from sema analysis first
    let (param_type_ids, return_type_id) = if let Some(lambda_type_id) = ctx.get_expr_type(&node_id)
    {
        let arena = ctx.arena.borrow();
        if let Some((sema_params, ret_id, _)) = arena.unwrap_function(lambda_type_id) {
            // Use sema-inferred types
            (sema_params.to_vec(), ret_id)
        } else {
            drop(arena);
            get_lambda_types_fallback(lambda, ctx)
        }
    } else {
        get_lambda_types_fallback(lambda, ctx)
    };

    // Convert to Cranelift types
    let param_types: Vec<Type> = {
        let arena = ctx.arena.borrow();
        param_type_ids
            .iter()
            .map(|&ty| type_id_to_cranelift(ty, &arena, ctx.pointer_type))
            .collect()
    };

    let return_type = type_id_to_cranelift(return_type_id, &ctx.arena.borrow(), ctx.pointer_type);

    // Always use closure calling convention for consistency with how all lambdas
    // are now wrapped in Closure structs. First param is the closure pointer.
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(ctx.pointer_type)); // closure ptr (ignored for pure lambdas)
    for &param_ty in &param_types {
        sig.params.push(AbiParam::new(param_ty));
    }
    sig.returns.push(AbiParam::new(return_type));

    let (name_id, func_key) = ctx.func_registry.intern_lambda_name(*ctx.lambda_counter);
    let lambda_name = ctx.func_registry.name_table().display(name_id);
    let func_id = ctx
        .module
        .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
        .map_err(|e| e.to_string())?;

    ctx.func_registry.set_func_id(func_key, func_id);
    ctx.func_registry.set_return_type(func_key, return_type_id);

    let mut lambda_ctx = ctx.module.make_context();
    lambda_ctx.func.signature = sig.clone();

    {
        let mut lambda_builder_ctx = FunctionBuilderContext::new();
        let mut lambda_builder =
            FunctionBuilder::new(&mut lambda_ctx.func, &mut lambda_builder_ctx);

        let entry_block = lambda_builder.create_block();
        lambda_builder.append_block_params_for_function_params(entry_block);
        lambda_builder.switch_to_block(entry_block);

        let mut lambda_variables: HashMap<Symbol, (Variable, TypeId)> = HashMap::new();
        let block_params = lambda_builder.block_params(entry_block).to_vec();
        // Skip block_params[0] which is the closure pointer (unused for pure lambdas)
        for (i, param) in lambda.params.iter().enumerate() {
            let var = lambda_builder.declare_var(param_types[i]);
            lambda_builder.def_var(var, block_params[i + 1]); // +1 to skip closure ptr
            lambda_variables.insert(param.name, (var, param_type_ids[i]));
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
            return_type_id,
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

    // Always wrap lambdas in Closure structs for consistent calling convention.
    // This ensures iterator methods like .map() work correctly - they expect
    // all transform functions as Closure pointers, not raw function pointers.
    let alloc_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::ClosureAlloc)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
    let zero_captures = builder.ins().iconst(types::I64, 0);
    let alloc_call = builder.ins().call(alloc_ref, &[func_addr, zero_captures]);
    let closure_ptr = builder.inst_results(alloc_call)[0];

    // Create TypeId directly from components
    let func_type_id = {
        let mut arena = ctx.arena.borrow_mut();
        let param_ids: TypeIdVec = param_type_ids.iter().copied().collect();
        arena.function(param_ids, return_type_id, true) // is_closure=true
    };
    Ok(CompiledValue {
        value: closure_ptr,
        ty: ctx.pointer_type,
        type_id: func_type_id,
    })
}

/// Compile a lambda with captures - returns a closure pointer
fn compile_lambda_with_captures(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    variables: &HashMap<Symbol, (Variable, TypeId)>,
    ctx: &mut CompileCtx,
    node_id: NodeId,
) -> Result<CompiledValue, String> {
    let captures = lambda.captures.borrow();
    let num_captures = captures.len();

    *ctx.lambda_counter += 1;

    // Try to get param and return types from sema analysis first
    let (param_type_ids, return_type_id) = if let Some(lambda_type_id) = ctx.get_expr_type(&node_id)
    {
        let arena = ctx.arena.borrow();
        if let Some((sema_params, ret_id, _)) = arena.unwrap_function(lambda_type_id) {
            // Use sema-inferred types
            (sema_params.to_vec(), ret_id)
        } else {
            drop(arena);
            get_lambda_types_fallback(lambda, ctx)
        }
    } else {
        get_lambda_types_fallback(lambda, ctx)
    };

    // Convert to Cranelift types
    let param_types: Vec<Type> = {
        let arena = ctx.arena.borrow();
        param_type_ids
            .iter()
            .map(|&ty| type_id_to_cranelift(ty, &arena, ctx.pointer_type))
            .collect()
    };

    let return_type = type_id_to_cranelift(return_type_id, &ctx.arena.borrow(), ctx.pointer_type);

    // First param is the closure pointer
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(ctx.pointer_type));
    for &param_ty in &param_types {
        sig.params.push(AbiParam::new(param_ty));
    }
    sig.returns.push(AbiParam::new(return_type));

    let (name_id, func_key) = ctx.func_registry.intern_lambda_name(*ctx.lambda_counter);
    let lambda_name = ctx.func_registry.name_table().display(name_id);
    let func_id = ctx
        .module
        .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
        .map_err(|e| e.to_string())?;

    ctx.func_registry.set_func_id(func_key, func_id);
    ctx.func_registry.set_return_type(func_key, return_type_id);

    let capture_bindings =
        build_capture_bindings(&captures, variables, &mut ctx.arena.borrow_mut());

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

        let mut lambda_variables: HashMap<Symbol, (Variable, TypeId)> = HashMap::new();
        for (i, param) in lambda.params.iter().enumerate() {
            let var = lambda_builder.declare_var(param_types[i]);
            lambda_builder.def_var(var, block_params[i + 1]);
            lambda_variables.insert(param.name, (var, param_type_ids[i]));
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
            return_type_id,
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
        .func_registry
        .runtime_key(RuntimeFn::ClosureAlloc)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
    let num_captures_val = builder.ins().iconst(types::I64, num_captures as i64);
    let alloc_call = builder
        .ins()
        .call(alloc_ref, &[func_addr, num_captures_val]);
    let closure_ptr = builder.inst_results(alloc_call)[0];

    // Set up each capture
    let set_capture_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::ClosureSetCapture)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_closure_set_capture not found".to_string())?;
    let set_capture_ref = ctx
        .module
        .declare_func_in_func(set_capture_id, builder.func);

    let heap_alloc_id = ctx
        .func_registry
        .runtime_key(RuntimeFn::HeapAlloc)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| "vole_heap_alloc not found".to_string())?;
    let heap_alloc_ref = ctx.module.declare_func_in_func(heap_alloc_id, builder.func);

    for (i, capture) in captures.iter().enumerate() {
        let (var, vole_type_id) = variables
            .get(&capture.name)
            .ok_or_else(|| format!("Captured variable not found: {:?}", capture.name))?;
        let current_value = builder.use_var(*var);

        let size = type_id_size(
            *vole_type_id,
            ctx.pointer_type,
            &ctx.analyzed.entity_registry,
            &ctx.arena.borrow(),
        );
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

    // Create TypeId directly from components
    let func_type_id = {
        let mut arena = ctx.arena.borrow_mut();
        let param_ids: TypeIdVec = param_type_ids.iter().copied().collect();
        arena.function(param_ids, return_type_id, true) // is_closure=true
    };
    Ok(CompiledValue {
        value: closure_ptr,
        ty: ctx.pointer_type,
        type_id: func_type_id,
    })
}

/// Compile a lambda body (either expression or block)
#[allow(clippy::too_many_arguments)]
fn compile_lambda_body(
    builder: &mut FunctionBuilder,
    body: &LambdaBody,
    variables: &mut HashMap<Symbol, (Variable, TypeId)>,
    capture_bindings: &HashMap<Symbol, CaptureBinding>,
    closure_var: Option<Variable>,
    cf: &mut ControlFlow,
    ctx: &mut CompileCtx,
    return_type_id: TypeId,
) -> Result<Option<CompiledValue>, String> {
    // Set up function context for raise/try statements (same as regular functions)
    let old_return_type = ctx.current_function_return_type;
    ctx.current_function_return_type = Some(return_type_id);
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
            // Restore old context
            ctx.current_function_return_type = old_return_type;
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
            // Restore old context
            ctx.current_function_return_type = old_return_type;
            if terminated {
                Ok(None)
            } else {
                let zero = builder.ins().iconst(types::I64, 0);
                Ok(Some(CompiledValue {
                    value: zero,
                    ty: types::I64,
                    type_id: ctx.arena.borrow().primitives.i64,
                }))
            }
        }
    }
}

impl Cg<'_, '_, '_> {
    /// Compile a lambda expression
    pub fn lambda(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> Result<CompiledValue, String> {
        compile_lambda(self.builder, lambda, self.vars, self.ctx, node_id)
    }
}
