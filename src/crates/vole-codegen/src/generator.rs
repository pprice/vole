// src/codegen/generator.rs
//
// Coroutine-backed generator compilation.
//
// Generator functions (containing `yield` and returning `Iterator<T>`) are compiled as:
// 1. An inner body function: `extern "C" fn(closure_ptr: *const u8, yielder_ptr: *const u8)`
//    This function receives captures (params packed into a closure) and a yielder pointer.
//    Yield expressions call `vole_generator_yield(yielder_ptr, value)`.
// 2. A wrapper function (the declared function): captures params into a closure struct,
//    calls `vole_generator_new(body_fn, closure_ptr, elem_tag)`, returns the iterator pointer.

use cranelift::prelude::*;
use cranelift_codegen::ir::{FuncRef, Function};
use cranelift_module::Module;
use rustc_hash::FxHashMap;

use vole_frontend::{FuncBody, FuncDecl, Symbol};
use vole_sema::type_arena::TypeId;

use crate::compiler::common::{DefaultReturn, compile_function_body_with_cg};
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::rc_state::compute_rc_state;
use crate::types::{CodegenCtx, CompileEnv, array_element_tag_id, type_id_size};
use crate::{FunctionKey, RuntimeKey};

/// Check whether a return type is `Iterator<T>` and extract the element type if so.
///
/// Returns `Some(element_type_id)` if the return type is `Iterator<T>`, `None` otherwise.
pub(crate) fn extract_iterator_element_type(
    return_type_id: TypeId,
    env: &CompileEnv<'_>,
) -> Option<TypeId> {
    let arena = env.analyzed.type_arena();
    let (type_def_id, type_args) = arena.unwrap_interface(return_type_id)?;
    let name_table = env.analyzed.name_table();
    if !name_table.well_known.is_iterator_type_def(type_def_id) {
        return None;
    }
    type_args.first().copied()
}

/// Check whether an AST function body contains any yield expressions.
///
/// Walks the AST to find `ExprKind::Yield` nodes.
pub(crate) fn body_contains_yield(body: &FuncBody) -> bool {
    use vole_frontend::FuncBody as FB;
    match body {
        FB::Block(block) => block_contains_yield(block),
        FB::Expr(expr) => expr_contains_yield(expr),
    }
}

fn block_contains_yield(block: &vole_frontend::Block) -> bool {
    block.stmts.iter().any(stmt_contains_yield)
}

fn stmt_contains_yield(stmt: &vole_frontend::Stmt) -> bool {
    use vole_frontend::Stmt;
    match stmt {
        Stmt::Expr(expr_stmt) => expr_contains_yield(&expr_stmt.expr),
        Stmt::Let(let_stmt) => match &let_stmt.init {
            vole_frontend::LetInit::Expr(expr) => expr_contains_yield(expr),
            _ => false,
        },
        Stmt::LetTuple(lt) => expr_contains_yield(&lt.init),
        Stmt::Return(ret) => ret.value.as_ref().is_some_and(expr_contains_yield),
        Stmt::While(w) => expr_contains_yield(&w.condition) || block_contains_yield(&w.body),
        Stmt::For(f) => expr_contains_yield(&f.iterable) || block_contains_yield(&f.body),
        Stmt::If(if_stmt) => {
            expr_contains_yield(&if_stmt.condition)
                || block_contains_yield(&if_stmt.then_branch)
                || if_stmt
                    .else_branch
                    .as_ref()
                    .is_some_and(block_contains_yield)
        }
        Stmt::Break(_) | Stmt::Continue(_) | Stmt::Raise(_) => false,
    }
}

fn expr_contains_yield(expr: &vole_frontend::Expr) -> bool {
    use vole_frontend::ExprKind;
    match &expr.kind {
        ExprKind::Yield(_) => true,
        ExprKind::Block(block_expr) => {
            block_expr.stmts.iter().any(stmt_contains_yield)
                || block_expr
                    .trailing_expr
                    .as_ref()
                    .is_some_and(expr_contains_yield)
        }
        ExprKind::If(if_expr) => {
            expr_contains_yield(&if_expr.condition)
                || expr_contains_yield(&if_expr.then_branch)
                || if_expr
                    .else_branch
                    .as_ref()
                    .is_some_and(expr_contains_yield)
        }
        ExprKind::Call(call) => {
            expr_contains_yield(&call.callee) || call.args.iter().any(expr_contains_yield)
        }
        ExprKind::Binary(bin) => expr_contains_yield(&bin.left) || expr_contains_yield(&bin.right),
        ExprKind::Unary(un) => expr_contains_yield(&un.operand),
        ExprKind::Match(m) => {
            expr_contains_yield(&m.scrutinee)
                || m.arms.iter().any(|arm| expr_contains_yield(&arm.body))
        }
        ExprKind::MethodCall(mc) => {
            expr_contains_yield(&mc.object) || mc.args.iter().any(expr_contains_yield)
        }
        ExprKind::Lambda(_) => false, // Lambdas are separate closures; don't recurse
        _ => false,
    }
}

/// Parameters for compiling a generator function.
pub(crate) struct GeneratorParams<'a> {
    pub func: &'a FuncDecl,
    pub jit_func_id: cranelift_module::FuncId,
    pub wrapper_func_key: FunctionKey,
    pub param_type_ids: &'a [TypeId],
    pub elem_type_id: TypeId,
    pub module_id: Option<vole_identity::ModuleId>,
}

/// Resolve a RuntimeKey to a FuncRef usable in a FunctionBuilder.
fn runtime_func_ref(
    key: RuntimeKey,
    codegen_ctx: &mut CodegenCtx<'_>,
    func: &mut Function,
) -> CodegenResult<FuncRef> {
    let func_key = codegen_ctx
        .funcs()
        .runtime_key(key)
        .ok_or_else(|| CodegenError::not_found("runtime function", format!("{key:?}")))?;
    let jit_id = codegen_ctx
        .funcs()
        .func_id(func_key)
        .ok_or_else(|| CodegenError::not_found("function id", format!("{key:?}")))?;
    Ok(codegen_ctx.jit_module().declare_func_in_func(jit_id, func))
}

/// Compile a generator function as a coroutine-backed iterator.
///
/// This replaces the normal function compilation path for generators.
/// It creates:
/// 1. An inner body function with signature `(closure_ptr, yielder_ptr) -> void`
/// 2. A wrapper function that packs params into a closure, creates the coroutine iterator
pub(crate) fn compile_generator_function<'ctx>(
    params: &GeneratorParams<'_>,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
) -> CodegenResult<()> {
    let func = params.func;
    let param_type_ids = params.param_type_ids;
    let module_id = params.module_id;
    // Step 1: Compile the inner body function
    let (body_func_id, has_captures) =
        compile_generator_body(func, param_type_ids, module_id, codegen_ctx, env)?;

    // Step 2: Compile the wrapper function
    compile_generator_wrapper(params, body_func_id, has_captures, codegen_ctx, env)?;

    // Override the return type to RuntimeIterator(T) so callers use direct dispatch
    let arena = env.analyzed.type_arena();
    let runtime_iter_type_id = arena
        .lookup_runtime_iterator(params.elem_type_id)
        .ok_or_else(|| {
            CodegenError::internal(
                "RuntimeIterator type not pre-created by sema for generator element type",
            )
        })?;
    codegen_ctx
        .funcs()
        .set_return_type(params.wrapper_func_key, runtime_iter_type_id);

    Ok(())
}

/// Compile the inner body function for a generator.
///
/// Signature: `(closure_ptr: ptr, yielder_ptr: ptr) -> void`
///
/// Returns the declared FuncId and whether the function has captures.
fn compile_generator_body<'ctx>(
    func: &FuncDecl,
    param_type_ids: &[TypeId],
    module_id: Option<vole_identity::ModuleId>,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
) -> CodegenResult<(cranelift_module::FuncId, bool)> {
    let ptr_type = codegen_ctx.ptr_type();

    let lambda_id = env.state.lambda_counter.get();
    env.state.lambda_counter.set(lambda_id + 1);

    let body_func_key = codegen_ctx.funcs().intern_lambda(lambda_id);
    let body_func_name = codegen_ctx.funcs().display(body_func_key);

    let mut body_sig = codegen_ctx.jit_module().make_signature();
    body_sig.params.push(AbiParam::new(ptr_type)); // closure_ptr
    body_sig.params.push(AbiParam::new(ptr_type)); // yielder_ptr

    let body_func_id = codegen_ctx
        .jit_module()
        .declare_function(&body_func_name, cranelift_module::Linkage::Local, &body_sig)
        .map_err(CodegenError::cranelift)?;

    codegen_ctx.funcs().set_func_id(body_func_key, body_func_id);
    codegen_ctx
        .funcs()
        .set_return_type(body_func_key, TypeId::VOID);

    // Build capture bindings: each parameter becomes a closure capture
    let mut capture_bindings: FxHashMap<Symbol, crate::lambda::CaptureBinding> =
        FxHashMap::default();
    for (i, param) in func.params.iter().enumerate() {
        capture_bindings.insert(
            param.name,
            crate::lambda::CaptureBinding::new(i, param_type_ids[i]),
        );
    }
    let has_captures = !capture_bindings.is_empty();

    let mut body_ctx = codegen_ctx.jit_module().make_context();
    body_ctx.func.signature = body_sig;

    {
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut body_ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();
        let closure_ptr_val = block_params[0];
        let yielder_ptr_val = block_params[1];

        let captures = if has_captures {
            let closure_var = builder.declare_var(ptr_type);
            builder.def_var(closure_var, closure_ptr_val);
            Some(crate::context::Captures {
                bindings: &capture_bindings,
                closure_var,
            })
        } else {
            None
        };

        let yielder_var = builder.declare_var(ptr_type);
        builder.def_var(yielder_var, yielder_ptr_val);

        let mut cg = Cg::new(&mut builder, codegen_ctx, env)
            .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline)
            .with_captures(captures)
            .with_module(module_id)
            .with_yielder(yielder_var);

        compile_function_body_with_cg(&mut cg, &func.body, DefaultReturn::Empty)?;
        drop(cg);

        builder.seal_all_blocks();
        builder.finalize();
    }

    codegen_ctx
        .jit_module()
        .define_function(body_func_id, &mut body_ctx)
        .map_err(CodegenError::cranelift)?;

    Ok((body_func_id, has_captures))
}

/// Compile the wrapper function that creates the coroutine iterator.
///
/// Packs parameters into a closure, calls `vole_generator_new`, returns the iterator.
fn compile_generator_wrapper<'ctx>(
    params: &GeneratorParams<'_>,
    body_func_id: cranelift_module::FuncId,
    has_captures: bool,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
) -> CodegenResult<()> {
    let func = params.func;
    let param_type_ids = params.param_type_ids;
    let elem_type_id = params.elem_type_id;
    let ptr_type = codegen_ctx.ptr_type();
    let arena = env.analyzed.type_arena();

    let mut wrapper_ctx = codegen_ctx.jit_module().make_context();

    let mut wrapper_sig = codegen_ctx.jit_module().make_signature();
    for &param_type_id in param_type_ids {
        let cr_type = crate::types::type_id_to_cranelift(param_type_id, arena, ptr_type);
        wrapper_sig.params.push(AbiParam::new(cr_type));
    }
    wrapper_sig.returns.push(AbiParam::new(ptr_type));
    wrapper_ctx.func.signature = wrapper_sig;

    {
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut wrapper_ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);

        let block_params = builder.block_params(entry_block).to_vec();

        let body_func_ref = codegen_ctx
            .jit_module()
            .declare_func_in_func(body_func_id, builder.func);
        let body_func_addr = builder.ins().func_addr(ptr_type, body_func_ref);

        let closure_ptr = if has_captures {
            emit_capture_closure(
                &block_params,
                param_type_ids,
                body_func_addr,
                func.params.len(),
                codegen_ctx,
                env,
                &mut builder,
            )?
        } else {
            builder.ins().iconst(ptr_type, 0)
        };

        // Call vole_generator_new(body_fn, closure_ptr, elem_tag)
        let gen_new_ref = runtime_func_ref(RuntimeKey::GeneratorNew, codegen_ctx, builder.func)?;
        let elem_tag = array_element_tag_id(elem_type_id, arena);
        let elem_tag_val = builder.ins().iconst(types::I64, elem_tag);

        let gen_call = builder
            .ins()
            .call(gen_new_ref, &[body_func_addr, closure_ptr, elem_tag_val]);
        let iter_ptr = builder.inst_results(gen_call)[0];

        builder.ins().return_(&[iter_ptr]);
        builder.seal_all_blocks();
        builder.finalize();
    }

    codegen_ctx
        .jit_module()
        .define_function(params.jit_func_id, &mut wrapper_ctx)
        .map_err(CodegenError::cranelift)?;

    Ok(())
}

/// Emit closure allocation and capture setup for generator parameters.
///
/// Allocates a closure struct, stores each parameter as a capture with proper
/// RC management (rc_inc for RC types, interface-aware for fat pointers).
/// Returns the closure pointer value.
fn emit_capture_closure(
    block_params: &[Value],
    param_type_ids: &[TypeId],
    body_func_addr: Value,
    num_params: usize,
    codegen_ctx: &mut CodegenCtx<'_>,
    env: &CompileEnv<'_>,
    builder: &mut FunctionBuilder<'_>,
) -> CodegenResult<Value> {
    let ptr_type = codegen_ctx.ptr_type();
    let arena = env.analyzed.type_arena();

    // Resolve all needed runtime functions
    let alloc_ref = runtime_func_ref(RuntimeKey::ClosureAlloc, codegen_ctx, builder.func)?;
    let set_capture_ref =
        runtime_func_ref(RuntimeKey::ClosureSetCapture, codegen_ctx, builder.func)?;
    let set_size_ref =
        runtime_func_ref(RuntimeKey::ClosureSetCaptureSize, codegen_ctx, builder.func)?;
    let heap_alloc_ref = runtime_func_ref(RuntimeKey::HeapAlloc, codegen_ctx, builder.func)?;
    let rc_inc_ref = runtime_func_ref(RuntimeKey::RcInc, codegen_ctx, builder.func)?;
    let set_kind_ref =
        runtime_func_ref(RuntimeKey::ClosureSetCaptureKind, codegen_ctx, builder.func)?;

    let num_captures = builder.ins().iconst(types::I64, num_params as i64);
    let alloc_call = builder
        .ins()
        .call(alloc_ref, &[body_func_addr, num_captures]);
    let closure_ptr = builder.inst_results(alloc_call)[0];

    for (i, (&param_val, &param_type_id)) in
        block_params.iter().zip(param_type_ids.iter()).enumerate()
    {
        let is_interface = arena.is_interface(param_type_id);
        let is_rc =
            compute_rc_state(arena, env.analyzed.entity_registry(), param_type_id).needs_cleanup();

        // RC captures need rc_inc so the closure owns its own reference.
        // For interfaces, rc_inc the data_ptr (offset 0 of fat pointer),
        // not the fat pointer itself (which has no RcHeader).
        if is_rc {
            if is_interface {
                let data_word = builder
                    .ins()
                    .load(types::I64, MemFlags::new(), param_val, 0);
                builder.ins().call(rc_inc_ref, &[data_word]);
            } else {
                builder.ins().call(rc_inc_ref, &[param_val]);
            }
        }

        let size = type_id_size(
            param_type_id,
            ptr_type,
            env.analyzed.entity_registry(),
            arena,
        );
        let size_val = builder.ins().iconst(types::I64, size as i64);

        let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = builder.inst_results(alloc_call)[0];

        builder.ins().store(MemFlags::new(), param_val, heap_ptr, 0);

        let index_val = builder.ins().iconst(types::I64, i as i64);
        builder
            .ins()
            .call(set_capture_ref, &[closure_ptr, index_val, heap_ptr]);

        // Set capture kind so closure_drop knows which captures need cleanup.
        // Interface captures use kind=2 so closure_drop loads the data_ptr
        // from the fat pointer before calling rc_dec.
        let kind: i64 = if is_interface {
            2 // CAPTURE_KIND_INTERFACE
        } else if is_rc {
            1 // CAPTURE_KIND_RC
        } else {
            0 // CAPTURE_KIND_VALUE
        };
        let kind_val = builder.ins().iconst(types::I8, kind);
        builder
            .ins()
            .call(set_kind_ref, &[closure_ptr, index_val, kind_val]);

        let size_i32 = builder.ins().iconst(types::I32, size as i64);
        builder
            .ins()
            .call(set_size_ref, &[closure_ptr, index_val, size_i32]);
    }

    Ok(closure_ptr)
}
