use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use std::collections::HashMap;

use super::super::patterns::compile_expr;
use crate::codegen::RuntimeFn;
use crate::codegen::types::{CompileCtx, CompiledValue};
use crate::frontend::{Expr, Symbol};
use crate::sema::Type;

fn runtime_func_id(ctx: &CompileCtx, runtime: RuntimeFn) -> Result<FuncId, String> {
    ctx.func_registry
        .runtime_key(runtime)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| format!("{} not found", runtime.name()))
}

/// Compile Iterator.map(fn) -> creates a MapIterator
pub(super) fn compile_iterator_map(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    _elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("map expects 1 argument, got {}", args.len()));
    }

    // Compile the transform function (should be a lambda/closure)
    let transform = compile_expr(builder, &args[0], variables, ctx)?;

    // The transform should be a function
    let (output_type, is_closure) = match &transform.vole_type {
        Type::Function(ft) => ((*ft.return_type).clone(), ft.is_closure),
        _ => {
            return Err(format!(
                "map argument must be a function, got {:?}",
                transform.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        transform.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = runtime_func_id(ctx, RuntimeFn::ClosureAlloc)?;
        let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[transform.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_map_iter(source_iter, transform_closure)
    let func_id = runtime_func_id(ctx, RuntimeFn::MapIter)?;
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, closure_ptr]);
    let result = builder.inst_results(call)[0];

    // MapIterator is stored as IteratorKind::Map internally
    // For now, we track that it's a mapped iterator in the vole_type
    // The collect method will need to check which kind of iterator it is
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::MapIterator(Box::new(output_type)),
    })
}

/// Compile Iterator.filter(fn) -> creates a FilterIterator
pub(super) fn compile_iterator_filter(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("filter expects 1 argument, got {}", args.len()));
    }

    // Compile the predicate function (should be a lambda/closure)
    let predicate = compile_expr(builder, &args[0], variables, ctx)?;

    // The predicate should be a function returning bool
    let is_closure = match &predicate.vole_type {
        Type::Function(ft) => ft.is_closure,
        _ => {
            return Err(format!(
                "filter argument must be a function, got {:?}",
                predicate.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        predicate.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = runtime_func_id(ctx, RuntimeFn::ClosureAlloc)?;
        let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[predicate.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_filter_iter(source_iter, predicate_closure)
    let func_id = runtime_func_id(ctx, RuntimeFn::FilterIter)?;
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, closure_ptr]);
    let result = builder.inst_results(call)[0];

    // FilterIterator preserves element type
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::FilterIterator(Box::new(elem_ty.clone())),
    })
}

/// Compile Iterator.take(n) -> creates a TakeIterator
pub(super) fn compile_iterator_take(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("take expects 1 argument, got {}", args.len()));
    }

    // Compile the count argument (should be an integer)
    let count = compile_expr(builder, &args[0], variables, ctx)?;

    // Call vole_take_iter(source_iter, count)
    let func_id = runtime_func_id(ctx, RuntimeFn::TakeIter)?;
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, count.value]);
    let result = builder.inst_results(call)[0];

    // TakeIterator preserves element type
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::TakeIterator(Box::new(elem_ty.clone())),
    })
}

/// Compile Iterator.skip(n) -> creates a SkipIterator
pub(super) fn compile_iterator_skip(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    elem_ty: &Type,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("skip expects 1 argument, got {}", args.len()));
    }

    // Compile the count argument (should be an integer)
    let count = compile_expr(builder, &args[0], variables, ctx)?;

    // Call vole_skip_iter(source_iter, count)
    let func_id = runtime_func_id(ctx, RuntimeFn::SkipIter)?;
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[iter_obj.value, count.value]);
    let result = builder.inst_results(call)[0];

    // SkipIterator preserves element type
    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::SkipIterator(Box::new(elem_ty.clone())),
    })
}

/// Compile Iterator.for_each(fn) -> calls function for each element, returns void
pub(super) fn compile_iterator_for_each(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err(format!("for_each expects 1 argument, got {}", args.len()));
    }

    // Compile the callback function (should be a lambda/closure)
    let callback = compile_expr(builder, &args[0], variables, ctx)?;

    // The callback should be a function
    let is_closure = match &callback.vole_type {
        Type::Function(ft) => ft.is_closure,
        _ => {
            return Err(format!(
                "for_each argument must be a function, got {:?}",
                callback.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        callback.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = runtime_func_id(ctx, RuntimeFn::ClosureAlloc)?;
        let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[callback.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_iter_for_each(iter, callback_closure)
    let func_id = runtime_func_id(ctx, RuntimeFn::IterForEach)?;
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    builder.ins().call(func_ref, &[iter_obj.value, closure_ptr]);

    // for_each returns void
    Ok(CompiledValue {
        value: builder.ins().iconst(types::I64, 0),
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile Iterator.reduce(init, fn) -> reduces iterator to single value
pub(super) fn compile_iterator_reduce(
    builder: &mut FunctionBuilder,
    iter_obj: &CompiledValue,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 2 {
        return Err(format!("reduce expects 2 arguments, got {}", args.len()));
    }

    // Compile the initial value
    let init = compile_expr(builder, &args[0], variables, ctx)?;

    // Compile the reducer function (should be a lambda/closure)
    let reducer = compile_expr(builder, &args[1], variables, ctx)?;

    // The reducer should be a function
    let is_closure = match &reducer.vole_type {
        Type::Function(ft) => ft.is_closure,
        _ => {
            return Err(format!(
                "reduce argument must be a function, got {:?}",
                reducer.vole_type
            ));
        }
    };

    // If it's a pure function (not a closure), wrap it in a closure structure
    // so the runtime can uniformly call it as a closure
    let closure_ptr = if is_closure {
        reducer.value
    } else {
        // Wrap pure function in a closure with 0 captures
        let alloc_id = runtime_func_id(ctx, RuntimeFn::ClosureAlloc)?;
        let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let alloc_call = builder.ins().call(alloc_ref, &[reducer.value, zero]);
        builder.inst_results(alloc_call)[0]
    };

    // Call vole_iter_reduce(iter, init, reducer_closure)
    let func_id = runtime_func_id(ctx, RuntimeFn::IterReduce)?;
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder
        .ins()
        .call(func_ref, &[iter_obj.value, init.value, closure_ptr]);
    let result = builder.inst_results(call)[0];

    // reduce returns the same type as init
    Ok(CompiledValue {
        value: result,
        ty: init.ty,
        vole_type: init.vole_type,
    })
}
