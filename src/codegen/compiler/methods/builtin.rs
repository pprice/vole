use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use crate::codegen::RuntimeFn;
use crate::codegen::types::{CompileCtx, CompiledValue};
use crate::sema::Type;

fn runtime_func_id(ctx: &CompileCtx, runtime: RuntimeFn) -> Result<FuncId, String> {
    ctx.func_registry
        .runtime_key(runtime)
        .and_then(|key| ctx.func_registry.func_id(key))
        .ok_or_else(|| format!("{} not found", runtime.name()))
}

/// Compile a built-in method call for primitive types
/// Returns Some(CompiledValue) if handled, None if not a built-in
pub(crate) fn compile_builtin_method(
    builder: &mut FunctionBuilder,
    obj: &CompiledValue,
    method_name: &str,
    ctx: &mut CompileCtx,
) -> Result<Option<CompiledValue>, String> {
    match (&obj.vole_type, method_name) {
        // Array.length() -> i64
        (Type::Array(_), "length") => {
            let func_id = runtime_func_id(ctx, RuntimeFn::ArrayLen)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        // String.length() -> i64
        (Type::String, "length") => {
            let func_id = runtime_func_id(ctx, RuntimeFn::StringLen)?;
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        _ => Ok(None),
    }
}
