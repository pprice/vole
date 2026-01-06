use cranelift::prelude::*;
use cranelift_module::Module;

use crate::codegen::types::{
    CompileCtx, CompiledValue, native_type_to_cranelift, type_to_cranelift,
};
use crate::runtime::native_registry::NativeType;
use crate::sema::Type;
use crate::sema::implement_registry::ExternalMethodInfo;

/// Compile a call to an external native function.
/// This is used for methods marked with external blocks.
pub(crate) fn compile_external_call(
    builder: &mut FunctionBuilder,
    ctx: &mut CompileCtx,
    external_info: &ExternalMethodInfo,
    args: &[Value],
    return_type: &Type,
) -> Result<CompiledValue, String> {
    // Look up the native function in the registry
    let native_func = ctx
        .native_registry
        .lookup(&external_info.module_path, &external_info.native_name)
        .ok_or_else(|| {
            format!(
                "Native function {}::{} not found in registry",
                external_info.module_path, external_info.native_name
            )
        })?;

    // Build the Cranelift signature from NativeSignature
    let mut sig = ctx.module.make_signature();
    for param_type in &native_func.signature.params {
        sig.params.push(AbiParam::new(native_type_to_cranelift(
            param_type,
            ctx.pointer_type,
        )));
    }
    if native_func.signature.return_type != NativeType::Nil {
        sig.returns.push(AbiParam::new(native_type_to_cranelift(
            &native_func.signature.return_type,
            ctx.pointer_type,
        )));
    }

    // Import the signature and emit an indirect call
    let sig_ref = builder.import_signature(sig);
    let func_ptr = native_func.ptr;

    // Load the function pointer as a constant
    let func_ptr_val = builder.ins().iconst(ctx.pointer_type, func_ptr as i64);

    // Emit the indirect call
    let call_inst = builder.ins().call_indirect(sig_ref, func_ptr_val, args);
    let results = builder.inst_results(call_inst);

    if results.is_empty() {
        Ok(CompiledValue::void(builder))
    } else {
        Ok(CompiledValue {
            value: results[0],
            ty: type_to_cranelift(return_type, ctx.pointer_type),
            vole_type: return_type.clone(),
        })
    }
}
