use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use std::collections::HashMap;

use super::super::patterns::compile_expr;
use crate::codegen::types::{
    CompileCtx, CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, FALLIBLE_TAG_OFFSET,
    type_to_cranelift,
};
use crate::errors::CodegenError;
use crate::frontend::{Expr, Symbol};
use crate::sema::Type;

pub(crate) fn compile_try_propagate(
    builder: &mut FunctionBuilder,
    inner: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Compile the inner fallible expression
    let fallible = compile_expr(builder, inner, variables, ctx)?;

    // Get type info
    let success_type = match &fallible.vole_type {
        Type::Fallible(ft) => (*ft.success_type).clone(),
        _ => {
            return Err(CodegenError::type_mismatch(
                "try operator",
                "fallible type",
                "non-fallible",
            )
            .into());
        }
    };

    // Load the tag
    let tag = builder.ins().load(
        types::I64,
        MemFlags::new(),
        fallible.value,
        FALLIBLE_TAG_OFFSET,
    );

    // Check if success (tag == 0)
    let is_success = builder
        .ins()
        .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

    // Create blocks
    let success_block = builder.create_block();
    let error_block = builder.create_block();
    let merge_block = builder.create_block();

    // Get payload type for success
    let payload_ty = type_to_cranelift(&success_type, ctx.pointer_type);
    builder.append_block_param(merge_block, payload_ty);

    // Branch based on tag
    builder
        .ins()
        .brif(is_success, success_block, &[], error_block, &[]);

    // Error block: propagate by returning the fallible value
    builder.switch_to_block(error_block);
    builder.seal_block(error_block);
    builder.ins().return_(&[fallible.value]);

    // Success block: extract payload and jump to merge
    builder.switch_to_block(success_block);
    builder.seal_block(success_block);
    let payload = builder.ins().load(
        payload_ty,
        MemFlags::new(),
        fallible.value,
        FALLIBLE_PAYLOAD_OFFSET,
    );
    let payload_arg = BlockArg::from(payload);
    builder.ins().jump(merge_block, &[payload_arg]);

    // Merge block: continue with extracted value
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);
    let result = builder.block_params(merge_block)[0];

    Ok(CompiledValue {
        value: result,
        ty: payload_ty,
        vole_type: success_type,
    })
}
