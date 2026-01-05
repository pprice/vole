// src/codegen/compiler/strings.rs
//
// String interpolation codegen.

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::patterns::compile_expr;
use crate::codegen::calls::{compile_string_literal, value_to_string};
use crate::codegen::types::{CompileCtx, CompiledValue};
use crate::frontend::{StringPart, Symbol};
use crate::sema::Type;

pub(crate) fn compile_interpolated_string(
    builder: &mut FunctionBuilder,
    parts: &[StringPart],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if parts.is_empty() {
        // Empty interpolated string - return empty string
        return compile_string_literal(builder, "", ctx.pointer_type, ctx.module, ctx.func_ids);
    }

    // Convert each part to a string value
    let mut string_values: Vec<Value> = Vec::new();
    for part in parts {
        let str_val = match part {
            StringPart::Literal(s) => {
                compile_string_literal(builder, s, ctx.pointer_type, ctx.module, ctx.func_ids)?
                    .value
            }
            StringPart::Expr(expr) => {
                let compiled = compile_expr(builder, expr, variables, ctx)?;
                value_to_string(
                    builder,
                    compiled,
                    ctx.pointer_type,
                    ctx.module,
                    ctx.func_ids,
                )?
            }
        };
        string_values.push(str_val);
    }

    // Concatenate all parts
    if string_values.len() == 1 {
        return Ok(CompiledValue {
            value: string_values[0],
            ty: ctx.pointer_type,
            vole_type: Type::String,
        });
    }

    let concat_func_id = ctx
        .func_ids
        .get("vole_string_concat")
        .ok_or_else(|| "vole_string_concat not found".to_string())?;
    let concat_func_ref = ctx
        .module
        .declare_func_in_func(*concat_func_id, builder.func);

    let mut result = string_values[0];
    for &next in &string_values[1..] {
        let call = builder.ins().call(concat_func_ref, &[result, next]);
        result = builder.inst_results(call)[0];
    }

    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::String,
    })
}
