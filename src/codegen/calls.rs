// src/codegen/calls.rs
//
// Call-related utilities for code generation.
// This module contains standalone helper functions for string operations and value conversion
// that don't depend on compile_expr.
//
// Note: The main call compilation functions (compile_call, compile_println, compile_assert,
// compile_indirect_call, etc.) remain in compiler.rs due to circular dependencies with
// compile_expr. This module extracts the standalone helpers that don't have such dependencies.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};

use crate::sema::Type;

use super::types::CompiledValue;

/// Compile a string literal by calling vole_string_new
pub(crate) fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: types::Type,
    module: &mut JITModule,
    func_ids: &HashMap<String, FuncId>,
) -> Result<CompiledValue, String> {
    // Get the vole_string_new function
    let func_id = func_ids
        .get("vole_string_new")
        .ok_or_else(|| "vole_string_new not found".to_string())?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

    // Pass the string data pointer and length as constants
    // The string is a Rust &str, so we can get its pointer and length
    let data_ptr = s.as_ptr() as i64;
    let len = s.len() as i64;

    let data_val = builder.ins().iconst(pointer_type, data_ptr);
    let len_val = builder.ins().iconst(pointer_type, len);

    // Call vole_string_new(data, len) -> *mut RcString
    let call = builder.ins().call(func_ref, &[data_val, len_val]);
    let result = builder.inst_results(call)[0];

    Ok(CompiledValue {
        value: result,
        ty: pointer_type,
        vole_type: Type::String,
    })
}

/// Convert a compiled value to a string by calling the appropriate vole_*_to_string function
pub(crate) fn value_to_string(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    _pointer_type: types::Type,
    module: &mut JITModule,
    func_ids: &HashMap<String, FuncId>,
) -> Result<Value, String> {
    // If already a string, return as-is
    if matches!(val.vole_type, Type::String) {
        return Ok(val.value);
    }

    let (func_name, call_val) = if val.ty == types::F64 {
        ("vole_f64_to_string", val.value)
    } else if val.ty == types::I8 {
        ("vole_bool_to_string", val.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if val.ty.is_int() && val.ty != types::I64 {
            builder.ins().sextend(types::I64, val.value)
        } else {
            val.value
        };
        ("vole_i64_to_string", extended)
    };

    let func_id = func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

    let call = builder.ins().call(func_ref, &[call_val]);
    Ok(builder.inst_results(call)[0])
}
