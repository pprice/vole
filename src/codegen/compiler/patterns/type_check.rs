// src/codegen/compiler/patterns/type_check.rs

use cranelift::prelude::*;

use crate::codegen::types::CompiledValue;
use crate::sema::Type;

pub(crate) fn compile_type_pattern_check(
    builder: &mut FunctionBuilder,
    scrutinee: &CompiledValue,
    pattern_type: &Type,
) -> Option<Value> {
    if let Type::Union(variants) = &scrutinee.vole_type {
        let expected_tag = variants
            .iter()
            .position(|v| v == pattern_type)
            .unwrap_or(usize::MAX);

        if expected_tag == usize::MAX {
            // Pattern type not in union - will never match
            let never_match = builder.ins().iconst(types::I8, 0);
            return Some(never_match);
        }

        let tag = builder
            .ins()
            .load(types::I8, MemFlags::new(), scrutinee.value, 0);
        let expected = builder.ins().iconst(types::I8, expected_tag as i64);
        let result = builder.ins().icmp(IntCC::Equal, tag, expected);

        Some(result)
    } else {
        // Non-union scrutinee - pattern matches if types are equal
        if scrutinee.vole_type == *pattern_type {
            None // Always matches
        } else {
            // Never matches
            let never_match = builder.ins().iconst(types::I8, 0);
            Some(never_match)
        }
    }
}
