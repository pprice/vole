// type_utils.rs
//
// Free functions for type promotion rules, shared between sema and codegen.

use crate::type_arena::TypeId;

/// Get the result type for numeric binary operations (wider type wins).
/// Float > integer, wider > narrower. This is the canonical promotion rule
/// used by both sema type-checking and codegen.
pub fn numeric_result_type(left: TypeId, right: TypeId) -> TypeId {
    // Float types take precedence, wider float wins
    if left == TypeId::F128 || right == TypeId::F128 {
        TypeId::F128
    } else if left == TypeId::F64 || right == TypeId::F64 {
        TypeId::F64
    } else if left == TypeId::F32 || right == TypeId::F32 {
        TypeId::F32
    } else {
        // Both are integers - use integer promotion rules
        integer_result_type(left, right)
    }
}

/// Get the result type for integer binary operations (wider type wins).
/// Follows C-like promotion: smaller types widen to larger types.
/// Sub-32-bit types (i8, i16, u8, u16) always promote to i32.
pub fn integer_result_type(left: TypeId, right: TypeId) -> TypeId {
    // i128 is widest
    if left == TypeId::I128 || right == TypeId::I128 {
        TypeId::I128
    }
    // 64-bit types
    else if left == TypeId::I64
        || right == TypeId::I64
        || left == TypeId::U64
        || right == TypeId::U64
    {
        // If mixing signed/unsigned 64-bit, result is i64
        TypeId::I64
    }
    // 32-bit and smaller types all promote to i32
    else {
        TypeId::I32
    }
}
