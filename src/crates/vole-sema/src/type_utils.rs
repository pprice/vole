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
/// Homogeneous unsigned operations (u8+u8, u16+u16, u32+u32) preserve the
/// unsigned type; mixed-sign or mixed-width operations widen to the signed
/// equivalent of the larger width.
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
    // 32-bit types
    else if left == TypeId::I32
        || right == TypeId::I32
        || left == TypeId::U32
        || right == TypeId::U32
    {
        // Homogeneous u32 preserves unsigned; any other mix goes to i32
        if left == TypeId::U32 && right == TypeId::U32 {
            TypeId::U32
        } else {
            TypeId::I32
        }
    }
    // 16-bit types
    else if left == TypeId::I16
        || right == TypeId::I16
        || left == TypeId::U16
        || right == TypeId::U16
    {
        // Homogeneous u16 preserves unsigned; mixed goes to i32 (integer promotion)
        if left == TypeId::U16 && right == TypeId::U16 {
            TypeId::U16
        } else {
            TypeId::I32
        }
    }
    // 8-bit types
    else if left == TypeId::U8 && right == TypeId::U8 {
        TypeId::U8
    }
    // Default: i8 or mixed 8-bit → i32 (standard integer promotion)
    else {
        TypeId::I32
    }
}
