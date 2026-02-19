// numeric_model.rs
//
// Numeric type promotion rules and related utilities, shared between sema and codegen.

use crate::type_arena::TypeId;

/// The semantic kind of a numeric coercion from one type to another.
///
/// This enum describes *what* the coercion means semantically, without
/// prescribing any Cranelift instruction or IR detail. Codegen consults this
/// to select the correct instruction for each case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericCoercion {
    /// Source and target types are identical — no operation needed.
    Identity,
    /// Integer widening: target has more bits than source.
    /// `signed` reflects whether the *source* type is signed (i.e. whether to
    /// sign-extend or zero-extend). U32→I64 is `IntWiden { signed: false }`
    /// because we zero-extend the unsigned source regardless of the target sign.
    IntWiden { signed: bool },
    /// Integer narrowing (truncation): target has fewer bits than source.
    /// `signed` reflects the signedness of the *source* type (semantic truth).
    IntNarrow { signed: bool },
    /// Float widening: F32→F64, F32→F128, or F64→F128.
    FloatWiden,
    /// Float narrowing: F64→F32, F128→F64, or F128→F32.
    FloatNarrow,
    /// Integer-to-float conversion.
    /// `from_signed` is true when the source integer type is signed.
    IntToFloat { from_signed: bool },
    /// Float-to-integer conversion.
    /// `to_signed` is true when the target integer type is signed.
    FloatToInt { to_signed: bool },
}

/// Helper: float width ordering (F32 < F64 < F128).
/// Returns None for non-float types.
#[inline]
fn float_width(ty: TypeId) -> Option<u8> {
    match ty {
        TypeId::F32 => Some(0),
        TypeId::F64 => Some(1),
        TypeId::F128 => Some(2),
        _ => None,
    }
}

/// Return the semantic coercion kind required to convert a value of type `from`
/// to type `to`.
///
/// Callers are responsible for ensuring that `from` and `to` are both numeric
/// types and that the conversion is valid. Passing non-numeric or non-coercible
/// pairs will panic in debug builds.
pub fn numeric_coercion(from: TypeId, to: TypeId) -> NumericCoercion {
    if from == to {
        return NumericCoercion::Identity;
    }

    let from_is_int = from.is_integer();
    let to_is_int = to.is_integer();
    let from_is_float = from.is_float();
    let to_is_float = to.is_float();

    if from_is_int && to_is_int {
        let from_bits = from.integer_bit_width();
        let to_bits = to.integer_bit_width();
        if to_bits > from_bits {
            NumericCoercion::IntWiden {
                signed: from.is_signed_int(),
            }
        } else {
            NumericCoercion::IntNarrow {
                signed: from.is_signed_int(),
            }
        }
    } else if from_is_float && to_is_float {
        let from_rank = float_width(from).expect("from is float");
        let to_rank = float_width(to).expect("to is float");
        if to_rank > from_rank {
            NumericCoercion::FloatWiden
        } else {
            NumericCoercion::FloatNarrow
        }
    } else if from_is_int && to_is_float {
        NumericCoercion::IntToFloat {
            from_signed: from.is_signed_int(),
        }
    } else {
        debug_assert!(
            from_is_float && to_is_int,
            "numeric_coercion called with non-numeric types: from={from:?}, to={to:?}"
        );
        NumericCoercion::FloatToInt {
            to_signed: to.is_signed_int(),
        }
    }
}

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
