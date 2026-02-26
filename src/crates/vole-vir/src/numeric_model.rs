// numeric_model.rs
//
// Numeric type promotion rules and related utilities shared by sema/codegen.

use vole_identity::TypeId;

/// The semantic kind of a numeric coercion from one type to another.
///
/// This enum describes *what* the coercion means semantically, without
/// prescribing any Cranelift instruction or IR detail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericCoercion {
    /// Source and target types are identical.
    Identity,
    /// Integer widening: target has more bits than source.
    IntWiden { signed: bool },
    /// Integer narrowing (truncation): target has fewer bits than source.
    IntNarrow { signed: bool },
    /// Float widening: F32->F64, F32->F128, or F64->F128.
    FloatWiden,
    /// Float narrowing: F64->F32, F128->F64, or F128->F32.
    FloatNarrow,
    /// Integer-to-float conversion.
    IntToFloat { from_signed: bool },
    /// Float-to-integer conversion.
    FloatToInt { to_signed: bool },
}

/// Helper: float width ordering (F32 < F64 < F128).
#[inline]
fn float_width(ty: TypeId) -> Option<u8> {
    match ty {
        TypeId::F32 => Some(0),
        TypeId::F64 => Some(1),
        TypeId::F128 => Some(2),
        _ => None,
    }
}

/// Return the semantic coercion kind required to convert a value of type
/// `from` to `to`.
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
pub fn numeric_result_type(left: TypeId, right: TypeId) -> TypeId {
    if left == TypeId::F128 || right == TypeId::F128 {
        TypeId::F128
    } else if left == TypeId::F64 || right == TypeId::F64 {
        TypeId::F64
    } else if left == TypeId::F32 || right == TypeId::F32 {
        TypeId::F32
    } else {
        integer_result_type(left, right)
    }
}

/// Get the result type for integer binary operations (wider type wins).
pub fn integer_result_type(left: TypeId, right: TypeId) -> TypeId {
    if left == TypeId::I128 || right == TypeId::I128 {
        TypeId::I128
    } else if left == TypeId::I64
        || right == TypeId::I64
        || left == TypeId::U64
        || right == TypeId::U64
    {
        TypeId::I64
    } else if left == TypeId::I32
        || right == TypeId::I32
        || left == TypeId::U32
        || right == TypeId::U32
    {
        if left == TypeId::U32 && right == TypeId::U32 {
            TypeId::U32
        } else {
            TypeId::I32
        }
    } else if left == TypeId::I16
        || right == TypeId::I16
        || left == TypeId::U16
        || right == TypeId::U16
    {
        if left == TypeId::U16 && right == TypeId::U16 {
            TypeId::U16
        } else {
            TypeId::I32
        }
    } else if left == TypeId::U8 && right == TypeId::U8 {
        TypeId::U8
    } else {
        TypeId::I32
    }
}
