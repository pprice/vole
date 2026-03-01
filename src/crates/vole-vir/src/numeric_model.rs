// numeric_model.rs
//
// Numeric type promotion rules and related utilities shared by sema/codegen.

use vole_identity::{TypeId, VirTypeId};

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

// =========================================================================
// VirTypeId overloads
//
// Identical promotion/coercion logic using VirTypeId constants instead of
// sema TypeId.  These exist so downstream codegen callers can operate on
// VirTypeId directly without bridging through cv_type_id().
// =========================================================================

/// Helper: float width ordering for VirTypeId (F32 < F64 < F128).
#[inline]
fn float_width_v(ty: VirTypeId) -> Option<u8> {
    match ty {
        VirTypeId::F32 => Some(0),
        VirTypeId::F64 => Some(1),
        VirTypeId::F128 => Some(2),
        _ => None,
    }
}

/// VirTypeId version of [`numeric_coercion`].
#[allow(dead_code)] // Convenience for downstream VIR migration tickets.
pub fn numeric_coercion_v(from: VirTypeId, to: VirTypeId) -> NumericCoercion {
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
        let from_rank = float_width_v(from).expect("from is float");
        let to_rank = float_width_v(to).expect("to is float");
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
            "numeric_coercion_v called with non-numeric types: from={from:?}, to={to:?}"
        );
        NumericCoercion::FloatToInt {
            to_signed: to.is_signed_int(),
        }
    }
}

/// VirTypeId version of [`numeric_result_type`].
#[allow(dead_code)] // Convenience for downstream VIR migration tickets.
pub fn numeric_result_type_v(left: VirTypeId, right: VirTypeId) -> VirTypeId {
    if left == VirTypeId::F128 || right == VirTypeId::F128 {
        VirTypeId::F128
    } else if left == VirTypeId::F64 || right == VirTypeId::F64 {
        VirTypeId::F64
    } else if left == VirTypeId::F32 || right == VirTypeId::F32 {
        VirTypeId::F32
    } else {
        integer_result_type_v(left, right)
    }
}

/// VirTypeId version of [`integer_result_type`].
#[allow(dead_code)] // Convenience for downstream VIR migration tickets.
pub fn integer_result_type_v(left: VirTypeId, right: VirTypeId) -> VirTypeId {
    if left == VirTypeId::I128 || right == VirTypeId::I128 {
        VirTypeId::I128
    } else if left == VirTypeId::I64
        || right == VirTypeId::I64
        || left == VirTypeId::U64
        || right == VirTypeId::U64
    {
        VirTypeId::I64
    } else if left == VirTypeId::I32
        || right == VirTypeId::I32
        || left == VirTypeId::U32
        || right == VirTypeId::U32
    {
        if left == VirTypeId::U32 && right == VirTypeId::U32 {
            VirTypeId::U32
        } else {
            VirTypeId::I32
        }
    } else if left == VirTypeId::I16
        || right == VirTypeId::I16
        || left == VirTypeId::U16
        || right == VirTypeId::U16
    {
        if left == VirTypeId::U16 && right == VirTypeId::U16 {
            VirTypeId::U16
        } else {
            VirTypeId::I32
        }
    } else if left == VirTypeId::U8 && right == VirTypeId::U8 {
        VirTypeId::U8
    } else {
        VirTypeId::I32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Parallel TypeId/VirTypeId constant pairs for exhaustive cross-checking.
    const PAIRS: [(TypeId, VirTypeId); 12] = [
        (TypeId::I8, VirTypeId::I8),
        (TypeId::I16, VirTypeId::I16),
        (TypeId::I32, VirTypeId::I32),
        (TypeId::I64, VirTypeId::I64),
        (TypeId::I128, VirTypeId::I128),
        (TypeId::U8, VirTypeId::U8),
        (TypeId::U16, VirTypeId::U16),
        (TypeId::U32, VirTypeId::U32),
        (TypeId::U64, VirTypeId::U64),
        (TypeId::F32, VirTypeId::F32),
        (TypeId::F64, VirTypeId::F64),
        (TypeId::F128, VirTypeId::F128),
    ];

    /// Map a TypeId result back to its VirTypeId equivalent for comparison.
    fn to_vir(ty: TypeId) -> VirTypeId {
        PAIRS
            .iter()
            .find(|(t, _)| *t == ty)
            .unwrap_or_else(|| panic!("unmapped TypeId: {ty:?}"))
            .1
    }

    // =================================================================
    // numeric_result_type_v — exhaustive 144-pair cross-check
    // =================================================================

    #[test]
    fn result_type_v_matches_all_144_pairs() {
        for &(t_a, v_a) in &PAIRS {
            for &(t_b, v_b) in &PAIRS {
                let expected = to_vir(numeric_result_type(t_a, t_b));
                let actual = numeric_result_type_v(v_a, v_b);
                assert_eq!(
                    actual, expected,
                    "numeric_result_type_v mismatch for ({v_a:?}, {v_b:?})"
                );
            }
        }
    }

    #[test]
    fn result_type_v_symmetry() {
        for &(_, v_a) in &PAIRS {
            for &(_, v_b) in &PAIRS {
                assert_eq!(
                    numeric_result_type_v(v_a, v_b),
                    numeric_result_type_v(v_b, v_a),
                    "symmetry failed for ({v_a:?}, {v_b:?})"
                );
            }
        }
    }

    // =================================================================
    // numeric_coercion_v — exhaustive 144-pair cross-check
    // =================================================================

    #[test]
    fn coercion_v_matches_all_144_pairs() {
        for &(t_a, v_a) in &PAIRS {
            for &(t_b, v_b) in &PAIRS {
                let expected = numeric_coercion(t_a, t_b);
                let actual = numeric_coercion_v(v_a, v_b);
                assert_eq!(
                    actual, expected,
                    "numeric_coercion_v mismatch for ({v_a:?} -> {v_b:?})"
                );
            }
        }
    }

    // =================================================================
    // integer_result_type_v — all integer pairs (81 = 9 × 9)
    // =================================================================

    #[test]
    fn integer_result_type_v_matches_all_81_pairs() {
        let int_pairs: Vec<_> = PAIRS.iter().filter(|(t, _)| t.is_integer()).collect();
        for &(t_a, v_a) in &int_pairs {
            for &(t_b, v_b) in &int_pairs {
                let expected = to_vir(integer_result_type(*t_a, *t_b));
                let actual = integer_result_type_v(*v_a, *v_b);
                assert_eq!(
                    actual, expected,
                    "integer_result_type_v mismatch for ({v_a:?}, {v_b:?})"
                );
            }
        }
    }
}
