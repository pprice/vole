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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_arena::TypeId;

    // Shorthand aliases for the 12 numeric TypeId constants.
    const I8: TypeId = TypeId::I8;
    const I16: TypeId = TypeId::I16;
    const I32: TypeId = TypeId::I32;
    const I64: TypeId = TypeId::I64;
    const I128: TypeId = TypeId::I128;
    const U8: TypeId = TypeId::U8;
    const U16: TypeId = TypeId::U16;
    const U32: TypeId = TypeId::U32;
    const U64: TypeId = TypeId::U64;
    const F32: TypeId = TypeId::F32;
    const F64: TypeId = TypeId::F64;
    const F128: TypeId = TypeId::F128;

    // =========================================================================
    // Test 1: promotion_rules — all 144 pairs (12 × 12)
    //
    // The 12 numeric TypeIds:
    //   I8, I16, I32, I64, I128, U8, U16, U32, U64, F32, F64, F128
    //
    // Rules (applied in order):
    //   1. Either F128  → F128
    //   2. Either F64   → F64
    //   3. Either F32   → F32
    //   4. Either I128  → I128
    //   5. Any 64-bit   → I64
    //   6. Both U32     → U32; any other 32-bit mix → I32
    //   7. Both U16     → U16; any other 16-bit mix → I32
    //   8. Both U8      → U8
    //   9. Otherwise    → I32  (I8 homogeneous or mixed 8-bit)
    // =========================================================================

    fn p(a: TypeId, b: TypeId) -> TypeId {
        numeric_result_type(a, b)
    }

    // ---- Row I8 × {all 12} ----
    #[test]
    fn promotion_i8_row() {
        // I8 × I8: mixed 8-bit with signed → I32 (default)
        assert_eq!(p(I8, I8), I32);
        // I8 × I16: 16-bit involved, mixed → I32
        assert_eq!(p(I8, I16), I32);
        // I8 × I32: 32-bit involved, not both U32 → I32
        assert_eq!(p(I8, I32), I32);
        // I8 × I64: 64-bit involved → I64
        assert_eq!(p(I8, I64), I64);
        // I8 × I128: I128 present → I128
        assert_eq!(p(I8, I128), I128);
        // I8 × U8: mixed 8-bit (I8+U8) → I32
        assert_eq!(p(I8, U8), I32);
        // I8 × U16: 16-bit involved, mixed → I32
        assert_eq!(p(I8, U16), I32);
        // I8 × U32: 32-bit involved, not both U32 → I32
        assert_eq!(p(I8, U32), I32);
        // I8 × U64: 64-bit involved → I64
        assert_eq!(p(I8, U64), I64);
        // I8 × F32: float present → F32
        assert_eq!(p(I8, F32), F32);
        // I8 × F64: float present → F64
        assert_eq!(p(I8, F64), F64);
        // I8 × F128: float present → F128
        assert_eq!(p(I8, F128), F128);
    }

    // ---- Row I16 × {all 12} ----
    #[test]
    fn promotion_i16_row() {
        // I16 × I8: 16-bit mix → I32
        assert_eq!(p(I16, I8), I32);
        // I16 × I16: 16-bit, mixed (I16 is signed, not both U16) → I32
        assert_eq!(p(I16, I16), I32);
        // I16 × I32: 32-bit involved, not both U32 → I32
        assert_eq!(p(I16, I32), I32);
        // I16 × I64: 64-bit → I64
        assert_eq!(p(I16, I64), I64);
        // I16 × I128: → I128
        assert_eq!(p(I16, I128), I128);
        // I16 × U8: 16-bit mix → I32
        assert_eq!(p(I16, U8), I32);
        // I16 × U16: 16-bit mix (not both U16) → I32
        assert_eq!(p(I16, U16), I32);
        // I16 × U32: 32-bit, not both U32 → I32
        assert_eq!(p(I16, U32), I32);
        // I16 × U64: 64-bit → I64
        assert_eq!(p(I16, U64), I64);
        // I16 × F32: → F32
        assert_eq!(p(I16, F32), F32);
        // I16 × F64: → F64
        assert_eq!(p(I16, F64), F64);
        // I16 × F128: → F128
        assert_eq!(p(I16, F128), F128);
    }

    // ---- Row I32 × {all 12} ----
    #[test]
    fn promotion_i32_row() {
        assert_eq!(p(I32, I8), I32);
        assert_eq!(p(I32, I16), I32);
        assert_eq!(p(I32, I32), I32);
        assert_eq!(p(I32, I64), I64);
        assert_eq!(p(I32, I128), I128);
        assert_eq!(p(I32, U8), I32);
        assert_eq!(p(I32, U16), I32);
        // I32 × U32: 32-bit, not both U32 → I32
        assert_eq!(p(I32, U32), I32);
        assert_eq!(p(I32, U64), I64);
        assert_eq!(p(I32, F32), F32);
        assert_eq!(p(I32, F64), F64);
        assert_eq!(p(I32, F128), F128);
    }

    // ---- Row I64 × {all 12} ----
    #[test]
    fn promotion_i64_row() {
        assert_eq!(p(I64, I8), I64);
        assert_eq!(p(I64, I16), I64);
        assert_eq!(p(I64, I32), I64);
        assert_eq!(p(I64, I64), I64);
        assert_eq!(p(I64, I128), I128);
        assert_eq!(p(I64, U8), I64);
        assert_eq!(p(I64, U16), I64);
        assert_eq!(p(I64, U32), I64);
        // I64 × U64: 64-bit → I64
        assert_eq!(p(I64, U64), I64);
        // Float dominates int:
        assert_eq!(p(I64, F32), F32);
        assert_eq!(p(I64, F64), F64);
        assert_eq!(p(I64, F128), F128);
    }

    // ---- Row I128 × {all 12} ----
    #[test]
    fn promotion_i128_row() {
        assert_eq!(p(I128, I8), I128);
        assert_eq!(p(I128, I16), I128);
        assert_eq!(p(I128, I32), I128);
        assert_eq!(p(I128, I64), I128);
        assert_eq!(p(I128, I128), I128);
        assert_eq!(p(I128, U8), I128);
        assert_eq!(p(I128, U16), I128);
        assert_eq!(p(I128, U32), I128);
        assert_eq!(p(I128, U64), I128);
        // Float still dominates I128:
        assert_eq!(p(I128, F32), F32);
        assert_eq!(p(I128, F64), F64);
        assert_eq!(p(I128, F128), F128);
    }

    // ---- Row U8 × {all 12} ----
    #[test]
    fn promotion_u8_row() {
        // U8 × I8: mixed 8-bit → I32
        assert_eq!(p(U8, I8), I32);
        // U8 × I16: 16-bit mix → I32
        assert_eq!(p(U8, I16), I32);
        // U8 × I32: 32-bit → I32
        assert_eq!(p(U8, I32), I32);
        // U8 × I64: 64-bit → I64
        assert_eq!(p(U8, I64), I64);
        // U8 × I128: → I128
        assert_eq!(p(U8, I128), I128);
        // U8 × U8: both U8 → U8
        assert_eq!(p(U8, U8), U8);
        // U8 × U16: 16-bit, not both U16 → I32
        assert_eq!(p(U8, U16), I32);
        // U8 × U32: 32-bit, not both U32 → I32
        assert_eq!(p(U8, U32), I32);
        // U8 × U64: 64-bit → I64
        assert_eq!(p(U8, U64), I64);
        assert_eq!(p(U8, F32), F32);
        assert_eq!(p(U8, F64), F64);
        assert_eq!(p(U8, F128), F128);
    }

    // ---- Row U16 × {all 12} ----
    #[test]
    fn promotion_u16_row() {
        // U16 × I8: 16-bit mix → I32
        assert_eq!(p(U16, I8), I32);
        // U16 × I16: 16-bit, not both U16 → I32
        assert_eq!(p(U16, I16), I32);
        // U16 × I32: 32-bit → I32
        assert_eq!(p(U16, I32), I32);
        // U16 × I64: 64-bit → I64
        assert_eq!(p(U16, I64), I64);
        // U16 × I128: → I128
        assert_eq!(p(U16, I128), I128);
        // U16 × U8: 16-bit, not both U16 → I32
        assert_eq!(p(U16, U8), I32);
        // U16 × U16: both U16 → U16
        assert_eq!(p(U16, U16), U16);
        // U16 × U32: 32-bit, not both U32 → I32
        assert_eq!(p(U16, U32), I32);
        // U16 × U64: 64-bit → I64
        assert_eq!(p(U16, U64), I64);
        assert_eq!(p(U16, F32), F32);
        assert_eq!(p(U16, F64), F64);
        assert_eq!(p(U16, F128), F128);
    }

    // ---- Row U32 × {all 12} ----
    #[test]
    fn promotion_u32_row() {
        // U32 × I8: 32-bit, not both U32 → I32
        assert_eq!(p(U32, I8), I32);
        // U32 × I16: 32-bit → I32
        assert_eq!(p(U32, I16), I32);
        // U32 × I32: 32-bit, not both U32 → I32
        assert_eq!(p(U32, I32), I32);
        // U32 × I64: 64-bit → I64
        assert_eq!(p(U32, I64), I64);
        // U32 × I128: → I128
        assert_eq!(p(U32, I128), I128);
        // U32 × U8: 32-bit, not both U32 → I32
        assert_eq!(p(U32, U8), I32);
        // U32 × U16: 32-bit, not both U32 → I32
        assert_eq!(p(U32, U16), I32);
        // U32 × U32: both U32 → U32
        assert_eq!(p(U32, U32), U32);
        // U32 × U64: 64-bit → I64
        assert_eq!(p(U32, U64), I64);
        assert_eq!(p(U32, F32), F32);
        assert_eq!(p(U32, F64), F64);
        assert_eq!(p(U32, F128), F128);
    }

    // ---- Row U64 × {all 12} ----
    #[test]
    fn promotion_u64_row() {
        assert_eq!(p(U64, I8), I64);
        assert_eq!(p(U64, I16), I64);
        assert_eq!(p(U64, I32), I64);
        // U64 × I64: 64-bit → I64
        assert_eq!(p(U64, I64), I64);
        // U64 × I128: → I128
        assert_eq!(p(U64, I128), I128);
        assert_eq!(p(U64, U8), I64);
        assert_eq!(p(U64, U16), I64);
        assert_eq!(p(U64, U32), I64);
        // U64 × U64: 64-bit → I64 (mixed goes to I64; U64+U64 also hits the 64-bit branch)
        assert_eq!(p(U64, U64), I64);
        assert_eq!(p(U64, F32), F32);
        assert_eq!(p(U64, F64), F64);
        assert_eq!(p(U64, F128), F128);
    }

    // ---- Row F32 × {all 12} ----
    #[test]
    fn promotion_f32_row() {
        assert_eq!(p(F32, I8), F32);
        assert_eq!(p(F32, I16), F32);
        assert_eq!(p(F32, I32), F32);
        assert_eq!(p(F32, I64), F32);
        assert_eq!(p(F32, I128), F32);
        assert_eq!(p(F32, U8), F32);
        assert_eq!(p(F32, U16), F32);
        assert_eq!(p(F32, U32), F32);
        assert_eq!(p(F32, U64), F32);
        assert_eq!(p(F32, F32), F32);
        // F32 × F64: F64 present → F64
        assert_eq!(p(F32, F64), F64);
        // F32 × F128: F128 present → F128
        assert_eq!(p(F32, F128), F128);
    }

    // ---- Row F64 × {all 12} ----
    #[test]
    fn promotion_f64_row() {
        assert_eq!(p(F64, I8), F64);
        assert_eq!(p(F64, I16), F64);
        assert_eq!(p(F64, I32), F64);
        assert_eq!(p(F64, I64), F64);
        assert_eq!(p(F64, I128), F64);
        assert_eq!(p(F64, U8), F64);
        assert_eq!(p(F64, U16), F64);
        assert_eq!(p(F64, U32), F64);
        assert_eq!(p(F64, U64), F64);
        // F64 × F32: F64 present → F64
        assert_eq!(p(F64, F32), F64);
        assert_eq!(p(F64, F64), F64);
        // F64 × F128: F128 present → F128
        assert_eq!(p(F64, F128), F128);
    }

    // ---- Row F128 × {all 12} ----
    #[test]
    fn promotion_f128_row() {
        assert_eq!(p(F128, I8), F128);
        assert_eq!(p(F128, I16), F128);
        assert_eq!(p(F128, I32), F128);
        assert_eq!(p(F128, I64), F128);
        assert_eq!(p(F128, I128), F128);
        assert_eq!(p(F128, U8), F128);
        assert_eq!(p(F128, U16), F128);
        assert_eq!(p(F128, U32), F128);
        assert_eq!(p(F128, U64), F128);
        assert_eq!(p(F128, F32), F128);
        assert_eq!(p(F128, F64), F128);
        assert_eq!(p(F128, F128), F128);
    }

    // ---- Symmetry: numeric_result_type(A, B) == numeric_result_type(B, A) ----
    #[test]
    fn promotion_symmetry() {
        let types = [I8, I16, I32, I64, I128, U8, U16, U32, U64, F32, F64, F128];
        for &a in &types {
            for &b in &types {
                assert_eq!(
                    numeric_result_type(a, b),
                    numeric_result_type(b, a),
                    "symmetry failed for {a:?} × {b:?}"
                );
            }
        }
    }

    // =========================================================================
    // Test 2: coercion_kinds — all valid directed pairs
    //
    // Identity: A → A (all 12 types)
    // IntWiden: from narrower int to wider int; signed = source signedness
    //   signed src: I8→{I16,I32,I64,I128}, I16→{I32,I64,I128}, I32→{I64,I128}, I64→I128
    //   unsigned src: U8→{I16,I32,I64,I128,U16,U32,U64},
    //                 U16→{I32,I64,I128,U32,U64}, U32→{I64,I128,U64}, U64→I128
    // IntNarrow: from wider int to narrower int; signed = source signedness
    //   signed src: I128→{I64,I32,I16,I8}, I64→{I32,I16,I8}, I32→{I16,I8}, I16→I8
    //   unsigned src: U64→{U32,U16,U8}, U32→{U16,U8}, U16→U8
    //   cross: I128→{U64,U32,U16,U8}, I64→{U32,U16,U8}, I32→{U16,U8}, I16→U8
    //          U64→{I64,I32,I16,I8}, U32→{I32,I16,I8}, U16→{I16,I8}, U8→I8
    // FloatWiden: F32→F64, F32→F128, F64→F128
    // FloatNarrow: F64→F32, F128→F64, F128→F32
    // IntToFloat: int→float (all int × float combos)
    // FloatToInt: float→int (all float × int combos)
    // =========================================================================

    fn c(from: TypeId, to: TypeId) -> NumericCoercion {
        numeric_coercion(from, to)
    }

    // ---- Identity (A → A) ----
    #[test]
    fn coercion_identity() {
        for ty in [I8, I16, I32, I64, I128, U8, U16, U32, U64, F32, F64, F128] {
            assert_eq!(
                c(ty, ty),
                NumericCoercion::Identity,
                "identity failed for {ty:?}"
            );
        }
    }

    // ---- IntWiden: signed source (sign-extend) ----
    #[test]
    fn coercion_int_widen_signed_source() {
        // I8 → wider signed
        assert_eq!(c(I8, I16), NumericCoercion::IntWiden { signed: true });
        assert_eq!(c(I8, I32), NumericCoercion::IntWiden { signed: true });
        assert_eq!(c(I8, I64), NumericCoercion::IntWiden { signed: true });
        assert_eq!(c(I8, I128), NumericCoercion::IntWiden { signed: true });
        // I16 → wider signed
        assert_eq!(c(I16, I32), NumericCoercion::IntWiden { signed: true });
        assert_eq!(c(I16, I64), NumericCoercion::IntWiden { signed: true });
        assert_eq!(c(I16, I128), NumericCoercion::IntWiden { signed: true });
        // I32 → wider signed
        assert_eq!(c(I32, I64), NumericCoercion::IntWiden { signed: true });
        assert_eq!(c(I32, I128), NumericCoercion::IntWiden { signed: true });
        // I64 → wider signed
        assert_eq!(c(I64, I128), NumericCoercion::IntWiden { signed: true });
    }

    // ---- IntWiden: unsigned source (zero-extend), into wider unsigned ----
    #[test]
    fn coercion_int_widen_unsigned_to_unsigned() {
        // U8 → wider unsigned
        assert_eq!(c(U8, U16), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U8, U32), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U8, U64), NumericCoercion::IntWiden { signed: false });
        // U16 → wider unsigned
        assert_eq!(c(U16, U32), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U16, U64), NumericCoercion::IntWiden { signed: false });
        // U32 → wider unsigned
        assert_eq!(c(U32, U64), NumericCoercion::IntWiden { signed: false });
    }

    // ---- IntWiden: unsigned source (zero-extend), into wider signed ----
    // This is the vol-b3p7 class of bug: U32→I64 must zero-extend.
    #[test]
    fn coercion_int_widen_unsigned_to_signed() {
        // U8 into wider signed
        assert_eq!(c(U8, I16), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U8, I32), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U8, I64), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U8, I128), NumericCoercion::IntWiden { signed: false });
        // U16 into wider signed
        assert_eq!(c(U16, I32), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U16, I64), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U16, I128), NumericCoercion::IntWiden { signed: false });
        // U32 into wider signed — the critical vol-b3p7 case
        assert_eq!(c(U32, I64), NumericCoercion::IntWiden { signed: false });
        assert_eq!(c(U32, I128), NumericCoercion::IntWiden { signed: false });
        // U64 into wider signed
        assert_eq!(c(U64, I128), NumericCoercion::IntWiden { signed: false });
    }

    // ---- IntNarrow: signed source (truncate) ----
    #[test]
    fn coercion_int_narrow_signed_source() {
        // I128 → narrower signed
        assert_eq!(c(I128, I64), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I128, I32), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I128, I16), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I128, I8), NumericCoercion::IntNarrow { signed: true });
        // I64 → narrower signed
        assert_eq!(c(I64, I32), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I64, I16), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I64, I8), NumericCoercion::IntNarrow { signed: true });
        // I32 → narrower signed
        assert_eq!(c(I32, I16), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I32, I8), NumericCoercion::IntNarrow { signed: true });
        // I16 → narrower signed
        assert_eq!(c(I16, I8), NumericCoercion::IntNarrow { signed: true });
    }

    // ---- IntNarrow: unsigned source (truncate) ----
    #[test]
    fn coercion_int_narrow_unsigned_source() {
        // U64 → narrower unsigned
        assert_eq!(c(U64, U32), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U64, U16), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U64, U8), NumericCoercion::IntNarrow { signed: false });
        // U32 → narrower unsigned
        assert_eq!(c(U32, U16), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U32, U8), NumericCoercion::IntNarrow { signed: false });
        // U16 → narrower unsigned
        assert_eq!(c(U16, U8), NumericCoercion::IntNarrow { signed: false });
    }

    // ---- IntNarrow: signed source → narrower unsigned ----
    #[test]
    fn coercion_int_narrow_signed_to_unsigned() {
        // I128 → unsigned (narrower)
        assert_eq!(c(I128, U64), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I128, U32), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I128, U16), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I128, U8), NumericCoercion::IntNarrow { signed: true });
        // I64 → unsigned (narrower)
        assert_eq!(c(I64, U32), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I64, U16), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I64, U8), NumericCoercion::IntNarrow { signed: true });
        // I32 → unsigned (narrower)
        assert_eq!(c(I32, U16), NumericCoercion::IntNarrow { signed: true });
        assert_eq!(c(I32, U8), NumericCoercion::IntNarrow { signed: true });
        // I16 → unsigned (narrower)
        assert_eq!(c(I16, U8), NumericCoercion::IntNarrow { signed: true });
    }

    // ---- IntNarrow: unsigned source → narrower signed ----
    #[test]
    fn coercion_int_narrow_unsigned_to_signed() {
        // U64 → smaller signed
        assert_eq!(c(U64, I64), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U64, I32), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U64, I16), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U64, I8), NumericCoercion::IntNarrow { signed: false });
        // U32 → smaller signed
        assert_eq!(c(U32, I32), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U32, I16), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U32, I8), NumericCoercion::IntNarrow { signed: false });
        // U16 → smaller signed
        assert_eq!(c(U16, I16), NumericCoercion::IntNarrow { signed: false });
        assert_eq!(c(U16, I8), NumericCoercion::IntNarrow { signed: false });
        // U8 → smaller signed
        assert_eq!(c(U8, I8), NumericCoercion::IntNarrow { signed: false });
    }

    // ---- FloatWiden ----
    #[test]
    fn coercion_float_widen() {
        assert_eq!(c(F32, F64), NumericCoercion::FloatWiden);
        assert_eq!(c(F32, F128), NumericCoercion::FloatWiden);
        assert_eq!(c(F64, F128), NumericCoercion::FloatWiden);
    }

    // ---- FloatNarrow ----
    #[test]
    fn coercion_float_narrow() {
        assert_eq!(c(F64, F32), NumericCoercion::FloatNarrow);
        assert_eq!(c(F128, F64), NumericCoercion::FloatNarrow);
        assert_eq!(c(F128, F32), NumericCoercion::FloatNarrow);
    }

    // ---- IntToFloat: signed integer → float ----
    #[test]
    fn coercion_int_to_float_signed() {
        for src in [I8, I16, I32, I64, I128] {
            for dst in [F32, F64, F128] {
                assert_eq!(
                    c(src, dst),
                    NumericCoercion::IntToFloat { from_signed: true },
                    "{src:?} → {dst:?}"
                );
            }
        }
    }

    // ---- IntToFloat: unsigned integer → float ----
    #[test]
    fn coercion_int_to_float_unsigned() {
        for src in [U8, U16, U32, U64] {
            for dst in [F32, F64, F128] {
                assert_eq!(
                    c(src, dst),
                    NumericCoercion::IntToFloat { from_signed: false },
                    "{src:?} → {dst:?}"
                );
            }
        }
    }

    // ---- FloatToInt: float → signed integer ----
    #[test]
    fn coercion_float_to_int_signed() {
        for src in [F32, F64, F128] {
            for dst in [I8, I16, I32, I64, I128] {
                assert_eq!(
                    c(src, dst),
                    NumericCoercion::FloatToInt { to_signed: true },
                    "{src:?} → {dst:?}"
                );
            }
        }
    }

    // ---- FloatToInt: float → unsigned integer ----
    #[test]
    fn coercion_float_to_int_unsigned() {
        for src in [F32, F64, F128] {
            for dst in [U8, U16, U32, U64] {
                assert_eq!(
                    c(src, dst),
                    NumericCoercion::FloatToInt { to_signed: false },
                    "{src:?} → {dst:?}"
                );
            }
        }
    }
}
