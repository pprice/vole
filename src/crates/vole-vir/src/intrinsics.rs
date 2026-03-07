// intrinsics.rs
//
// Typed intrinsic key enum shared between VIR and codegen.
//
// This is the canonical definition of `IntrinsicKey`.  Codegen re-exports it
// so existing call sites do not need to change their imports.

// =============================================================================
// Macros for generating integer intrinsic enums and registration
// =============================================================================

/// Macro for defining integer operation enums with type-prefixed variants.
///
/// Usage:
/// ```ignore
/// define_int_op_enum! {
///     /// Doc comment for the enum.
///     pub enum UnaryIntOp {
///         signed: [Abs],                    // Only i8, i16, i32, i64
///         all: [Clz, Ctz, Popcnt, Bitrev],  // All 8 integer types
///     }
/// }
/// ```
#[macro_export]
macro_rules! define_int_op_enum {
    // Only signed operations
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $name:ident {
            signed: [$($signed_op:ident),* $(,)?] $(,)?
        }
    ) => {
        $crate::paste::paste! {
            $(#[$enum_meta])*
            #[derive(Debug, Clone, Copy)]
            $vis enum $name {
                $(
                    [<I8 $signed_op>],
                    [<I16 $signed_op>],
                    [<I32 $signed_op>],
                    [<I64 $signed_op>],
                )*
            }
        }
    };
    // Only all operations
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $name:ident {
            all: [$($all_op:ident),* $(,)?] $(,)?
        }
    ) => {
        $crate::paste::paste! {
            $(#[$enum_meta])*
            #[derive(Debug, Clone, Copy)]
            $vis enum $name {
                $(
                    [<I8 $all_op>],
                    [<I16 $all_op>],
                    [<I32 $all_op>],
                    [<I64 $all_op>],
                    [<U8 $all_op>],
                    [<U16 $all_op>],
                    [<U32 $all_op>],
                    [<U64 $all_op>],
                )*
            }
        }
    };
    // Both signed and all operations
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $name:ident {
            signed: [$($signed_op:ident),* $(,)?],
            all: [$($all_op:ident),* $(,)?] $(,)?
        }
    ) => {
        $crate::paste::paste! {
            $(#[$enum_meta])*
            #[derive(Debug, Clone, Copy)]
            $vis enum $name {
                // Signed-only variants
                $(
                    [<I8 $signed_op>],
                    [<I16 $signed_op>],
                    [<I32 $signed_op>],
                    [<I64 $signed_op>],
                )*
                // All-type variants
                $(
                    [<I8 $all_op>],
                    [<I16 $all_op>],
                    [<I32 $all_op>],
                    [<I64 $all_op>],
                    [<U8 $all_op>],
                    [<U16 $all_op>],
                    [<U32 $all_op>],
                    [<U64 $all_op>],
                )*
            }
        }
    };
}

/// A typed key identifying an intrinsic function.
///
/// One variant per intrinsic; no heap allocation. String names only appear at
/// the boundary where Vole names map to typed keys (see `try_from_name`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntrinsicKey {
    // ---- Float constants ----
    F32Nan,
    F32Infinity,
    F32NegInfinity,
    F32Epsilon,
    F64Nan,
    F64Infinity,
    F64NegInfinity,
    F64Epsilon,

    // ---- Unary float ops ----
    F32Sqrt,
    F64Sqrt,
    F32Abs,
    F64Abs,
    F32Ceil,
    F64Ceil,
    F32Floor,
    F64Floor,
    F32Trunc,
    F64Trunc,
    F32Round,
    F64Round,

    // ---- Binary float ops ----
    F32Min,
    F64Min,
    F32Max,
    F64Max,

    // ---- Unary integer ops (signed-only: abs) ----
    I8Abs,
    I16Abs,
    I32Abs,
    I64Abs,

    // ---- Unary integer ops (all types: clz, ctz, popcnt, bitrev) ----
    I8Clz,
    I16Clz,
    I32Clz,
    I64Clz,
    U8Clz,
    U16Clz,
    U32Clz,
    U64Clz,

    I8Ctz,
    I16Ctz,
    I32Ctz,
    I64Ctz,
    U8Ctz,
    U16Ctz,
    U32Ctz,
    U64Ctz,

    I8Popcnt,
    I16Popcnt,
    I32Popcnt,
    I64Popcnt,
    U8Popcnt,
    U16Popcnt,
    U32Popcnt,
    U64Popcnt,

    I8Bitrev,
    I16Bitrev,
    I32Bitrev,
    I64Bitrev,
    U8Bitrev,
    U16Bitrev,
    U32Bitrev,
    U64Bitrev,

    // ---- Binary integer ops (all types) ----
    I8Min,
    I16Min,
    I32Min,
    I64Min,
    U8Min,
    U16Min,
    U32Min,
    U64Min,

    I8Max,
    I16Max,
    I32Max,
    I64Max,
    U8Max,
    U16Max,
    U32Max,
    U64Max,

    I8Rotl,
    I16Rotl,
    I32Rotl,
    I64Rotl,
    U8Rotl,
    U16Rotl,
    U32Rotl,
    U64Rotl,

    I8Rotr,
    I16Rotr,
    I32Rotr,
    I64Rotr,
    U8Rotr,
    U16Rotr,
    U32Rotr,
    U64Rotr,

    I8WrappingAdd,
    I16WrappingAdd,
    I32WrappingAdd,
    I64WrappingAdd,
    U8WrappingAdd,
    U16WrappingAdd,
    U32WrappingAdd,
    U64WrappingAdd,

    I8WrappingSub,
    I16WrappingSub,
    I32WrappingSub,
    I64WrappingSub,
    U8WrappingSub,
    U16WrappingSub,
    U32WrappingSub,
    U64WrappingSub,

    I8WrappingMul,
    I16WrappingMul,
    I32WrappingMul,
    I64WrappingMul,
    U8WrappingMul,
    U16WrappingMul,
    U32WrappingMul,
    U64WrappingMul,

    // ---- Unary integer wrapping ops (signed-only: wrapping_neg) ----
    I8WrappingNeg,
    I16WrappingNeg,
    I32WrappingNeg,
    I64WrappingNeg,

    // ---- Saturating integer ops (all types) ----
    I8SaturatingAdd,
    I16SaturatingAdd,
    I32SaturatingAdd,
    I64SaturatingAdd,
    U8SaturatingAdd,
    U16SaturatingAdd,
    U32SaturatingAdd,
    U64SaturatingAdd,

    I8SaturatingSub,
    I16SaturatingSub,
    I32SaturatingSub,
    I64SaturatingSub,
    U8SaturatingSub,
    U16SaturatingSub,
    U32SaturatingSub,
    U64SaturatingSub,

    I8SaturatingMul,
    I16SaturatingMul,
    I32SaturatingMul,
    I64SaturatingMul,
    U8SaturatingMul,
    U16SaturatingMul,
    U32SaturatingMul,
    U64SaturatingMul,

    // ---- Checked integer ops (all types) ----
    I8CheckedAdd,
    I16CheckedAdd,
    I32CheckedAdd,
    I64CheckedAdd,
    U8CheckedAdd,
    U16CheckedAdd,
    U32CheckedAdd,
    U64CheckedAdd,

    I8CheckedSub,
    I16CheckedSub,
    I32CheckedSub,
    I64CheckedSub,
    U8CheckedSub,
    U16CheckedSub,
    U32CheckedSub,
    U64CheckedSub,

    I8CheckedMul,
    I16CheckedMul,
    I32CheckedMul,
    I64CheckedMul,
    U8CheckedMul,
    U16CheckedMul,
    U32CheckedMul,
    U64CheckedMul,

    I8CheckedDiv,
    I16CheckedDiv,
    I32CheckedDiv,
    I64CheckedDiv,
    U8CheckedDiv,
    U16CheckedDiv,
    U32CheckedDiv,
    U64CheckedDiv,

    // ---- Builtins ----
    Panic,
    Assert,
    PrintChar,
    ArrayLen,
    StringLen,

    // ---- Task intrinsics ----
    TaskChannelSend,
    TaskChannelRecv,
    TaskChannelTryRecv,
    TaskJoin,
    TaskRun,
}

impl IntrinsicKey {
    /// Boundary translation: map a Vole intrinsic name string to a typed key.
    ///
    /// Returns `None` if the string does not correspond to any known intrinsic.
    /// This is the single place where strings enter the intrinsic system;
    /// all internal code uses `IntrinsicKey` variants directly.
    pub fn try_from_name(s: &str) -> Option<Self> {
        Some(match s {
            // Float constants
            "f32_nan" => Self::F32Nan,
            "f32_infinity" => Self::F32Infinity,
            "f32_neg_infinity" => Self::F32NegInfinity,
            "f32_epsilon" => Self::F32Epsilon,
            "f64_nan" => Self::F64Nan,
            "f64_infinity" => Self::F64Infinity,
            "f64_neg_infinity" => Self::F64NegInfinity,
            "f64_epsilon" => Self::F64Epsilon,
            // Unary float ops
            "f32_sqrt" => Self::F32Sqrt,
            "f64_sqrt" => Self::F64Sqrt,
            "f32_abs" => Self::F32Abs,
            "f64_abs" => Self::F64Abs,
            "f32_ceil" => Self::F32Ceil,
            "f64_ceil" => Self::F64Ceil,
            "f32_floor" => Self::F32Floor,
            "f64_floor" => Self::F64Floor,
            "f32_trunc" => Self::F32Trunc,
            "f64_trunc" => Self::F64Trunc,
            "f32_round" => Self::F32Round,
            "f64_round" => Self::F64Round,
            // Binary float ops
            "f32_min" => Self::F32Min,
            "f64_min" => Self::F64Min,
            "f32_max" => Self::F32Max,
            "f64_max" => Self::F64Max,
            // Unary integer ops - abs (signed only)
            "i8_abs" => Self::I8Abs,
            "i16_abs" => Self::I16Abs,
            "i32_abs" => Self::I32Abs,
            "i64_abs" => Self::I64Abs,
            // Unary integer ops - clz
            "i8_clz" => Self::I8Clz,
            "i16_clz" => Self::I16Clz,
            "i32_clz" => Self::I32Clz,
            "i64_clz" => Self::I64Clz,
            "u8_clz" => Self::U8Clz,
            "u16_clz" => Self::U16Clz,
            "u32_clz" => Self::U32Clz,
            "u64_clz" => Self::U64Clz,
            // Unary integer ops - ctz
            "i8_ctz" => Self::I8Ctz,
            "i16_ctz" => Self::I16Ctz,
            "i32_ctz" => Self::I32Ctz,
            "i64_ctz" => Self::I64Ctz,
            "u8_ctz" => Self::U8Ctz,
            "u16_ctz" => Self::U16Ctz,
            "u32_ctz" => Self::U32Ctz,
            "u64_ctz" => Self::U64Ctz,
            // Unary integer ops - popcnt
            "i8_popcnt" => Self::I8Popcnt,
            "i16_popcnt" => Self::I16Popcnt,
            "i32_popcnt" => Self::I32Popcnt,
            "i64_popcnt" => Self::I64Popcnt,
            "u8_popcnt" => Self::U8Popcnt,
            "u16_popcnt" => Self::U16Popcnt,
            "u32_popcnt" => Self::U32Popcnt,
            "u64_popcnt" => Self::U64Popcnt,
            // Unary integer ops - bitrev
            "i8_bitrev" => Self::I8Bitrev,
            "i16_bitrev" => Self::I16Bitrev,
            "i32_bitrev" => Self::I32Bitrev,
            "i64_bitrev" => Self::I64Bitrev,
            "u8_bitrev" => Self::U8Bitrev,
            "u16_bitrev" => Self::U16Bitrev,
            "u32_bitrev" => Self::U32Bitrev,
            "u64_bitrev" => Self::U64Bitrev,
            // Binary integer ops - min
            "i8_min" => Self::I8Min,
            "i16_min" => Self::I16Min,
            "i32_min" => Self::I32Min,
            "i64_min" => Self::I64Min,
            "u8_min" => Self::U8Min,
            "u16_min" => Self::U16Min,
            "u32_min" => Self::U32Min,
            "u64_min" => Self::U64Min,
            // Binary integer ops - max
            "i8_max" => Self::I8Max,
            "i16_max" => Self::I16Max,
            "i32_max" => Self::I32Max,
            "i64_max" => Self::I64Max,
            "u8_max" => Self::U8Max,
            "u16_max" => Self::U16Max,
            "u32_max" => Self::U32Max,
            "u64_max" => Self::U64Max,
            // Binary integer ops - rotl
            "i8_rotl" => Self::I8Rotl,
            "i16_rotl" => Self::I16Rotl,
            "i32_rotl" => Self::I32Rotl,
            "i64_rotl" => Self::I64Rotl,
            "u8_rotl" => Self::U8Rotl,
            "u16_rotl" => Self::U16Rotl,
            "u32_rotl" => Self::U32Rotl,
            "u64_rotl" => Self::U64Rotl,
            // Binary integer ops - rotr
            "i8_rotr" => Self::I8Rotr,
            "i16_rotr" => Self::I16Rotr,
            "i32_rotr" => Self::I32Rotr,
            "i64_rotr" => Self::I64Rotr,
            "u8_rotr" => Self::U8Rotr,
            "u16_rotr" => Self::U16Rotr,
            "u32_rotr" => Self::U32Rotr,
            "u64_rotr" => Self::U64Rotr,
            // Binary integer ops - wrapping_add
            "i8_wrapping_add" => Self::I8WrappingAdd,
            "i16_wrapping_add" => Self::I16WrappingAdd,
            "i32_wrapping_add" => Self::I32WrappingAdd,
            "i64_wrapping_add" => Self::I64WrappingAdd,
            "u8_wrapping_add" => Self::U8WrappingAdd,
            "u16_wrapping_add" => Self::U16WrappingAdd,
            "u32_wrapping_add" => Self::U32WrappingAdd,
            "u64_wrapping_add" => Self::U64WrappingAdd,
            // Binary integer ops - wrapping_sub
            "i8_wrapping_sub" => Self::I8WrappingSub,
            "i16_wrapping_sub" => Self::I16WrappingSub,
            "i32_wrapping_sub" => Self::I32WrappingSub,
            "i64_wrapping_sub" => Self::I64WrappingSub,
            "u8_wrapping_sub" => Self::U8WrappingSub,
            "u16_wrapping_sub" => Self::U16WrappingSub,
            "u32_wrapping_sub" => Self::U32WrappingSub,
            "u64_wrapping_sub" => Self::U64WrappingSub,
            // Binary integer ops - wrapping_mul
            "i8_wrapping_mul" => Self::I8WrappingMul,
            "i16_wrapping_mul" => Self::I16WrappingMul,
            "i32_wrapping_mul" => Self::I32WrappingMul,
            "i64_wrapping_mul" => Self::I64WrappingMul,
            "u8_wrapping_mul" => Self::U8WrappingMul,
            "u16_wrapping_mul" => Self::U16WrappingMul,
            "u32_wrapping_mul" => Self::U32WrappingMul,
            "u64_wrapping_mul" => Self::U64WrappingMul,
            // Unary integer wrapping ops - wrapping_neg (signed only)
            "i8_wrapping_neg" => Self::I8WrappingNeg,
            "i16_wrapping_neg" => Self::I16WrappingNeg,
            "i32_wrapping_neg" => Self::I32WrappingNeg,
            "i64_wrapping_neg" => Self::I64WrappingNeg,
            // Saturating ops - saturating_add
            "i8_saturating_add" => Self::I8SaturatingAdd,
            "i16_saturating_add" => Self::I16SaturatingAdd,
            "i32_saturating_add" => Self::I32SaturatingAdd,
            "i64_saturating_add" => Self::I64SaturatingAdd,
            "u8_saturating_add" => Self::U8SaturatingAdd,
            "u16_saturating_add" => Self::U16SaturatingAdd,
            "u32_saturating_add" => Self::U32SaturatingAdd,
            "u64_saturating_add" => Self::U64SaturatingAdd,
            // Saturating ops - saturating_sub
            "i8_saturating_sub" => Self::I8SaturatingSub,
            "i16_saturating_sub" => Self::I16SaturatingSub,
            "i32_saturating_sub" => Self::I32SaturatingSub,
            "i64_saturating_sub" => Self::I64SaturatingSub,
            "u8_saturating_sub" => Self::U8SaturatingSub,
            "u16_saturating_sub" => Self::U16SaturatingSub,
            "u32_saturating_sub" => Self::U32SaturatingSub,
            "u64_saturating_sub" => Self::U64SaturatingSub,
            // Saturating ops - saturating_mul
            "i8_saturating_mul" => Self::I8SaturatingMul,
            "i16_saturating_mul" => Self::I16SaturatingMul,
            "i32_saturating_mul" => Self::I32SaturatingMul,
            "i64_saturating_mul" => Self::I64SaturatingMul,
            "u8_saturating_mul" => Self::U8SaturatingMul,
            "u16_saturating_mul" => Self::U16SaturatingMul,
            "u32_saturating_mul" => Self::U32SaturatingMul,
            "u64_saturating_mul" => Self::U64SaturatingMul,
            // Checked ops - checked_add
            "i8_checked_add" => Self::I8CheckedAdd,
            "i16_checked_add" => Self::I16CheckedAdd,
            "i32_checked_add" => Self::I32CheckedAdd,
            "i64_checked_add" => Self::I64CheckedAdd,
            "u8_checked_add" => Self::U8CheckedAdd,
            "u16_checked_add" => Self::U16CheckedAdd,
            "u32_checked_add" => Self::U32CheckedAdd,
            "u64_checked_add" => Self::U64CheckedAdd,
            // Checked ops - checked_sub
            "i8_checked_sub" => Self::I8CheckedSub,
            "i16_checked_sub" => Self::I16CheckedSub,
            "i32_checked_sub" => Self::I32CheckedSub,
            "i64_checked_sub" => Self::I64CheckedSub,
            "u8_checked_sub" => Self::U8CheckedSub,
            "u16_checked_sub" => Self::U16CheckedSub,
            "u32_checked_sub" => Self::U32CheckedSub,
            "u64_checked_sub" => Self::U64CheckedSub,
            // Checked ops - checked_mul
            "i8_checked_mul" => Self::I8CheckedMul,
            "i16_checked_mul" => Self::I16CheckedMul,
            "i32_checked_mul" => Self::I32CheckedMul,
            "i64_checked_mul" => Self::I64CheckedMul,
            "u8_checked_mul" => Self::U8CheckedMul,
            "u16_checked_mul" => Self::U16CheckedMul,
            "u32_checked_mul" => Self::U32CheckedMul,
            "u64_checked_mul" => Self::U64CheckedMul,
            // Checked ops - checked_div
            "i8_checked_div" => Self::I8CheckedDiv,
            "i16_checked_div" => Self::I16CheckedDiv,
            "i32_checked_div" => Self::I32CheckedDiv,
            "i64_checked_div" => Self::I64CheckedDiv,
            "u8_checked_div" => Self::U8CheckedDiv,
            "u16_checked_div" => Self::U16CheckedDiv,
            "u32_checked_div" => Self::U32CheckedDiv,
            "u64_checked_div" => Self::U64CheckedDiv,
            // Builtins
            "panic" => Self::Panic,
            "assert" => Self::Assert,
            "print_char" => Self::PrintChar,
            "array_len" => Self::ArrayLen,
            "string_len" => Self::StringLen,
            // Task intrinsics
            "task_channel_send" => Self::TaskChannelSend,
            "task_channel_recv" => Self::TaskChannelRecv,
            "task_channel_try_recv" => Self::TaskChannelTryRecv,
            "task_join" => Self::TaskJoin,
            "task_run" => Self::TaskRun,
            _ => return None,
        })
    }

    /// Boundary translation: map a composite key from two name parts.
    ///
    /// This is called at the boundary where Vole type/method names arrive as strings.
    /// Internal code should use enum variants directly.
    /// Returns `None` if the combined name does not correspond to any known intrinsic.
    pub fn from_names(type_name: &str, method_name: &str) -> Option<Self> {
        let combined = format!("{}_{}", type_name, method_name);
        Self::try_from_name(combined.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_str_boundary_roundtrip() {
        // Verify the boundary translation works for all known keys
        assert_eq!(
            IntrinsicKey::try_from_name("f32_nan"),
            Some(IntrinsicKey::F32Nan)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("f64_infinity"),
            Some(IntrinsicKey::F64Infinity)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("panic"),
            Some(IntrinsicKey::Panic)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("array_len"),
            Some(IntrinsicKey::ArrayLen)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("string_len"),
            Some(IntrinsicKey::StringLen)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("i32_abs"),
            Some(IntrinsicKey::I32Abs)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("u64_wrapping_add"),
            Some(IntrinsicKey::U64WrappingAdd)
        );
        assert_eq!(
            IntrinsicKey::try_from_name("i64_checked_div"),
            Some(IntrinsicKey::I64CheckedDiv)
        );
        // Unknown key returns None (no panic)
        assert_eq!(IntrinsicKey::try_from_name("nonexistent_intrinsic"), None);
    }

    #[test]
    fn test_from_names_composite() {
        assert_eq!(
            IntrinsicKey::from_names("f32", "nan"),
            Some(IntrinsicKey::F32Nan)
        );
        assert_eq!(
            IntrinsicKey::from_names("f64", "infinity"),
            Some(IntrinsicKey::F64Infinity)
        );
        assert_eq!(
            IntrinsicKey::from_names("i32", "abs"),
            Some(IntrinsicKey::I32Abs)
        );
        assert_eq!(IntrinsicKey::from_names("nonexistent", "method"), None);
    }
}
