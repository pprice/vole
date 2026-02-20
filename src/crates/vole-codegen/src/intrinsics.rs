//! Intrinsics registry for codegen.
//!
//! Provides a centralized registry mapping intrinsic keys to their codegen handlers.
//! This allows float intrinsics (nan, infinity, epsilon, etc.) to be looked up
//! and compiled in a uniform way.

use paste::paste;
use rustc_hash::FxHashMap;

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
macro_rules! define_int_op_enum {
    // Only signed operations
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $name:ident {
            signed: [$($signed_op:ident),* $(,)?] $(,)?
        }
    ) => {
        paste! {
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
        paste! {
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
        paste! {
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

/// Macro for registering integer intrinsics for all or signed-only types.
macro_rules! register_int_intrinsics {
    // All integer types
    ($self:ident, all, $handler:ident, $op:ident) => {
        paste! {
            $self.register(IntrinsicKey::[<I8 $op>], IntrinsicHandler::$handler($handler::[<I8 $op>]));
            $self.register(IntrinsicKey::[<I16 $op>], IntrinsicHandler::$handler($handler::[<I16 $op>]));
            $self.register(IntrinsicKey::[<I32 $op>], IntrinsicHandler::$handler($handler::[<I32 $op>]));
            $self.register(IntrinsicKey::[<I64 $op>], IntrinsicHandler::$handler($handler::[<I64 $op>]));
            $self.register(IntrinsicKey::[<U8 $op>], IntrinsicHandler::$handler($handler::[<U8 $op>]));
            $self.register(IntrinsicKey::[<U16 $op>], IntrinsicHandler::$handler($handler::[<U16 $op>]));
            $self.register(IntrinsicKey::[<U32 $op>], IntrinsicHandler::$handler($handler::[<U32 $op>]));
            $self.register(IntrinsicKey::[<U64 $op>], IntrinsicHandler::$handler($handler::[<U64 $op>]));
        }
    };
    // Signed integer types only
    ($self:ident, signed, $handler:ident, $op:ident) => {
        paste! {
            $self.register(IntrinsicKey::[<I8 $op>], IntrinsicHandler::$handler($handler::[<I8 $op>]));
            $self.register(IntrinsicKey::[<I16 $op>], IntrinsicHandler::$handler($handler::[<I16 $op>]));
            $self.register(IntrinsicKey::[<I32 $op>], IntrinsicHandler::$handler($handler::[<I32 $op>]));
            $self.register(IntrinsicKey::[<I64 $op>], IntrinsicHandler::$handler($handler::[<I64 $op>]));
        }
    };
}

/// A typed key identifying an intrinsic function.
///
/// One variant per intrinsic; no heap allocation. String names only appear at
/// the boundary where Vole names map to typed keys (see `From<&str>`).
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

/// Handler for generating IR for an intrinsic.
#[derive(Debug, Clone, Copy)]
pub enum IntrinsicHandler {
    /// Constant float value (nan, infinity, epsilon).
    FloatConstant(FloatConstant),
    /// Unary float operation (sqrt, abs, floor, ceil, etc.).
    UnaryFloatOp(UnaryFloatOp),
    /// Binary float operation (min, max).
    BinaryFloatOp(BinaryFloatOp),
    /// Unary integer operation (abs, clz, ctz, popcnt).
    UnaryIntOp(UnaryIntOp),
    /// Binary integer operation (min, max).
    BinaryIntOp(BinaryIntOp),
    /// Unary integer wrapping operation (wrapping_neg).
    UnaryIntWrappingOp(UnaryIntWrappingOp),
    /// Checked integer operation (returns Optional<T> - nil on overflow).
    CheckedIntOp(CheckedIntOp),
    /// Built-in panic: terminates execution with a message.
    BuiltinPanic,
    /// Inline array length read with runtime-compatible null semantics.
    BuiltinArrayLen,
    /// Inline UTF-8 string character count with runtime-compatible null semantics.
    BuiltinStringLen,
}

/// Unary float operations that take one argument and return a float.
#[derive(Debug, Clone, Copy)]
pub enum UnaryFloatOp {
    /// Square root (f32)
    F32Sqrt,
    /// Square root (f64)
    F64Sqrt,
    /// Absolute value (f32)
    F32Abs,
    /// Absolute value (f64)
    F64Abs,
    /// Ceiling - round up (f32)
    F32Ceil,
    /// Ceiling - round up (f64)
    F64Ceil,
    /// Floor - round down (f32)
    F32Floor,
    /// Floor - round down (f64)
    F64Floor,
    /// Truncate - round toward zero (f32)
    F32Trunc,
    /// Truncate - round toward zero (f64)
    F64Trunc,
    /// Round to nearest (f32)
    F32Round,
    /// Round to nearest (f64)
    F64Round,
}

/// Binary float operations that take two arguments and return a float.
#[derive(Debug, Clone, Copy)]
pub enum BinaryFloatOp {
    /// Minimum of two values (f32)
    F32Min,
    /// Minimum of two values (f64)
    F64Min,
    /// Maximum of two values (f32)
    F32Max,
    /// Maximum of two values (f64)
    F64Max,
}

define_int_op_enum! {
    /// Unary integer operations.
    pub enum UnaryIntOp {
        signed: [Abs],
        all: [Clz, Ctz, Popcnt, Bitrev],
    }
}

define_int_op_enum! {
    /// Binary integer operations.
    pub enum BinaryIntOp {
        all: [Min, Max, Rotl, Rotr, WrappingAdd, WrappingSub, WrappingMul,
              SaturatingAdd, SaturatingSub, SaturatingMul],
    }
}

define_int_op_enum! {
    /// Unary integer wrapping operations.
    #[expect(clippy::enum_variant_names)] // All variants are WrappingNeg by design for consistency
    pub enum UnaryIntWrappingOp {
        signed: [WrappingNeg],
    }
}

define_int_op_enum! {
    /// Checked integer operations (return Optional<T> - nil on overflow).
    pub enum CheckedIntOp {
        all: [CheckedAdd, CheckedSub, CheckedMul, CheckedDiv],
    }
}

/// Float constant intrinsic values.
#[derive(Debug, Clone, Copy)]
pub enum FloatConstant {
    /// f32::NAN
    F32Nan,
    /// f64::NAN
    F64Nan,
    /// f32::INFINITY
    F32Infinity,
    /// f64::INFINITY
    F64Infinity,
    /// f32::NEG_INFINITY
    F32NegInfinity,
    /// f64::NEG_INFINITY
    F64NegInfinity,
    /// f32::EPSILON
    F32Epsilon,
    /// f64::EPSILON
    F64Epsilon,
}

impl FloatConstant {
    /// Get the f32 value for this constant, if applicable.
    pub fn as_f32(self) -> Option<f32> {
        match self {
            FloatConstant::F32Nan => Some(f32::NAN),
            FloatConstant::F32Infinity => Some(f32::INFINITY),
            FloatConstant::F32NegInfinity => Some(f32::NEG_INFINITY),
            FloatConstant::F32Epsilon => Some(f32::EPSILON),
            FloatConstant::F64Nan
            | FloatConstant::F64Infinity
            | FloatConstant::F64NegInfinity
            | FloatConstant::F64Epsilon => None,
        }
    }

    /// Get the f64 value for this constant, if applicable.
    pub fn as_f64(self) -> Option<f64> {
        match self {
            FloatConstant::F64Nan => Some(f64::NAN),
            FloatConstant::F64Infinity => Some(f64::INFINITY),
            FloatConstant::F64NegInfinity => Some(f64::NEG_INFINITY),
            FloatConstant::F64Epsilon => Some(f64::EPSILON),
            FloatConstant::F32Nan
            | FloatConstant::F32Infinity
            | FloatConstant::F32NegInfinity
            | FloatConstant::F32Epsilon => None,
        }
    }

    /// Returns true if this is an f32 constant.
    pub fn is_f32(self) -> bool {
        matches!(
            self,
            FloatConstant::F32Nan
                | FloatConstant::F32Infinity
                | FloatConstant::F32NegInfinity
                | FloatConstant::F32Epsilon
        )
    }

    /// Returns true if this is an f64 constant.
    pub fn is_f64(self) -> bool {
        matches!(
            self,
            FloatConstant::F64Nan
                | FloatConstant::F64Infinity
                | FloatConstant::F64NegInfinity
                | FloatConstant::F64Epsilon
        )
    }
}

/// Registry for intrinsics, mapping keys to handlers.
pub struct IntrinsicsRegistry {
    handlers: FxHashMap<IntrinsicKey, IntrinsicHandler>,
}

impl Default for IntrinsicsRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl IntrinsicsRegistry {
    /// Create a new registry with all built-in intrinsics registered.
    pub fn new() -> Self {
        let mut registry = Self {
            handlers: FxHashMap::default(),
        };
        registry.register_float_intrinsics();
        registry.register_float_operations();
        registry.register_binary_float_operations();
        registry.register_int_operations();
        registry.register_binary_int_operations();
        registry.register_wrapping_int_operations();
        registry.register_saturating_int_operations();
        registry.register_checked_int_operations();
        registry.register_builtin_intrinsics();
        registry
    }

    /// Register a single intrinsic handler.
    pub fn register(&mut self, key: IntrinsicKey, handler: IntrinsicHandler) {
        self.handlers.insert(key, handler);
    }

    /// Look up an intrinsic by key.
    pub fn lookup(&self, key: &IntrinsicKey) -> Option<&IntrinsicHandler> {
        self.handlers.get(key)
    }

    /// Look up an intrinsic by type and method name.
    ///
    /// This is the boundary method for looking up by string names. Internal code
    /// should use `lookup` with a typed `IntrinsicKey` variant.
    pub fn lookup_by_names(&self, type_name: &str, method_name: &str) -> Option<&IntrinsicHandler> {
        let key = IntrinsicKey::from_names(type_name, method_name)?;
        self.lookup(&key)
    }

    /// Check if an intrinsic is registered.
    pub fn contains(&self, key: &IntrinsicKey) -> bool {
        self.handlers.contains_key(key)
    }

    /// Get the number of registered intrinsics.
    pub fn len(&self) -> usize {
        self.handlers.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.handlers.is_empty()
    }

    /// Register all built-in float intrinsics.
    fn register_float_intrinsics(&mut self) {
        use FloatConstant::*;
        use IntrinsicHandler::FloatConstant as FC;

        // f32 intrinsics
        self.register(IntrinsicKey::F32Nan, FC(F32Nan));
        self.register(IntrinsicKey::F32Infinity, FC(F32Infinity));
        self.register(IntrinsicKey::F32NegInfinity, FC(F32NegInfinity));
        self.register(IntrinsicKey::F32Epsilon, FC(F32Epsilon));

        // f64 intrinsics
        self.register(IntrinsicKey::F64Nan, FC(F64Nan));
        self.register(IntrinsicKey::F64Infinity, FC(F64Infinity));
        self.register(IntrinsicKey::F64NegInfinity, FC(F64NegInfinity));
        self.register(IntrinsicKey::F64Epsilon, FC(F64Epsilon));
    }

    /// Register float operation intrinsics (sqrt, abs, ceil, floor, trunc, round).
    fn register_float_operations(&mut self) {
        use IntrinsicHandler::UnaryFloatOp as UF;
        use UnaryFloatOp::*;

        // sqrt
        self.register(IntrinsicKey::F32Sqrt, UF(F32Sqrt));
        self.register(IntrinsicKey::F64Sqrt, UF(F64Sqrt));

        // abs
        self.register(IntrinsicKey::F32Abs, UF(F32Abs));
        self.register(IntrinsicKey::F64Abs, UF(F64Abs));

        // ceil
        self.register(IntrinsicKey::F32Ceil, UF(F32Ceil));
        self.register(IntrinsicKey::F64Ceil, UF(F64Ceil));

        // floor
        self.register(IntrinsicKey::F32Floor, UF(F32Floor));
        self.register(IntrinsicKey::F64Floor, UF(F64Floor));

        // trunc
        self.register(IntrinsicKey::F32Trunc, UF(F32Trunc));
        self.register(IntrinsicKey::F64Trunc, UF(F64Trunc));

        // round (nearest)
        self.register(IntrinsicKey::F32Round, UF(F32Round));
        self.register(IntrinsicKey::F64Round, UF(F64Round));
    }

    /// Register binary float operation intrinsics (min, max).
    fn register_binary_float_operations(&mut self) {
        use BinaryFloatOp::*;
        use IntrinsicHandler::BinaryFloatOp as BF;

        // min
        self.register(IntrinsicKey::F32Min, BF(F32Min));
        self.register(IntrinsicKey::F64Min, BF(F64Min));

        // max
        self.register(IntrinsicKey::F32Max, BF(F32Max));
        self.register(IntrinsicKey::F64Max, BF(F64Max));
    }

    /// Register unary integer operation intrinsics (abs, clz, ctz, popcnt, bitrev).
    fn register_int_operations(&mut self) {
        register_int_intrinsics!(self, signed, UnaryIntOp, Abs);
        register_int_intrinsics!(self, all, UnaryIntOp, Clz);
        register_int_intrinsics!(self, all, UnaryIntOp, Ctz);
        register_int_intrinsics!(self, all, UnaryIntOp, Popcnt);
        register_int_intrinsics!(self, all, UnaryIntOp, Bitrev);
    }

    /// Register binary integer operation intrinsics (min, max, rotl, rotr, wrapping_add/sub/mul).
    fn register_binary_int_operations(&mut self) {
        register_int_intrinsics!(self, all, BinaryIntOp, Min);
        register_int_intrinsics!(self, all, BinaryIntOp, Max);
        register_int_intrinsics!(self, all, BinaryIntOp, Rotl);
        register_int_intrinsics!(self, all, BinaryIntOp, Rotr);
        register_int_intrinsics!(self, all, BinaryIntOp, WrappingAdd);
        register_int_intrinsics!(self, all, BinaryIntOp, WrappingSub);
        register_int_intrinsics!(self, all, BinaryIntOp, WrappingMul);
    }

    /// Register wrapping integer operation intrinsics (wrapping_neg).
    fn register_wrapping_int_operations(&mut self) {
        register_int_intrinsics!(self, signed, UnaryIntWrappingOp, WrappingNeg);
    }

    /// Register saturating integer operation intrinsics (saturating_add, saturating_sub, saturating_mul).
    fn register_saturating_int_operations(&mut self) {
        register_int_intrinsics!(self, all, BinaryIntOp, SaturatingAdd);
        register_int_intrinsics!(self, all, BinaryIntOp, SaturatingSub);
        register_int_intrinsics!(self, all, BinaryIntOp, SaturatingMul);
    }

    /// Register checked integer operation intrinsics (checked_add, checked_sub, checked_mul, checked_div).
    fn register_checked_int_operations(&mut self) {
        register_int_intrinsics!(self, all, CheckedIntOp, CheckedAdd);
        register_int_intrinsics!(self, all, CheckedIntOp, CheckedSub);
        register_int_intrinsics!(self, all, CheckedIntOp, CheckedMul);
        register_int_intrinsics!(self, all, CheckedIntOp, CheckedDiv);
    }

    /// Register built-in intrinsics (panic, etc.).
    fn register_builtin_intrinsics(&mut self) {
        self.register(IntrinsicKey::Panic, IntrinsicHandler::BuiltinPanic);
        self.register(IntrinsicKey::ArrayLen, IntrinsicHandler::BuiltinArrayLen);
        self.register(IntrinsicKey::StringLen, IntrinsicHandler::BuiltinStringLen);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_contains_float_intrinsics() {
        let registry = IntrinsicsRegistry::new();

        // Verify all f32 constant intrinsics are registered
        assert!(registry.contains(&IntrinsicKey::F32Nan));
        assert!(registry.contains(&IntrinsicKey::F32Infinity));
        assert!(registry.contains(&IntrinsicKey::F32NegInfinity));
        assert!(registry.contains(&IntrinsicKey::F32Epsilon));

        // Verify all f64 constant intrinsics are registered
        assert!(registry.contains(&IntrinsicKey::F64Nan));
        assert!(registry.contains(&IntrinsicKey::F64Infinity));
        assert!(registry.contains(&IntrinsicKey::F64NegInfinity));
        assert!(registry.contains(&IntrinsicKey::F64Epsilon));

        // Verify float operations are registered
        assert!(registry.contains(&IntrinsicKey::F32Sqrt));
        assert!(registry.contains(&IntrinsicKey::F64Sqrt));
        assert!(registry.contains(&IntrinsicKey::F32Abs));
        assert!(registry.contains(&IntrinsicKey::F64Abs));
        assert!(registry.contains(&IntrinsicKey::F32Ceil));
        assert!(registry.contains(&IntrinsicKey::F64Ceil));
        assert!(registry.contains(&IntrinsicKey::F32Floor));
        assert!(registry.contains(&IntrinsicKey::F64Floor));
        assert!(registry.contains(&IntrinsicKey::F32Trunc));
        assert!(registry.contains(&IntrinsicKey::F64Trunc));
        assert!(registry.contains(&IntrinsicKey::F32Round));
        assert!(registry.contains(&IntrinsicKey::F64Round));

        // Binary float operations
        assert!(registry.contains(&IntrinsicKey::F32Min));
        assert!(registry.contains(&IntrinsicKey::F64Min));
        assert!(registry.contains(&IntrinsicKey::F32Max));
        assert!(registry.contains(&IntrinsicKey::F64Max));

        // Unary integer operations (spot check)
        assert!(registry.contains(&IntrinsicKey::I32Abs));
        assert!(registry.contains(&IntrinsicKey::I64Clz));
        assert!(registry.contains(&IntrinsicKey::U32Ctz));
        assert!(registry.contains(&IntrinsicKey::I64Popcnt));

        // Binary integer operations (spot check)
        assert!(registry.contains(&IntrinsicKey::I32Min));
        assert!(registry.contains(&IntrinsicKey::U64Max));

        // Verify count:
        // 8 float constants
        // 12 unary float ops
        // 4 binary float ops (min, max)
        // 36 unary int ops (4 abs + 8 clz + 8 ctz + 8 popcnt + 8 bitrev)
        // 56 binary int ops (8 min + 8 max + 8 rotl + 8 rotr + 8 wrapping_add + 8 wrapping_sub + 8 wrapping_mul)
        // 4 unary int wrapping ops (wrapping_neg for signed types)
        // 24 saturating int ops (8 saturating_add + 8 saturating_sub + 8 saturating_mul)
        // 32 checked int ops (8 checked_add + 8 checked_sub + 8 checked_mul + 8 checked_div)
        // Total: 179 (176 numeric intrinsics + 3 builtins)
        assert_eq!(registry.len(), 179);
    }

    #[test]
    fn test_lookup_by_names() {
        let registry = IntrinsicsRegistry::new();

        let handler = registry.lookup_by_names("f32", "nan");
        assert!(handler.is_some());
        assert!(matches!(
            handler,
            Some(IntrinsicHandler::FloatConstant(FloatConstant::F32Nan))
        ));

        let handler = registry.lookup_by_names("f64", "infinity");
        assert!(handler.is_some());
        assert!(matches!(
            handler,
            Some(IntrinsicHandler::FloatConstant(FloatConstant::F64Infinity))
        ));
    }

    #[test]
    fn test_float_constant_values() {
        assert!(FloatConstant::F32Nan.as_f32().unwrap().is_nan());
        assert_eq!(FloatConstant::F32Infinity.as_f32(), Some(f32::INFINITY));
        assert_eq!(
            FloatConstant::F32NegInfinity.as_f32(),
            Some(f32::NEG_INFINITY)
        );
        assert_eq!(FloatConstant::F32Epsilon.as_f32(), Some(f32::EPSILON));

        assert!(FloatConstant::F64Nan.as_f64().unwrap().is_nan());
        assert_eq!(FloatConstant::F64Infinity.as_f64(), Some(f64::INFINITY));
        assert_eq!(
            FloatConstant::F64NegInfinity.as_f64(),
            Some(f64::NEG_INFINITY)
        );
        assert_eq!(FloatConstant::F64Epsilon.as_f64(), Some(f64::EPSILON));
    }

    #[test]
    fn test_float_constant_type_checks() {
        assert!(FloatConstant::F32Nan.is_f32());
        assert!(!FloatConstant::F32Nan.is_f64());
        assert!(FloatConstant::F64Nan.is_f64());
        assert!(!FloatConstant::F64Nan.is_f32());
    }

    #[test]
    fn test_known_intrinsics_are_registered() {
        let registry = IntrinsicsRegistry::new();
        assert!(registry.lookup(&IntrinsicKey::F32Nan).is_some());
        assert!(registry.lookup(&IntrinsicKey::Panic).is_some());
    }

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

    /// Guard: no stringly-typed IntrinsicKey or RuntimeKey construction outside boundary modules.
    ///
    /// Boundary modules (allowed to use string->key translation):
    ///   - intrinsics.rs           (IntrinsicKey::try_from_name / from_names)
    ///   - runtime_registry.rs     (runtime_keys! macro, the sole place RuntimeKey strings live)
    ///
    /// All other codegen source files must NOT construct keys from raw string literals.
    /// This test enforces that invariant by scanning every .rs file under codegen/src.
    #[test]
    fn no_stringly_typed_key_construction_outside_boundary() {
        use std::fs;
        use std::path::Path;

        let crate_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut rs_files = Vec::new();
        collect_rs_files_for_guard(&crate_root, &mut rs_files);

        let forbidden: &[&str] = &[
            "IntrinsicKey::from(",
            "IntrinsicKey(\"",
            "RuntimeKey::from(",
            "RuntimeKey(\"",
            "format!(\"vole_",
            "concat!(\"vole_",
        ];

        for file in &rs_files {
            let rel = file
                .strip_prefix(&crate_root)
                .expect("INTERNAL: file must live under codegen/src");

            // Skip the two designated boundary modules.
            if rel == Path::new("intrinsics.rs") || rel == Path::new("runtime_registry.rs") {
                continue;
            }

            let content =
                fs::read_to_string(file).expect("INTERNAL: failed to read codegen source file");

            for pattern in forbidden {
                assert!(
                    !content.contains(pattern),
                    "forbidden stringly-typed key pattern {:?} found outside boundary modules: {}",
                    pattern,
                    rel.display()
                );
            }
        }
    }

    fn collect_rs_files_for_guard(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        use std::fs;
        let entries = fs::read_dir(dir).expect("INTERNAL: failed to read directory");
        for entry in entries {
            let entry = entry.expect("INTERNAL: failed to read directory entry");
            let path = entry.path();
            if path.is_dir() {
                collect_rs_files_for_guard(&path, out);
                continue;
            }
            if path.extension().is_some_and(|ext| ext == "rs") {
                out.push(path);
            }
        }
    }
}
