//! Intrinsics registry for codegen.
//!
//! Provides a centralized registry mapping intrinsic keys to their codegen handlers.
//! This allows float intrinsics (nan, infinity, epsilon, etc.) to be looked up
//! and compiled in a uniform way.

use rustc_hash::FxHashMap;

/// A unique key identifying an intrinsic.
///
/// Format: `{type_name}_{method_name}`, e.g., "f32_nan", "f64_infinity".
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntrinsicKey(String);

impl IntrinsicKey {
    /// Create a new intrinsic key from type and method names.
    pub fn new(type_name: &str, method_name: &str) -> Self {
        Self(format!("{}_{}", type_name, method_name))
    }

    /// Get the key as a string slice.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for IntrinsicKey {
    fn from(s: &str) -> Self {
        Self(s.to_string())
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

/// Unary integer operations.
#[derive(Debug, Clone, Copy)]
pub enum UnaryIntOp {
    // Absolute value (signed types only)
    I8Abs,
    I16Abs,
    I32Abs,
    I64Abs,
    // Count leading zeros
    I8Clz,
    I16Clz,
    I32Clz,
    I64Clz,
    U8Clz,
    U16Clz,
    U32Clz,
    U64Clz,
    // Count trailing zeros
    I8Ctz,
    I16Ctz,
    I32Ctz,
    I64Ctz,
    U8Ctz,
    U16Ctz,
    U32Ctz,
    U64Ctz,
    // Population count (count 1 bits)
    I8Popcnt,
    I16Popcnt,
    I32Popcnt,
    I64Popcnt,
    U8Popcnt,
    U16Popcnt,
    U32Popcnt,
    U64Popcnt,
    // Bit reverse
    I8Bitrev,
    I16Bitrev,
    I32Bitrev,
    I64Bitrev,
    U8Bitrev,
    U16Bitrev,
    U32Bitrev,
    U64Bitrev,
}

/// Binary integer operations.
#[derive(Debug, Clone, Copy)]
pub enum BinaryIntOp {
    // Signed minimum
    I8Min,
    I16Min,
    I32Min,
    I64Min,
    // Unsigned minimum
    U8Min,
    U16Min,
    U32Min,
    U64Min,
    // Signed maximum
    I8Max,
    I16Max,
    I32Max,
    I64Max,
    // Unsigned maximum
    U8Max,
    U16Max,
    U32Max,
    U64Max,
    // Rotate left
    I8Rotl,
    I16Rotl,
    I32Rotl,
    I64Rotl,
    U8Rotl,
    U16Rotl,
    U32Rotl,
    U64Rotl,
    // Rotate right
    I8Rotr,
    I16Rotr,
    I32Rotr,
    I64Rotr,
    U8Rotr,
    U16Rotr,
    U32Rotr,
    U64Rotr,
    // Wrapping add
    I8WrappingAdd,
    I16WrappingAdd,
    I32WrappingAdd,
    I64WrappingAdd,
    U8WrappingAdd,
    U16WrappingAdd,
    U32WrappingAdd,
    U64WrappingAdd,
    // Wrapping sub
    I8WrappingSub,
    I16WrappingSub,
    I32WrappingSub,
    I64WrappingSub,
    U8WrappingSub,
    U16WrappingSub,
    U32WrappingSub,
    U64WrappingSub,
    // Wrapping mul
    I8WrappingMul,
    I16WrappingMul,
    I32WrappingMul,
    I64WrappingMul,
    U8WrappingMul,
    U16WrappingMul,
    U32WrappingMul,
    U64WrappingMul,
    // Saturating add
    I8SaturatingAdd,
    I16SaturatingAdd,
    I32SaturatingAdd,
    I64SaturatingAdd,
    U8SaturatingAdd,
    U16SaturatingAdd,
    U32SaturatingAdd,
    U64SaturatingAdd,
    // Saturating sub
    I8SaturatingSub,
    I16SaturatingSub,
    I32SaturatingSub,
    I64SaturatingSub,
    U8SaturatingSub,
    U16SaturatingSub,
    U32SaturatingSub,
    U64SaturatingSub,
    // Saturating mul
    I8SaturatingMul,
    I16SaturatingMul,
    I32SaturatingMul,
    I64SaturatingMul,
    U8SaturatingMul,
    U16SaturatingMul,
    U32SaturatingMul,
    U64SaturatingMul,
}

/// Unary integer wrapping operations.
#[derive(Debug, Clone, Copy)]
#[allow(clippy::enum_variant_names)] // All variants are WrappingNeg by design for consistency
pub enum UnaryIntWrappingOp {
    // Wrapping negation (signed types only)
    I8WrappingNeg,
    I16WrappingNeg,
    I32WrappingNeg,
    I64WrappingNeg,
}

/// Checked integer operations (return Optional<T> - nil on overflow).
#[derive(Debug, Clone, Copy)]
pub enum CheckedIntOp {
    // Checked add - signed
    I8CheckedAdd,
    I16CheckedAdd,
    I32CheckedAdd,
    I64CheckedAdd,
    // Checked add - unsigned
    U8CheckedAdd,
    U16CheckedAdd,
    U32CheckedAdd,
    U64CheckedAdd,
    // Checked sub - signed
    I8CheckedSub,
    I16CheckedSub,
    I32CheckedSub,
    I64CheckedSub,
    // Checked sub - unsigned
    U8CheckedSub,
    U16CheckedSub,
    U32CheckedSub,
    U64CheckedSub,
    // Checked mul - signed
    I8CheckedMul,
    I16CheckedMul,
    I32CheckedMul,
    I64CheckedMul,
    // Checked mul - unsigned
    U8CheckedMul,
    U16CheckedMul,
    U32CheckedMul,
    U64CheckedMul,
    // Checked div - signed (returns nil on div-by-zero or MIN/-1)
    I8CheckedDiv,
    I16CheckedDiv,
    I32CheckedDiv,
    I64CheckedDiv,
    // Checked div - unsigned (returns nil on div-by-zero)
    U8CheckedDiv,
    U16CheckedDiv,
    U32CheckedDiv,
    U64CheckedDiv,
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
            _ => None,
        }
    }

    /// Get the f64 value for this constant, if applicable.
    pub fn as_f64(self) -> Option<f64> {
        match self {
            FloatConstant::F64Nan => Some(f64::NAN),
            FloatConstant::F64Infinity => Some(f64::INFINITY),
            FloatConstant::F64NegInfinity => Some(f64::NEG_INFINITY),
            FloatConstant::F64Epsilon => Some(f64::EPSILON),
            _ => None,
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
    pub fn lookup_by_names(&self, type_name: &str, method_name: &str) -> Option<&IntrinsicHandler> {
        let key = IntrinsicKey::new(type_name, method_name);
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
        self.register(IntrinsicKey::new("f32", "nan"), FC(F32Nan));
        self.register(IntrinsicKey::new("f32", "infinity"), FC(F32Infinity));
        self.register(IntrinsicKey::new("f32", "neg_infinity"), FC(F32NegInfinity));
        self.register(IntrinsicKey::new("f32", "epsilon"), FC(F32Epsilon));

        // f64 intrinsics
        self.register(IntrinsicKey::new("f64", "nan"), FC(F64Nan));
        self.register(IntrinsicKey::new("f64", "infinity"), FC(F64Infinity));
        self.register(IntrinsicKey::new("f64", "neg_infinity"), FC(F64NegInfinity));
        self.register(IntrinsicKey::new("f64", "epsilon"), FC(F64Epsilon));
    }

    /// Register float operation intrinsics (sqrt, abs, ceil, floor, trunc, round).
    fn register_float_operations(&mut self) {
        use IntrinsicHandler::UnaryFloatOp as UF;
        use UnaryFloatOp::*;

        // sqrt
        self.register(IntrinsicKey::from("f32_sqrt"), UF(F32Sqrt));
        self.register(IntrinsicKey::from("f64_sqrt"), UF(F64Sqrt));

        // abs
        self.register(IntrinsicKey::from("f32_abs"), UF(F32Abs));
        self.register(IntrinsicKey::from("f64_abs"), UF(F64Abs));

        // ceil
        self.register(IntrinsicKey::from("f32_ceil"), UF(F32Ceil));
        self.register(IntrinsicKey::from("f64_ceil"), UF(F64Ceil));

        // floor
        self.register(IntrinsicKey::from("f32_floor"), UF(F32Floor));
        self.register(IntrinsicKey::from("f64_floor"), UF(F64Floor));

        // trunc
        self.register(IntrinsicKey::from("f32_trunc"), UF(F32Trunc));
        self.register(IntrinsicKey::from("f64_trunc"), UF(F64Trunc));

        // round (nearest)
        self.register(IntrinsicKey::from("f32_round"), UF(F32Round));
        self.register(IntrinsicKey::from("f64_round"), UF(F64Round));
    }

    /// Register binary float operation intrinsics (min, max).
    fn register_binary_float_operations(&mut self) {
        use BinaryFloatOp::*;
        use IntrinsicHandler::BinaryFloatOp as BF;

        // min
        self.register(IntrinsicKey::from("f32_min"), BF(F32Min));
        self.register(IntrinsicKey::from("f64_min"), BF(F64Min));

        // max
        self.register(IntrinsicKey::from("f32_max"), BF(F32Max));
        self.register(IntrinsicKey::from("f64_max"), BF(F64Max));
    }

    /// Register unary integer operation intrinsics (abs, clz, ctz, popcnt).
    fn register_int_operations(&mut self) {
        use IntrinsicHandler::UnaryIntOp as UI;
        use UnaryIntOp::*;

        // abs (signed only)
        self.register(IntrinsicKey::from("i8_abs"), UI(I8Abs));
        self.register(IntrinsicKey::from("i16_abs"), UI(I16Abs));
        self.register(IntrinsicKey::from("i32_abs"), UI(I32Abs));
        self.register(IntrinsicKey::from("i64_abs"), UI(I64Abs));

        // clz (all int types)
        self.register(IntrinsicKey::from("i8_clz"), UI(I8Clz));
        self.register(IntrinsicKey::from("i16_clz"), UI(I16Clz));
        self.register(IntrinsicKey::from("i32_clz"), UI(I32Clz));
        self.register(IntrinsicKey::from("i64_clz"), UI(I64Clz));
        self.register(IntrinsicKey::from("u8_clz"), UI(U8Clz));
        self.register(IntrinsicKey::from("u16_clz"), UI(U16Clz));
        self.register(IntrinsicKey::from("u32_clz"), UI(U32Clz));
        self.register(IntrinsicKey::from("u64_clz"), UI(U64Clz));

        // ctz (all int types)
        self.register(IntrinsicKey::from("i8_ctz"), UI(I8Ctz));
        self.register(IntrinsicKey::from("i16_ctz"), UI(I16Ctz));
        self.register(IntrinsicKey::from("i32_ctz"), UI(I32Ctz));
        self.register(IntrinsicKey::from("i64_ctz"), UI(I64Ctz));
        self.register(IntrinsicKey::from("u8_ctz"), UI(U8Ctz));
        self.register(IntrinsicKey::from("u16_ctz"), UI(U16Ctz));
        self.register(IntrinsicKey::from("u32_ctz"), UI(U32Ctz));
        self.register(IntrinsicKey::from("u64_ctz"), UI(U64Ctz));

        // popcnt (all int types)
        self.register(IntrinsicKey::from("i8_popcnt"), UI(I8Popcnt));
        self.register(IntrinsicKey::from("i16_popcnt"), UI(I16Popcnt));
        self.register(IntrinsicKey::from("i32_popcnt"), UI(I32Popcnt));
        self.register(IntrinsicKey::from("i64_popcnt"), UI(I64Popcnt));
        self.register(IntrinsicKey::from("u8_popcnt"), UI(U8Popcnt));
        self.register(IntrinsicKey::from("u16_popcnt"), UI(U16Popcnt));
        self.register(IntrinsicKey::from("u32_popcnt"), UI(U32Popcnt));
        self.register(IntrinsicKey::from("u64_popcnt"), UI(U64Popcnt));

        // bitrev (all int types)
        self.register(IntrinsicKey::from("i8_bitrev"), UI(I8Bitrev));
        self.register(IntrinsicKey::from("i16_bitrev"), UI(I16Bitrev));
        self.register(IntrinsicKey::from("i32_bitrev"), UI(I32Bitrev));
        self.register(IntrinsicKey::from("i64_bitrev"), UI(I64Bitrev));
        self.register(IntrinsicKey::from("u8_bitrev"), UI(U8Bitrev));
        self.register(IntrinsicKey::from("u16_bitrev"), UI(U16Bitrev));
        self.register(IntrinsicKey::from("u32_bitrev"), UI(U32Bitrev));
        self.register(IntrinsicKey::from("u64_bitrev"), UI(U64Bitrev));
    }

    /// Register binary integer operation intrinsics (min, max).
    fn register_binary_int_operations(&mut self) {
        use BinaryIntOp::*;
        use IntrinsicHandler::BinaryIntOp as BI;

        // min (signed)
        self.register(IntrinsicKey::from("i8_min"), BI(I8Min));
        self.register(IntrinsicKey::from("i16_min"), BI(I16Min));
        self.register(IntrinsicKey::from("i32_min"), BI(I32Min));
        self.register(IntrinsicKey::from("i64_min"), BI(I64Min));

        // min (unsigned)
        self.register(IntrinsicKey::from("u8_min"), BI(U8Min));
        self.register(IntrinsicKey::from("u16_min"), BI(U16Min));
        self.register(IntrinsicKey::from("u32_min"), BI(U32Min));
        self.register(IntrinsicKey::from("u64_min"), BI(U64Min));

        // max (signed)
        self.register(IntrinsicKey::from("i8_max"), BI(I8Max));
        self.register(IntrinsicKey::from("i16_max"), BI(I16Max));
        self.register(IntrinsicKey::from("i32_max"), BI(I32Max));
        self.register(IntrinsicKey::from("i64_max"), BI(I64Max));

        // max (unsigned)
        self.register(IntrinsicKey::from("u8_max"), BI(U8Max));
        self.register(IntrinsicKey::from("u16_max"), BI(U16Max));
        self.register(IntrinsicKey::from("u32_max"), BI(U32Max));
        self.register(IntrinsicKey::from("u64_max"), BI(U64Max));

        // rotl (all int types)
        self.register(IntrinsicKey::from("i8_rotl"), BI(I8Rotl));
        self.register(IntrinsicKey::from("i16_rotl"), BI(I16Rotl));
        self.register(IntrinsicKey::from("i32_rotl"), BI(I32Rotl));
        self.register(IntrinsicKey::from("i64_rotl"), BI(I64Rotl));
        self.register(IntrinsicKey::from("u8_rotl"), BI(U8Rotl));
        self.register(IntrinsicKey::from("u16_rotl"), BI(U16Rotl));
        self.register(IntrinsicKey::from("u32_rotl"), BI(U32Rotl));
        self.register(IntrinsicKey::from("u64_rotl"), BI(U64Rotl));

        // rotr (all int types)
        self.register(IntrinsicKey::from("i8_rotr"), BI(I8Rotr));
        self.register(IntrinsicKey::from("i16_rotr"), BI(I16Rotr));
        self.register(IntrinsicKey::from("i32_rotr"), BI(I32Rotr));
        self.register(IntrinsicKey::from("i64_rotr"), BI(I64Rotr));
        self.register(IntrinsicKey::from("u8_rotr"), BI(U8Rotr));
        self.register(IntrinsicKey::from("u16_rotr"), BI(U16Rotr));
        self.register(IntrinsicKey::from("u32_rotr"), BI(U32Rotr));
        self.register(IntrinsicKey::from("u64_rotr"), BI(U64Rotr));

        // wrapping_add (all int types)
        self.register(IntrinsicKey::from("i8_wrapping_add"), BI(I8WrappingAdd));
        self.register(IntrinsicKey::from("i16_wrapping_add"), BI(I16WrappingAdd));
        self.register(IntrinsicKey::from("i32_wrapping_add"), BI(I32WrappingAdd));
        self.register(IntrinsicKey::from("i64_wrapping_add"), BI(I64WrappingAdd));
        self.register(IntrinsicKey::from("u8_wrapping_add"), BI(U8WrappingAdd));
        self.register(IntrinsicKey::from("u16_wrapping_add"), BI(U16WrappingAdd));
        self.register(IntrinsicKey::from("u32_wrapping_add"), BI(U32WrappingAdd));
        self.register(IntrinsicKey::from("u64_wrapping_add"), BI(U64WrappingAdd));

        // wrapping_sub (all int types)
        self.register(IntrinsicKey::from("i8_wrapping_sub"), BI(I8WrappingSub));
        self.register(IntrinsicKey::from("i16_wrapping_sub"), BI(I16WrappingSub));
        self.register(IntrinsicKey::from("i32_wrapping_sub"), BI(I32WrappingSub));
        self.register(IntrinsicKey::from("i64_wrapping_sub"), BI(I64WrappingSub));
        self.register(IntrinsicKey::from("u8_wrapping_sub"), BI(U8WrappingSub));
        self.register(IntrinsicKey::from("u16_wrapping_sub"), BI(U16WrappingSub));
        self.register(IntrinsicKey::from("u32_wrapping_sub"), BI(U32WrappingSub));
        self.register(IntrinsicKey::from("u64_wrapping_sub"), BI(U64WrappingSub));

        // wrapping_mul (all int types)
        self.register(IntrinsicKey::from("i8_wrapping_mul"), BI(I8WrappingMul));
        self.register(IntrinsicKey::from("i16_wrapping_mul"), BI(I16WrappingMul));
        self.register(IntrinsicKey::from("i32_wrapping_mul"), BI(I32WrappingMul));
        self.register(IntrinsicKey::from("i64_wrapping_mul"), BI(I64WrappingMul));
        self.register(IntrinsicKey::from("u8_wrapping_mul"), BI(U8WrappingMul));
        self.register(IntrinsicKey::from("u16_wrapping_mul"), BI(U16WrappingMul));
        self.register(IntrinsicKey::from("u32_wrapping_mul"), BI(U32WrappingMul));
        self.register(IntrinsicKey::from("u64_wrapping_mul"), BI(U64WrappingMul));
    }

    /// Register wrapping integer operation intrinsics (wrapping_neg).
    fn register_wrapping_int_operations(&mut self) {
        use IntrinsicHandler::UnaryIntWrappingOp as UW;
        use UnaryIntWrappingOp::*;

        // wrapping_neg (signed types only)
        self.register(IntrinsicKey::from("i8_wrapping_neg"), UW(I8WrappingNeg));
        self.register(IntrinsicKey::from("i16_wrapping_neg"), UW(I16WrappingNeg));
        self.register(IntrinsicKey::from("i32_wrapping_neg"), UW(I32WrappingNeg));
        self.register(IntrinsicKey::from("i64_wrapping_neg"), UW(I64WrappingNeg));
    }

    /// Register saturating integer operation intrinsics (saturating_add, saturating_sub, saturating_mul).
    fn register_saturating_int_operations(&mut self) {
        use BinaryIntOp::*;
        use IntrinsicHandler::BinaryIntOp as BI;

        // saturating_add (all int types)
        self.register(IntrinsicKey::from("i8_saturating_add"), BI(I8SaturatingAdd));
        self.register(
            IntrinsicKey::from("i16_saturating_add"),
            BI(I16SaturatingAdd),
        );
        self.register(
            IntrinsicKey::from("i32_saturating_add"),
            BI(I32SaturatingAdd),
        );
        self.register(
            IntrinsicKey::from("i64_saturating_add"),
            BI(I64SaturatingAdd),
        );
        self.register(IntrinsicKey::from("u8_saturating_add"), BI(U8SaturatingAdd));
        self.register(
            IntrinsicKey::from("u16_saturating_add"),
            BI(U16SaturatingAdd),
        );
        self.register(
            IntrinsicKey::from("u32_saturating_add"),
            BI(U32SaturatingAdd),
        );
        self.register(
            IntrinsicKey::from("u64_saturating_add"),
            BI(U64SaturatingAdd),
        );

        // saturating_sub (all int types)
        self.register(IntrinsicKey::from("i8_saturating_sub"), BI(I8SaturatingSub));
        self.register(
            IntrinsicKey::from("i16_saturating_sub"),
            BI(I16SaturatingSub),
        );
        self.register(
            IntrinsicKey::from("i32_saturating_sub"),
            BI(I32SaturatingSub),
        );
        self.register(
            IntrinsicKey::from("i64_saturating_sub"),
            BI(I64SaturatingSub),
        );
        self.register(IntrinsicKey::from("u8_saturating_sub"), BI(U8SaturatingSub));
        self.register(
            IntrinsicKey::from("u16_saturating_sub"),
            BI(U16SaturatingSub),
        );
        self.register(
            IntrinsicKey::from("u32_saturating_sub"),
            BI(U32SaturatingSub),
        );
        self.register(
            IntrinsicKey::from("u64_saturating_sub"),
            BI(U64SaturatingSub),
        );

        // saturating_mul (all int types)
        self.register(IntrinsicKey::from("i8_saturating_mul"), BI(I8SaturatingMul));
        self.register(
            IntrinsicKey::from("i16_saturating_mul"),
            BI(I16SaturatingMul),
        );
        self.register(
            IntrinsicKey::from("i32_saturating_mul"),
            BI(I32SaturatingMul),
        );
        self.register(
            IntrinsicKey::from("i64_saturating_mul"),
            BI(I64SaturatingMul),
        );
        self.register(IntrinsicKey::from("u8_saturating_mul"), BI(U8SaturatingMul));
        self.register(
            IntrinsicKey::from("u16_saturating_mul"),
            BI(U16SaturatingMul),
        );
        self.register(
            IntrinsicKey::from("u32_saturating_mul"),
            BI(U32SaturatingMul),
        );
        self.register(
            IntrinsicKey::from("u64_saturating_mul"),
            BI(U64SaturatingMul),
        );
    }

    /// Register checked integer operation intrinsics (checked_add, checked_sub, checked_mul, checked_div).
    fn register_checked_int_operations(&mut self) {
        use CheckedIntOp::*;
        use IntrinsicHandler::CheckedIntOp as CI;

        // checked_add (all int types)
        self.register(IntrinsicKey::from("i8_checked_add"), CI(I8CheckedAdd));
        self.register(IntrinsicKey::from("i16_checked_add"), CI(I16CheckedAdd));
        self.register(IntrinsicKey::from("i32_checked_add"), CI(I32CheckedAdd));
        self.register(IntrinsicKey::from("i64_checked_add"), CI(I64CheckedAdd));
        self.register(IntrinsicKey::from("u8_checked_add"), CI(U8CheckedAdd));
        self.register(IntrinsicKey::from("u16_checked_add"), CI(U16CheckedAdd));
        self.register(IntrinsicKey::from("u32_checked_add"), CI(U32CheckedAdd));
        self.register(IntrinsicKey::from("u64_checked_add"), CI(U64CheckedAdd));

        // checked_sub (all int types)
        self.register(IntrinsicKey::from("i8_checked_sub"), CI(I8CheckedSub));
        self.register(IntrinsicKey::from("i16_checked_sub"), CI(I16CheckedSub));
        self.register(IntrinsicKey::from("i32_checked_sub"), CI(I32CheckedSub));
        self.register(IntrinsicKey::from("i64_checked_sub"), CI(I64CheckedSub));
        self.register(IntrinsicKey::from("u8_checked_sub"), CI(U8CheckedSub));
        self.register(IntrinsicKey::from("u16_checked_sub"), CI(U16CheckedSub));
        self.register(IntrinsicKey::from("u32_checked_sub"), CI(U32CheckedSub));
        self.register(IntrinsicKey::from("u64_checked_sub"), CI(U64CheckedSub));

        // checked_mul (all int types)
        self.register(IntrinsicKey::from("i8_checked_mul"), CI(I8CheckedMul));
        self.register(IntrinsicKey::from("i16_checked_mul"), CI(I16CheckedMul));
        self.register(IntrinsicKey::from("i32_checked_mul"), CI(I32CheckedMul));
        self.register(IntrinsicKey::from("i64_checked_mul"), CI(I64CheckedMul));
        self.register(IntrinsicKey::from("u8_checked_mul"), CI(U8CheckedMul));
        self.register(IntrinsicKey::from("u16_checked_mul"), CI(U16CheckedMul));
        self.register(IntrinsicKey::from("u32_checked_mul"), CI(U32CheckedMul));
        self.register(IntrinsicKey::from("u64_checked_mul"), CI(U64CheckedMul));

        // checked_div (all int types)
        self.register(IntrinsicKey::from("i8_checked_div"), CI(I8CheckedDiv));
        self.register(IntrinsicKey::from("i16_checked_div"), CI(I16CheckedDiv));
        self.register(IntrinsicKey::from("i32_checked_div"), CI(I32CheckedDiv));
        self.register(IntrinsicKey::from("i64_checked_div"), CI(I64CheckedDiv));
        self.register(IntrinsicKey::from("u8_checked_div"), CI(U8CheckedDiv));
        self.register(IntrinsicKey::from("u16_checked_div"), CI(U16CheckedDiv));
        self.register(IntrinsicKey::from("u32_checked_div"), CI(U32CheckedDiv));
        self.register(IntrinsicKey::from("u64_checked_div"), CI(U64CheckedDiv));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_contains_float_intrinsics() {
        let registry = IntrinsicsRegistry::new();

        // Verify all f32 constant intrinsics are registered
        assert!(registry.contains(&IntrinsicKey::new("f32", "nan")));
        assert!(registry.contains(&IntrinsicKey::new("f32", "infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f32", "neg_infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f32", "epsilon")));

        // Verify all f64 constant intrinsics are registered
        assert!(registry.contains(&IntrinsicKey::new("f64", "nan")));
        assert!(registry.contains(&IntrinsicKey::new("f64", "infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f64", "neg_infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f64", "epsilon")));

        // Verify float operations are registered
        assert!(registry.contains(&IntrinsicKey::from("f32_sqrt")));
        assert!(registry.contains(&IntrinsicKey::from("f64_sqrt")));
        assert!(registry.contains(&IntrinsicKey::from("f32_abs")));
        assert!(registry.contains(&IntrinsicKey::from("f64_abs")));
        assert!(registry.contains(&IntrinsicKey::from("f32_ceil")));
        assert!(registry.contains(&IntrinsicKey::from("f64_ceil")));
        assert!(registry.contains(&IntrinsicKey::from("f32_floor")));
        assert!(registry.contains(&IntrinsicKey::from("f64_floor")));
        assert!(registry.contains(&IntrinsicKey::from("f32_trunc")));
        assert!(registry.contains(&IntrinsicKey::from("f64_trunc")));
        assert!(registry.contains(&IntrinsicKey::from("f32_round")));
        assert!(registry.contains(&IntrinsicKey::from("f64_round")));

        // Binary float operations
        assert!(registry.contains(&IntrinsicKey::from("f32_min")));
        assert!(registry.contains(&IntrinsicKey::from("f64_min")));
        assert!(registry.contains(&IntrinsicKey::from("f32_max")));
        assert!(registry.contains(&IntrinsicKey::from("f64_max")));

        // Unary integer operations (spot check)
        assert!(registry.contains(&IntrinsicKey::from("i32_abs")));
        assert!(registry.contains(&IntrinsicKey::from("i64_clz")));
        assert!(registry.contains(&IntrinsicKey::from("u32_ctz")));
        assert!(registry.contains(&IntrinsicKey::from("i64_popcnt")));

        // Binary integer operations (spot check)
        assert!(registry.contains(&IntrinsicKey::from("i32_min")));
        assert!(registry.contains(&IntrinsicKey::from("u64_max")));

        // Verify count:
        // 8 float constants
        // 12 unary float ops
        // 4 binary float ops (min, max)
        // 36 unary int ops (4 abs + 8 clz + 8 ctz + 8 popcnt + 8 bitrev)
        // 56 binary int ops (8 min + 8 max + 8 rotl + 8 rotr + 8 wrapping_add + 8 wrapping_sub + 8 wrapping_mul)
        // 4 unary int wrapping ops (wrapping_neg for signed types)
        // 24 saturating int ops (8 saturating_add + 8 saturating_sub + 8 saturating_mul)
        // 32 checked int ops (8 checked_add + 8 checked_sub + 8 checked_mul + 8 checked_div)
        // Total: 176
        assert_eq!(registry.len(), 176);
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
    fn test_unknown_intrinsic_returns_none() {
        let registry = IntrinsicsRegistry::new();
        assert!(registry.lookup_by_names("f32", "unknown").is_none());
        assert!(registry.lookup_by_names("i64", "nan").is_none());
    }
}
