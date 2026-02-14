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
    ($self:ident, all, $handler:ident, $method:literal, $op:ident) => {
        paste! {
            $self.register(IntrinsicKey::from(concat!("i8_", $method)), IntrinsicHandler::$handler($handler::[<I8 $op>]));
            $self.register(IntrinsicKey::from(concat!("i16_", $method)), IntrinsicHandler::$handler($handler::[<I16 $op>]));
            $self.register(IntrinsicKey::from(concat!("i32_", $method)), IntrinsicHandler::$handler($handler::[<I32 $op>]));
            $self.register(IntrinsicKey::from(concat!("i64_", $method)), IntrinsicHandler::$handler($handler::[<I64 $op>]));
            $self.register(IntrinsicKey::from(concat!("u8_", $method)), IntrinsicHandler::$handler($handler::[<U8 $op>]));
            $self.register(IntrinsicKey::from(concat!("u16_", $method)), IntrinsicHandler::$handler($handler::[<U16 $op>]));
            $self.register(IntrinsicKey::from(concat!("u32_", $method)), IntrinsicHandler::$handler($handler::[<U32 $op>]));
            $self.register(IntrinsicKey::from(concat!("u64_", $method)), IntrinsicHandler::$handler($handler::[<U64 $op>]));
        }
    };
    // Signed integer types only
    ($self:ident, signed, $handler:ident, $method:literal, $op:ident) => {
        paste! {
            $self.register(IntrinsicKey::from(concat!("i8_", $method)), IntrinsicHandler::$handler($handler::[<I8 $op>]));
            $self.register(IntrinsicKey::from(concat!("i16_", $method)), IntrinsicHandler::$handler($handler::[<I16 $op>]));
            $self.register(IntrinsicKey::from(concat!("i32_", $method)), IntrinsicHandler::$handler($handler::[<I32 $op>]));
            $self.register(IntrinsicKey::from(concat!("i64_", $method)), IntrinsicHandler::$handler($handler::[<I64 $op>]));
        }
    };
}

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

    /// Register unary integer operation intrinsics (abs, clz, ctz, popcnt, bitrev).
    fn register_int_operations(&mut self) {
        register_int_intrinsics!(self, signed, UnaryIntOp, "abs", Abs);
        register_int_intrinsics!(self, all, UnaryIntOp, "clz", Clz);
        register_int_intrinsics!(self, all, UnaryIntOp, "ctz", Ctz);
        register_int_intrinsics!(self, all, UnaryIntOp, "popcnt", Popcnt);
        register_int_intrinsics!(self, all, UnaryIntOp, "bitrev", Bitrev);
    }

    /// Register binary integer operation intrinsics (min, max, rotl, rotr, wrapping_add/sub/mul).
    fn register_binary_int_operations(&mut self) {
        register_int_intrinsics!(self, all, BinaryIntOp, "min", Min);
        register_int_intrinsics!(self, all, BinaryIntOp, "max", Max);
        register_int_intrinsics!(self, all, BinaryIntOp, "rotl", Rotl);
        register_int_intrinsics!(self, all, BinaryIntOp, "rotr", Rotr);
        register_int_intrinsics!(self, all, BinaryIntOp, "wrapping_add", WrappingAdd);
        register_int_intrinsics!(self, all, BinaryIntOp, "wrapping_sub", WrappingSub);
        register_int_intrinsics!(self, all, BinaryIntOp, "wrapping_mul", WrappingMul);
    }

    /// Register wrapping integer operation intrinsics (wrapping_neg).
    fn register_wrapping_int_operations(&mut self) {
        register_int_intrinsics!(
            self,
            signed,
            UnaryIntWrappingOp,
            "wrapping_neg",
            WrappingNeg
        );
    }

    /// Register saturating integer operation intrinsics (saturating_add, saturating_sub, saturating_mul).
    fn register_saturating_int_operations(&mut self) {
        register_int_intrinsics!(self, all, BinaryIntOp, "saturating_add", SaturatingAdd);
        register_int_intrinsics!(self, all, BinaryIntOp, "saturating_sub", SaturatingSub);
        register_int_intrinsics!(self, all, BinaryIntOp, "saturating_mul", SaturatingMul);
    }

    /// Register checked integer operation intrinsics (checked_add, checked_sub, checked_mul, checked_div).
    fn register_checked_int_operations(&mut self) {
        register_int_intrinsics!(self, all, CheckedIntOp, "checked_add", CheckedAdd);
        register_int_intrinsics!(self, all, CheckedIntOp, "checked_sub", CheckedSub);
        register_int_intrinsics!(self, all, CheckedIntOp, "checked_mul", CheckedMul);
        register_int_intrinsics!(self, all, CheckedIntOp, "checked_div", CheckedDiv);
    }

    /// Register built-in intrinsics (panic, etc.).
    fn register_builtin_intrinsics(&mut self) {
        self.register(IntrinsicKey::from("panic"), IntrinsicHandler::BuiltinPanic);
        self.register(
            IntrinsicKey::from("array_len"),
            IntrinsicHandler::BuiltinArrayLen,
        );
        self.register(
            IntrinsicKey::from("string_len"),
            IntrinsicHandler::BuiltinStringLen,
        );
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
    fn test_unknown_intrinsic_returns_none() {
        let registry = IntrinsicsRegistry::new();
        assert!(registry.lookup_by_names("f32", "unknown").is_none());
        assert!(registry.lookup_by_names("i64", "nan").is_none());
    }
}
