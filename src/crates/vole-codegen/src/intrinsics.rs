//! Intrinsics registry for codegen.
//!
//! Provides a centralized registry mapping intrinsic keys to their codegen handlers.
//! This allows float intrinsics (nan, infinity, epsilon, etc.) to be looked up
//! and compiled in a uniform way.
//!
//! `IntrinsicKey` is defined in `vole-vir` and re-exported here for convenience.

use paste::paste;
use rustc_hash::FxHashMap;

// Re-export IntrinsicKey from its canonical home in vole-vir.
pub use vole_vir::IntrinsicKey;

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

vole_vir::define_int_op_enum! {
    /// Unary integer operations.
    pub enum UnaryIntOp {
        signed: [Abs],
        all: [Clz, Ctz, Popcnt, Bitrev],
    }
}

vole_vir::define_int_op_enum! {
    /// Binary integer operations.
    pub enum BinaryIntOp {
        all: [Min, Max, Rotl, Rotr, WrappingAdd, WrappingSub, WrappingMul,
              SaturatingAdd, SaturatingSub, SaturatingMul],
    }
}

vole_vir::define_int_op_enum! {
    /// Unary integer wrapping operations.
    #[expect(clippy::enum_variant_names)] // All variants are WrappingNeg by design for consistency
    pub enum UnaryIntWrappingOp {
        signed: [WrappingNeg],
    }
}

vole_vir::define_int_op_enum! {
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

    /// Register saturating integer operation intrinsics.
    fn register_saturating_int_operations(&mut self) {
        register_int_intrinsics!(self, all, BinaryIntOp, SaturatingAdd);
        register_int_intrinsics!(self, all, BinaryIntOp, SaturatingSub);
        register_int_intrinsics!(self, all, BinaryIntOp, SaturatingMul);
    }

    /// Register checked integer operation intrinsics.
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
                .unwrap_or_else(|_| panic!("file must live under codegen/src: {}", file.display()));

            // Skip the two designated boundary modules.
            if rel == Path::new("intrinsics.rs") || rel == Path::new("runtime_registry.rs") {
                continue;
            }

            let content = fs::read_to_string(file).unwrap_or_else(|e| {
                panic!("failed to read codegen source file {}: {e}", file.display())
            });

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
        let entries = fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("failed to read directory {}: {e}", dir.display()));
        for entry in entries {
            let entry = entry.unwrap_or_else(|e| {
                panic!("failed to read directory entry in {}: {e}", dir.display())
            });
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
