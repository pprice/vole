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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_contains_float_intrinsics() {
        let registry = IntrinsicsRegistry::new();

        // Verify all f32 intrinsics are registered
        assert!(registry.contains(&IntrinsicKey::new("f32", "nan")));
        assert!(registry.contains(&IntrinsicKey::new("f32", "infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f32", "neg_infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f32", "epsilon")));

        // Verify all f64 intrinsics are registered
        assert!(registry.contains(&IntrinsicKey::new("f64", "nan")));
        assert!(registry.contains(&IntrinsicKey::new("f64", "infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f64", "neg_infinity")));
        assert!(registry.contains(&IntrinsicKey::new("f64", "epsilon")));

        // Verify count
        assert_eq!(registry.len(), 8);
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
