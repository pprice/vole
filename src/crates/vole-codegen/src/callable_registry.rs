//! Typed callable resolver for codegen dispatch.
//!
//! This is the single typed boundary for selecting callable backends.

use crate::{IntrinsicKey, RuntimeFn};

/// Typed callable identity used by codegen call sites.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallableKey {
    Runtime(RuntimeFn),
    Intrinsic(IntrinsicKey),
}

/// Resolved callable backend target.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResolvedCallable {
    Runtime(RuntimeFn),
    InlineIntrinsic(IntrinsicKey),
}

/// Resolve a typed callable key to its backend implementation.
///
/// Current behavior is a 1:1 mapping with existing call paths.
pub fn resolve_callable(key: CallableKey) -> ResolvedCallable {
    match key {
        CallableKey::Runtime(runtime) => ResolvedCallable::Runtime(runtime),
        CallableKey::Intrinsic(intrinsic) => ResolvedCallable::InlineIntrinsic(intrinsic),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_key_resolves_to_runtime_backend() {
        let resolved = resolve_callable(CallableKey::Runtime(RuntimeFn::StringNew));
        assert!(matches!(
            resolved,
            ResolvedCallable::Runtime(RuntimeFn::StringNew)
        ));
    }

    #[test]
    fn intrinsic_key_resolves_to_inline_backend() {
        let resolved = resolve_callable(CallableKey::Intrinsic(IntrinsicKey::from("f64_nan")));
        assert!(matches!(
            resolved,
            ResolvedCallable::InlineIntrinsic(key) if key.as_str() == "f64_nan"
        ));
    }
}
