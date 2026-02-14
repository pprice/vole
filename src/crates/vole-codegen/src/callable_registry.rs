//! Typed callable resolver for codegen dispatch.
//!
//! This is the single typed boundary for selecting callable backends.

use crate::runtime_registry::AbiTy;
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

/// Backend selection policy for dual-backend callables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallableBackendPreference {
    PreferInline,
    PreferRuntime,
}

/// Strategy contract per callable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallableStrategy {
    RuntimeOnly,
    InlineOnly,
    PreferInlineFallbackRuntime,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CallableSig {
    params: &'static [AbiTy],
    ret: Option<AbiTy>,
}

/// Resolve a typed callable key to its backend implementation.
///
/// Current behavior is a 1:1 mapping with existing call paths.
pub fn resolve_callable(key: CallableKey) -> ResolvedCallable {
    resolve_callable_with_preference(key, default_backend_preference())
}

pub fn resolve_callable_with_preference(
    key: CallableKey,
    preference: CallableBackendPreference,
) -> ResolvedCallable {
    match key {
        CallableKey::Runtime(runtime) => {
            debug_assert_eq!(
                strategy_for_callable(&CallableKey::Runtime(runtime)),
                CallableStrategy::RuntimeOnly
            );
            ResolvedCallable::Runtime(runtime)
        }
        CallableKey::Intrinsic(intrinsic) => match strategy_for_intrinsic(&intrinsic) {
            CallableStrategy::InlineOnly => ResolvedCallable::InlineIntrinsic(intrinsic),
            CallableStrategy::RuntimeOnly => {
                let runtime = runtime_peer_for_intrinsic(&intrinsic)
                    .expect("INTERNAL: runtime-only intrinsic must define runtime peer");
                ResolvedCallable::Runtime(runtime)
            }
            CallableStrategy::PreferInlineFallbackRuntime => {
                if matches!(preference, CallableBackendPreference::PreferRuntime)
                    && let Some(runtime) = runtime_peer_for_intrinsic(&intrinsic)
                {
                    validate_runtime_swap_contract(&intrinsic, runtime)
                        .expect("INTERNAL: invalid intrinsic/runtime swap contract");
                    return ResolvedCallable::Runtime(runtime);
                }
                ResolvedCallable::InlineIntrinsic(intrinsic)
            }
        },
    }
}

fn default_backend_preference() -> CallableBackendPreference {
    if std::env::var("VOLE_CALLABLE_BACKEND").is_ok_and(|value| value == "runtime") {
        return CallableBackendPreference::PreferRuntime;
    }
    CallableBackendPreference::PreferInline
}

pub fn strategy_for_callable(key: &CallableKey) -> CallableStrategy {
    match key {
        CallableKey::Runtime(_) => CallableStrategy::RuntimeOnly,
        CallableKey::Intrinsic(intrinsic) => strategy_for_intrinsic(intrinsic),
    }
}

fn strategy_for_intrinsic(intrinsic: &IntrinsicKey) -> CallableStrategy {
    if intrinsic.as_str() == "panic" {
        // Guardrail: only panic is dual-backend today; NaN/overflow-sensitive
        // numeric intrinsics stay inline-only until behavior conformance exists.
        return CallableStrategy::PreferInlineFallbackRuntime;
    }
    CallableStrategy::InlineOnly
}

fn runtime_peer_for_intrinsic(key: &IntrinsicKey) -> Option<RuntimeFn> {
    match key.as_str() {
        "panic" => Some(RuntimeFn::Panic),
        _ => None,
    }
}

fn intrinsic_signature(key: &IntrinsicKey) -> Option<CallableSig> {
    match key.as_str() {
        "panic" => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: None,
        }),
        _ => None,
    }
}

fn runtime_adapter_signature(key: &IntrinsicKey, runtime: RuntimeFn) -> Option<CallableSig> {
    match (key.as_str(), runtime) {
        // The runtime backend for panic enriches args with source-file metadata.
        ("panic", RuntimeFn::Panic) => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: None,
        }),
        _ => None,
    }
}

fn validate_runtime_swap_contract(key: &IntrinsicKey, runtime: RuntimeFn) -> Result<(), String> {
    let intrinsic = intrinsic_signature(key)
        .ok_or_else(|| format!("missing intrinsic signature contract for {}", key.as_str()))?;
    let runtime_adapter = runtime_adapter_signature(key, runtime).ok_or_else(|| {
        format!(
            "missing runtime adapter signature contract for {} -> {:?}",
            key.as_str(),
            runtime
        )
    })?;
    if intrinsic != runtime_adapter {
        return Err(format!(
            "signature mismatch for {} runtime swap",
            key.as_str()
        ));
    }
    Ok(())
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

    #[test]
    fn panic_intrinsic_can_toggle_to_runtime_backend() {
        let key = CallableKey::Intrinsic(IntrinsicKey::from("panic"));
        let inline =
            resolve_callable_with_preference(key.clone(), CallableBackendPreference::PreferInline);
        assert!(matches!(
            inline,
            ResolvedCallable::InlineIntrinsic(k) if k.as_str() == "panic"
        ));

        let runtime =
            resolve_callable_with_preference(key, CallableBackendPreference::PreferRuntime);
        assert!(matches!(
            runtime,
            ResolvedCallable::Runtime(RuntimeFn::Panic)
        ));
    }

    #[test]
    fn panic_runtime_swap_contract_is_valid() {
        validate_runtime_swap_contract(&IntrinsicKey::from("panic"), RuntimeFn::Panic)
            .expect("panic swap contract must remain valid");
    }
}
