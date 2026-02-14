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
pub fn resolve_callable_with_preference(
    key: CallableKey,
    preference: CallableBackendPreference,
) -> Result<ResolvedCallable, CallableResolutionError> {
    match key {
        CallableKey::Runtime(runtime) => {
            if !matches!(
                strategy_for_callable(&CallableKey::Runtime(runtime)),
                CallableStrategy::RuntimeOnly
            ) {
                return Err(CallableResolutionError::InvalidRuntimeStrategy { runtime });
            }
            Ok(ResolvedCallable::Runtime(runtime))
        }
        CallableKey::Intrinsic(intrinsic) => match strategy_for_intrinsic(&intrinsic) {
            CallableStrategy::InlineOnly => Ok(ResolvedCallable::InlineIntrinsic(intrinsic)),
            CallableStrategy::RuntimeOnly => {
                let runtime = runtime_peer_for_intrinsic(&intrinsic).ok_or_else(|| {
                    CallableResolutionError::MissingRuntimePeer {
                        intrinsic: intrinsic.as_str().to_string(),
                    }
                })?;
                Ok(ResolvedCallable::Runtime(runtime))
            }
            CallableStrategy::PreferInlineFallbackRuntime => {
                if matches!(preference, CallableBackendPreference::PreferRuntime)
                    && let Some(runtime) = runtime_peer_for_intrinsic(&intrinsic)
                {
                    validate_runtime_swap_contract(&intrinsic, runtime)?;
                    return Ok(ResolvedCallable::Runtime(runtime));
                }
                Ok(ResolvedCallable::InlineIntrinsic(intrinsic))
            }
        },
    }
}

pub fn strategy_for_callable(key: &CallableKey) -> CallableStrategy {
    match key {
        CallableKey::Runtime(_) => CallableStrategy::RuntimeOnly,
        CallableKey::Intrinsic(intrinsic) => strategy_for_intrinsic(intrinsic),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallableResolutionError {
    InvalidRuntimeStrategy {
        runtime: RuntimeFn,
    },
    MissingRuntimePeer {
        intrinsic: String,
    },
    MissingIntrinsicSignature {
        intrinsic: String,
    },
    MissingRuntimeAdapterSignature {
        intrinsic: String,
        runtime: RuntimeFn,
    },
    SignatureMismatch {
        intrinsic: String,
    },
}

impl std::fmt::Display for CallableResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRuntimeStrategy { runtime } => {
                write!(f, "invalid runtime strategy for `{runtime:?}`")
            }
            Self::MissingRuntimePeer { intrinsic } => {
                write!(f, "missing runtime peer for intrinsic `{intrinsic}`")
            }
            Self::MissingIntrinsicSignature { intrinsic } => {
                write!(f, "missing intrinsic signature contract for `{intrinsic}`")
            }
            Self::MissingRuntimeAdapterSignature { intrinsic, runtime } => {
                write!(
                    f,
                    "missing runtime adapter signature contract for `{intrinsic}` -> `{runtime:?}`"
                )
            }
            Self::SignatureMismatch { intrinsic } => {
                write!(f, "signature mismatch for `{intrinsic}` runtime swap")
            }
        }
    }
}

impl std::error::Error for CallableResolutionError {}

fn strategy_for_intrinsic(intrinsic: &IntrinsicKey) -> CallableStrategy {
    match intrinsic.as_str() {
        // Guardrail: only explicitly-vetted callables are dual-backend; NaN/overflow-sensitive
        // numeric intrinsics stay inline-only until behavior conformance exists.
        "panic" | "array_len" | "string_len" | "string_eq" => {
            CallableStrategy::PreferInlineFallbackRuntime
        }
        _ => CallableStrategy::InlineOnly,
    }
}

fn runtime_peer_for_intrinsic(key: &IntrinsicKey) -> Option<RuntimeFn> {
    match key.as_str() {
        "panic" => Some(RuntimeFn::Panic),
        "array_len" => Some(RuntimeFn::ArrayLen),
        "string_len" => Some(RuntimeFn::StringLen),
        "string_eq" => Some(RuntimeFn::StringEq),
        _ => None,
    }
}

fn intrinsic_signature(key: &IntrinsicKey) -> Option<CallableSig> {
    match key.as_str() {
        "panic" => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: None,
        }),
        "array_len" => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        "string_len" => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        "string_eq" => Some(CallableSig {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I8),
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
        ("array_len", RuntimeFn::ArrayLen) => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        ("string_len", RuntimeFn::StringLen) => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        ("string_eq", RuntimeFn::StringEq) => Some(CallableSig {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I8),
        }),
        _ => None,
    }
}

fn validate_runtime_swap_contract(
    key: &IntrinsicKey,
    runtime: RuntimeFn,
) -> Result<(), CallableResolutionError> {
    let intrinsic = intrinsic_signature(key).ok_or_else(|| {
        CallableResolutionError::MissingIntrinsicSignature {
            intrinsic: key.as_str().to_string(),
        }
    })?;
    let runtime_adapter = runtime_adapter_signature(key, runtime).ok_or_else(|| {
        CallableResolutionError::MissingRuntimeAdapterSignature {
            intrinsic: key.as_str().to_string(),
            runtime,
        }
    })?;
    if intrinsic != runtime_adapter {
        return Err(CallableResolutionError::SignatureMismatch {
            intrinsic: key.as_str().to_string(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_key_resolves_to_runtime_backend() {
        let resolved = resolve_callable_with_preference(
            CallableKey::Runtime(RuntimeFn::StringNew),
            CallableBackendPreference::PreferInline,
        )
        .expect("runtime callable resolution");
        assert!(matches!(
            resolved,
            ResolvedCallable::Runtime(RuntimeFn::StringNew)
        ));
    }

    #[test]
    fn intrinsic_key_resolves_to_inline_backend() {
        let resolved = resolve_callable_with_preference(
            CallableKey::Intrinsic(IntrinsicKey::from("f64_nan")),
            CallableBackendPreference::PreferInline,
        )
        .expect("intrinsic callable resolution");
        assert!(matches!(
            resolved,
            ResolvedCallable::InlineIntrinsic(key) if key.as_str() == "f64_nan"
        ));
    }

    #[test]
    fn panic_intrinsic_can_toggle_to_runtime_backend() {
        let key = CallableKey::Intrinsic(IntrinsicKey::from("panic"));
        let inline =
            resolve_callable_with_preference(key.clone(), CallableBackendPreference::PreferInline)
                .expect("inline panic callable resolution");
        assert!(matches!(
            inline,
            ResolvedCallable::InlineIntrinsic(k) if k.as_str() == "panic"
        ));

        let runtime =
            resolve_callable_with_preference(key, CallableBackendPreference::PreferRuntime)
                .expect("runtime panic callable resolution");
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

    #[test]
    fn len_intrinsics_can_toggle_to_runtime_backend() {
        for key in ["array_len", "string_len", "string_eq"] {
            let resolved = resolve_callable_with_preference(
                CallableKey::Intrinsic(IntrinsicKey::from(key)),
                CallableBackendPreference::PreferRuntime,
            )
            .expect("len callable resolution");
            assert!(matches!(
                resolved,
                ResolvedCallable::Runtime(
                    RuntimeFn::ArrayLen | RuntimeFn::StringLen | RuntimeFn::StringEq
                )
            ));
        }
    }
}
