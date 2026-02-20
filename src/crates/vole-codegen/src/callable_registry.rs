//! Typed callable resolver for codegen dispatch.
//!
//! This is the single typed boundary for selecting callable backends.

use crate::runtime_registry::AbiTy;
use crate::{IntrinsicKey, RuntimeKey};

/// Typed callable identity used by codegen call sites.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallableKey {
    Runtime(RuntimeKey),
    Intrinsic(IntrinsicKey),
}

/// Resolved callable backend target.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResolvedCallable {
    Runtime(RuntimeKey),
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
                let runtime = runtime_peer_for_intrinsic(&intrinsic)
                    .ok_or(CallableResolutionError::MissingRuntimePeer { intrinsic })?;
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

fn strategy_for_callable(key: &CallableKey) -> CallableStrategy {
    match key {
        CallableKey::Runtime(_) => CallableStrategy::RuntimeOnly,
        CallableKey::Intrinsic(intrinsic) => strategy_for_intrinsic(intrinsic),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallableResolutionError {
    InvalidRuntimeStrategy {
        runtime: RuntimeKey,
    },
    MissingRuntimePeer {
        intrinsic: IntrinsicKey,
    },
    MissingIntrinsicSignature {
        intrinsic: IntrinsicKey,
    },
    MissingRuntimeAdapterSignature {
        intrinsic: IntrinsicKey,
        runtime: RuntimeKey,
    },
    SignatureMismatch {
        intrinsic: IntrinsicKey,
    },
}

impl std::fmt::Display for CallableResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRuntimeStrategy { runtime } => {
                write!(f, "invalid runtime strategy for `{runtime:?}`")
            }
            Self::MissingRuntimePeer { intrinsic } => {
                write!(f, "missing runtime peer for intrinsic `{intrinsic:?}`")
            }
            Self::MissingIntrinsicSignature { intrinsic } => {
                write!(
                    f,
                    "missing intrinsic signature contract for `{intrinsic:?}`"
                )
            }
            Self::MissingRuntimeAdapterSignature { intrinsic, runtime } => {
                write!(
                    f,
                    "missing runtime adapter signature contract for `{intrinsic:?}` -> `{runtime:?}`"
                )
            }
            Self::SignatureMismatch { intrinsic } => {
                write!(f, "signature mismatch for `{intrinsic:?}` runtime swap")
            }
        }
    }
}

impl std::error::Error for CallableResolutionError {}

fn strategy_for_intrinsic(intrinsic: &IntrinsicKey) -> CallableStrategy {
    match intrinsic {
        // Guardrail: only explicitly-vetted callables are dual-backend; NaN/overflow-sensitive
        // numeric intrinsics stay inline-only until behavior conformance exists.
        IntrinsicKey::Panic | IntrinsicKey::ArrayLen | IntrinsicKey::StringLen => {
            CallableStrategy::PreferInlineFallbackRuntime
        }
        _ => CallableStrategy::InlineOnly,
    }
}

fn runtime_peer_for_intrinsic(key: &IntrinsicKey) -> Option<RuntimeKey> {
    match key {
        IntrinsicKey::Panic => Some(RuntimeKey::Panic),
        IntrinsicKey::ArrayLen => Some(RuntimeKey::ArrayLen),
        IntrinsicKey::StringLen => Some(RuntimeKey::StringLen),
        _ => None,
    }
}

fn intrinsic_signature(key: &IntrinsicKey) -> Option<CallableSig> {
    match key {
        IntrinsicKey::Panic => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: None,
        }),
        IntrinsicKey::ArrayLen | IntrinsicKey::StringLen => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        _ => None,
    }
}

fn runtime_adapter_signature(key: &IntrinsicKey, runtime: RuntimeKey) -> Option<CallableSig> {
    match (key, runtime) {
        // The runtime backend for panic enriches args with source-file metadata.
        (IntrinsicKey::Panic, RuntimeKey::Panic) => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: None,
        }),
        (IntrinsicKey::ArrayLen, RuntimeKey::ArrayLen) => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        (IntrinsicKey::StringLen, RuntimeKey::StringLen) => Some(CallableSig {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        }),
        _ => None,
    }
}

fn validate_runtime_swap_contract(
    key: &IntrinsicKey,
    runtime: RuntimeKey,
) -> Result<(), CallableResolutionError> {
    let intrinsic_sig = intrinsic_signature(key)
        .ok_or(CallableResolutionError::MissingIntrinsicSignature { intrinsic: *key })?;
    let runtime_adapter = runtime_adapter_signature(key, runtime).ok_or(
        CallableResolutionError::MissingRuntimeAdapterSignature {
            intrinsic: *key,
            runtime,
        },
    )?;
    if intrinsic_sig != runtime_adapter {
        return Err(CallableResolutionError::SignatureMismatch { intrinsic: *key });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_key_resolves_to_runtime_backend() {
        let resolved = resolve_callable_with_preference(
            CallableKey::Runtime(RuntimeKey::StringNew),
            CallableBackendPreference::PreferInline,
        )
        .expect("runtime callable resolution");
        assert!(matches!(
            resolved,
            ResolvedCallable::Runtime(RuntimeKey::StringNew)
        ));
    }

    #[test]
    fn intrinsic_key_resolves_to_inline_backend() {
        let resolved = resolve_callable_with_preference(
            CallableKey::Intrinsic(IntrinsicKey::F64Nan),
            CallableBackendPreference::PreferInline,
        )
        .expect("intrinsic callable resolution");
        assert!(matches!(
            resolved,
            ResolvedCallable::InlineIntrinsic(IntrinsicKey::F64Nan)
        ));
    }

    #[test]
    fn panic_intrinsic_can_toggle_to_runtime_backend() {
        let key = CallableKey::Intrinsic(IntrinsicKey::Panic);
        let inline =
            resolve_callable_with_preference(key.clone(), CallableBackendPreference::PreferInline)
                .expect("inline panic callable resolution");
        assert!(matches!(
            inline,
            ResolvedCallable::InlineIntrinsic(IntrinsicKey::Panic)
        ));

        let runtime =
            resolve_callable_with_preference(key, CallableBackendPreference::PreferRuntime)
                .expect("runtime panic callable resolution");
        assert!(matches!(
            runtime,
            ResolvedCallable::Runtime(RuntimeKey::Panic)
        ));
    }

    #[test]
    fn panic_runtime_swap_contract_is_valid() {
        validate_runtime_swap_contract(&IntrinsicKey::Panic, RuntimeKey::Panic)
            .expect("panic swap contract must remain valid");
    }

    #[test]
    fn len_intrinsics_can_toggle_to_runtime_backend() {
        for key in [IntrinsicKey::ArrayLen, IntrinsicKey::StringLen] {
            let resolved = resolve_callable_with_preference(
                CallableKey::Intrinsic(key),
                CallableBackendPreference::PreferRuntime,
            )
            .expect("len callable resolution");
            assert!(matches!(
                resolved,
                ResolvedCallable::Runtime(RuntimeKey::ArrayLen | RuntimeKey::StringLen)
            ));
        }
    }
}
