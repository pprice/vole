//! VIR monomorphization support.
//!
//! Type substitution, tree rewriting, decision re-derivation, fixpoint loop,
//! and GenericCall resolution for generic instantiation.

pub mod fixpoint;
pub mod instance;
pub mod rederive;
pub mod resolve;
pub mod rewrite;
pub mod substitute;

pub use fixpoint::{MonomorphInstance, MonomorphResult, monomorphize, monomorphize_with_seeds};
pub use instance::{
    VirClassMethodMonomorphInfo, VirImplementMethodMonomorphInfo, VirMonomorphInfo,
    VirStaticMethodMonomorphInfo,
};
pub use rederive::{
    RederiveCallCtx, classify_capture_rc_kind, classify_rc_cleanup, rederive_decisions,
    rederive_decisions_with_calls, rederive_monomorphized_calls,
};
pub use resolve::{InstanceIndex, resolve_all_calls, resolve_generic_calls, resolve_test_calls};
pub use rewrite::{RewriteCtx, rewrite_function};
pub use substitute::{TypeSubstitution, substitute_types};
