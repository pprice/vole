//! VIR monomorphization support.
//!
//! Type substitution, tree rewriting, decision re-derivation, fixpoint loop,
//! and GenericCall resolution for generic instantiation.

pub mod fixpoint;
pub mod rederive;
pub mod resolve;
pub mod rewrite;
pub mod substitute;

pub use fixpoint::{MonomorphInstance, MonomorphResult, monomorphize};
pub use rederive::rederive_decisions;
pub use resolve::{InstanceIndex, resolve_generic_calls};
pub use rewrite::{RewriteCtx, rewrite_function};
pub use substitute::{TypeSubstitution, substitute_types};
