//! VIR monomorphization support.
//!
//! Type substitution, tree rewriting, decision re-derivation, and fixpoint
//! loop for generic instantiation.

pub mod fixpoint;
pub mod rederive;
pub mod rewrite;
pub mod substitute;

pub use fixpoint::{MonomorphInstance, MonomorphResult, monomorphize};
pub use rederive::rederive_decisions;
pub use rewrite::{RewriteCtx, rewrite_function};
pub use substitute::{TypeSubstitution, substitute_types};
