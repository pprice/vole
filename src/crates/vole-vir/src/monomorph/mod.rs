//! VIR monomorphization support.
//!
//! Type substitution, tree rewriting, and decision re-derivation for generic
//! instantiation.

pub mod rederive;
pub mod rewrite;
pub mod substitute;

pub use rederive::rederive_decisions;
pub use rewrite::{RewriteCtx, rewrite_function};
pub use substitute::{TypeSubstitution, substitute_types};
