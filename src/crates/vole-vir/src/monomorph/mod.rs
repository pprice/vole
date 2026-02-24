//! VIR monomorphization support.
//!
//! Type substitution and tree rewriting for generic instantiation.

pub mod rewrite;
pub mod substitute;

pub use rewrite::{RewriteCtx, rewrite_function};
pub use substitute::{TypeSubstitution, substitute_types};
