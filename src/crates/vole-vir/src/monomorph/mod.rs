//! VIR monomorphization support.
//!
//! Type substitution and tree rewriting for generic instantiation.

pub mod substitute;

pub use substitute::{TypeSubstitution, substitute_types};
