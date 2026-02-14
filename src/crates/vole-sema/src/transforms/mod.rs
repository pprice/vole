//! AST transformations applied between parsing and semantic analysis.
//!
//! These transforms operate on the raw AST before type checking,
//! allowing high-level language features to be desugared into
//! simpler constructs.

mod expr_walker;
pub mod generator;
mod rewrite_refs;

pub use generator::transform_generators;
