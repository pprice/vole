//! AST transformations applied between parsing and semantic analysis.
//!
//! These transforms operate on the raw AST before type checking,
//! allowing high-level language features to be desugared into
//! simpler constructs.

pub mod generator;

pub use generator::transform_generators;
