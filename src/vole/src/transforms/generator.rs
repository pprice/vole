// src/transforms/generator.rs
//! Generator-to-state-machine transformation.
//!
//! This module re-exports the implementation from vole-sema so that
//! both the main pipeline and imported module analysis share the same
//! transform logic.

pub use vole_sema::transforms::generator::transform_generators;
