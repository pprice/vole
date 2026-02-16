//! AST query utilities for generator detection.
//!
//! The AST-level generator-to-state-machine transform has been removed.
//! Generators are now compiled directly to coroutine-backed iterators
//! in vole-codegen. This module retains the expression walker and
//! `contains_yield` detection used by codegen.

mod expr_walker;
pub mod generator;

pub use generator::contains_yield;
