// passes/mod.rs
//! Reduction passes for vole-reduce.
//!
//! Each pass attempts a different strategy for shrinking the test case while
//! preserving the original bug (as determined by the oracle).

mod file_utils;

pub mod body_reduction;
pub mod decl_elimination;
pub mod import_trimming;
pub mod line_delta;
pub mod module_elimination;
pub mod single_file_collapse;
