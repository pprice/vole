// passes/mod.rs
//! Reduction passes for vole-reduce.
//!
//! Each pass attempts a different strategy for shrinking the test case while
//! preserving the original bug (as determined by the oracle).

pub mod import_trimming;
pub mod module_elimination;
