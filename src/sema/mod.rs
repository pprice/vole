// src/sema/mod.rs
pub mod types;
pub mod scope;
pub mod analyzer;

pub use types::{Type, FunctionType};
pub use analyzer::{Analyzer, TypeError};
