// src/fmt/mod.rs
//! Vole source code formatter.
//!
//! Provides canonical formatting for Vole source files.

mod config;
mod formatter;

pub use config::{FormatConfig, CANONICAL};
pub use formatter::{format, FormatError, FormatResult};
