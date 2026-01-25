// src/fmt/mod.rs
//! Vole source code formatter.
//!
//! Provides canonical formatting for Vole source files.

mod config;
mod formatter;
mod printer;

pub use config::{CANONICAL, FormatConfig};
pub use formatter::{FormatError, FormatResult, format};
