// src/errors/mod.rs
//! Structured error reporting for the Vole compiler.
//!
//! This module provides error types using miette for fancy diagnostics.

pub mod report;

// Re-export frontend errors
pub use vole_frontend::errors::{LexerError, ParserError};

// Re-export sema errors
pub use vole_sema::errors::{SemanticError, SemanticWarning};

// Re-export codegen errors
pub use vole_codegen::errors::CodegenError;

pub use report::{
    WithExtraHelp, get_color_mode, render_to_stderr, render_to_string, render_to_writer,
    render_to_writer_terminal, set_color_mode,
};
