// src/errors/mod.rs
//! Structured error reporting for the Vole compiler.
//!
//! This module provides error types using miette for fancy diagnostics.

pub mod codegen;
pub mod lexer;
pub mod parser;
pub mod report;
pub mod sema;

pub use codegen::CodegenError;
pub use lexer::LexerError;
pub use parser::ParserError;
pub use report::{
    get_color_mode, render_to_stderr, render_to_string, render_to_writer, set_color_mode,
};
pub use sema::{SemanticError, SemanticWarning};
