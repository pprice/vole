// src/errors/mod.rs
//! Structured error reporting for the Vole compiler.
//!
//! This module provides error codes, diagnostic types, and rendering
//! functionality for compiler errors that match void's error format.

pub mod codes;
pub mod diagnostic;

pub use codes::{ErrorInfo, Severity};
pub use diagnostic::{Diagnostic, DiagnosticBuilder, RelatedInfo, get_line_from_source};

// Re-export all error codes for convenient access
pub use codes::{
    // Lexer errors (E0xxx)
    LEXER_INVALID_NUMBER,
    LEXER_UNEXPECTED_CHARACTER,
    LEXER_UNTERMINATED_STRING,
    // Parser errors (E1xxx)
    PARSER_EXPECTED_BLOCK,
    PARSER_EXPECTED_EXPRESSION,
    PARSER_EXPECTED_IDENTIFIER,
    PARSER_EXPECTED_TOKEN,
    PARSER_EXPECTED_TYPE,
    PARSER_UNEXPECTED_TOKEN,
    // Semantic errors (E2xxx)
    SEMA_CONDITION_NOT_BOOL,
    SEMA_IMMUTABLE_VARIABLE,
    SEMA_INVALID_BREAK,
    SEMA_TYPE_MISMATCH,
    SEMA_UNDEFINED_VARIABLE,
    SEMA_WRONG_ARGUMENT_COUNT,
};
