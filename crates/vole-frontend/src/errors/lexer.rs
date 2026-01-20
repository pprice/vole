// src/errors/lexer.rs
//! Lexer errors (E0xxx).

#![allow(unused_assignments)] // False positives from thiserror derive

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Error, Debug, Diagnostic, Clone)]
pub enum LexerError {
    #[error("unexpected character '{ch}'")]
    #[diagnostic(code(E0001))]
    UnexpectedCharacter {
        ch: char,
        #[label("unexpected character")]
        span: SourceSpan,
    },

    #[error("unterminated string literal")]
    #[diagnostic(code(E0002), help("add a closing '\"' to terminate the string"))]
    UnterminatedString {
        #[label("string starts here")]
        span: SourceSpan,
    },

    #[error("invalid number literal")]
    #[diagnostic(code(E0005))]
    InvalidNumber {
        #[label("invalid number")]
        span: SourceSpan,
    },
}
