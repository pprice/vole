// src/errors/sema.rs
//! Semantic analysis errors (E2xxx).

#![allow(unused_assignments)] // False positives from thiserror derive

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Error, Debug, Diagnostic, Clone)]
pub enum SemanticError {
    #[error("expected {expected}, found {found}")]
    #[diagnostic(code(E2001))]
    TypeMismatch {
        expected: String,
        found: String,
        #[label("type mismatch")]
        span: SourceSpan,
    },

    #[error("undefined variable '{name}'")]
    #[diagnostic(code(E2002))]
    UndefinedVariable {
        name: String,
        #[label("not found in scope")]
        span: SourceSpan,
    },

    #[error("cannot assign to immutable variable '{name}'")]
    #[diagnostic(
        code(E2006),
        help("consider declaring with 'let mut' to make it mutable")
    )]
    ImmutableAssignment {
        name: String,
        #[label("cannot assign")]
        span: SourceSpan,
        #[label("declared as immutable here")]
        declaration: SourceSpan,
    },

    #[error("break outside of loop")]
    #[diagnostic(code(E2008))]
    InvalidBreak {
        #[label("not inside a loop")]
        span: SourceSpan,
    },

    #[error("expected {expected} arguments, found {found}")]
    #[diagnostic(code(E2012))]
    WrongArgumentCount {
        expected: usize,
        found: usize,
        #[label("wrong number of arguments")]
        span: SourceSpan,
    },

    #[error("condition must be boolean, found {found}")]
    #[diagnostic(code(E2027))]
    ConditionNotBool {
        found: String,
        #[label("expected bool")]
        span: SourceSpan,
    },
}
