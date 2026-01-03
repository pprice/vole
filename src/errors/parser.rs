// src/errors/parser.rs
//! Parser errors (E1xxx).

#![allow(unused_assignments)] // False positives from thiserror derive

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Error, Debug, Diagnostic, Clone)]
pub enum ParserError {
    #[error("expected expression, found '{found}'")]
    #[diagnostic(code(E1001))]
    ExpectedExpression {
        found: String,
        #[label("expected expression")]
        span: SourceSpan,
    },

    #[error("expected '{expected}', found '{found}'")]
    #[diagnostic(code(E1002))]
    ExpectedToken {
        expected: String,
        found: String,
        #[label("unexpected token")]
        span: SourceSpan,
    },

    #[error("unexpected token '{token}'")]
    #[diagnostic(code(E1003))]
    UnexpectedToken {
        token: String,
        #[label("unexpected")]
        span: SourceSpan,
    },

    #[error("expected type annotation")]
    #[diagnostic(code(E1004))]
    ExpectedType {
        #[label("expected type")]
        span: SourceSpan,
    },

    #[error("expected identifier")]
    #[diagnostic(code(E1006))]
    ExpectedIdentifier {
        #[label("expected identifier")]
        span: SourceSpan,
    },

    #[error("expected block")]
    #[diagnostic(code(E1007), help("blocks start with '{{'"))]
    ExpectedBlock {
        #[label("expected block here")]
        span: SourceSpan,
    },

    #[error("expected pattern")]
    #[diagnostic(
        code(E1010),
        help("patterns can be literals (1, \"hello\"), identifiers, or '_'")
    )]
    ExpectedPattern {
        #[label("expected pattern")]
        span: SourceSpan,
    },

    #[error("expected '=>' after pattern")]
    #[diagnostic(code(E1011))]
    ExpectedFatArrow {
        #[label("expected '=>'")]
        span: SourceSpan,
    },
}
