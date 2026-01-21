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

    #[error("invalid external module path")]
    #[diagnostic(
        code(E1020),
        help("expected format \"provider:module\" (e.g., \"std:string\")")
    )]
    InvalidExternalModulePath {
        #[label("invalid module path")]
        span: SourceSpan,
    },

    #[error("expected string literal for module path")]
    #[diagnostic(code(E1021))]
    ExpectedModulePath {
        #[label("expected \"provider:module\"")]
        span: SourceSpan,
    },

    #[error("expected 'as' after native function name")]
    #[diagnostic(code(E1022))]
    ExpectedAs {
        #[label("expected 'as'")]
        span: SourceSpan,
    },

    #[error("duplicate external block")]
    #[diagnostic(code(E1023))]
    DuplicateExternalBlock {
        #[label("second external block")]
        span: SourceSpan,
    },

    #[error("duplicate statics block")]
    #[diagnostic(code(E1024), help("only one statics block is allowed per declaration"))]
    DuplicateStaticsBlock {
        #[label("second statics block")]
        span: SourceSpan,
    },

    #[error("missing type annotation for parameter '{name}'")]
    #[diagnostic(code(E1025), help("add a type annotation: {name}: Type"))]
    MissingTypeAnnotation {
        name: String,
        #[label("type annotation required")]
        span: SourceSpan,
    },

    #[error("nested tests blocks are not allowed")]
    #[diagnostic(
        code(E1026),
        help("tests blocks must be flat; use separate tests blocks instead")
    )]
    NestedTestsBlock {
        #[label("nested tests block not allowed")]
        span: SourceSpan,
    },

    #[error("declarations must appear before test cases")]
    #[diagnostic(code(E1027), help("move this declaration before the first test case"))]
    DeclarationAfterTest {
        #[label("declaration not allowed after test cases")]
        span: SourceSpan,
    },
}
