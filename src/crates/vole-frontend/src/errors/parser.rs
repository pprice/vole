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

    #[error("type parameter '{name}' starts with a digit")]
    #[diagnostic(
        code(E1028),
        help("type parameters must start with a letter, not a digit")
    )]
    TypeParamStartsWithDigit {
        name: String,
        #[label("invalid type parameter name")]
        span: SourceSpan,
    },

    #[error("type parameter '{name}' starts with reserved prefix '__'")]
    #[diagnostic(
        code(E1029),
        help("the '__' prefix is reserved for internal use; rename this type parameter")
    )]
    TypeParamReservedPrefix {
        name: String,
        #[label("reserved prefix")]
        span: SourceSpan,
    },

    #[error("sentinel declarations cannot have a body")]
    #[diagnostic(
        code(E1030),
        help("sentinel declarations are body-less: just `sentinel Name`")
    )]
    SentinelCannotHaveBody {
        #[label("unexpected body")]
        span: SourceSpan,
    },

    #[error("only declarations are allowed at the top level")]
    #[diagnostic(
        code(E1031),
        help("use func, class, struct, interface, implement, tests, or let")
    )]
    StatementAtTopLevel {
        #[label("expected a declaration, not a statement or expression")]
        span: SourceSpan,
    },

    #[error("to define a function, use `func {name}() {{ ... }}`")]
    #[diagnostic(code(E1032), help("add the `func` keyword before the function name"))]
    MissingFuncKeyword {
        name: String,
        #[label("missing `func` keyword")]
        span: SourceSpan,
    },

    #[error("to define a function, use `func` instead of `{keyword}`")]
    #[diagnostic(
        code(E1033),
        help("Vole uses `func` to define functions: `func {name}() {{ ... }}`")
    )]
    WrongFuncKeyword {
        keyword: String,
        name: String,
        #[label("use `func` here")]
        span: SourceSpan,
    },

    #[error("import without assignment")]
    #[diagnostic(
        code(E1034),
        help("in Vole, imports are expressions: `let name = import \"module\"`")
    )]
    BareImport {
        #[label("`import` must be assigned to a variable")]
        span: SourceSpan,
    },

    #[error("`from ... import` is not valid Vole syntax")]
    #[diagnostic(
        code(E1035),
        help("use `let {{ name }} = import \"module\"` to import specific items")
    )]
    PythonStyleImport {
        #[label("not valid Vole syntax")]
        span: SourceSpan,
    },

    #[error("`use` is not valid Vole syntax")]
    #[diagnostic(
        code(E1036),
        help("in Vole, imports are expressions: `let name = import \"module\"`")
    )]
    RustStyleUse {
        #[label("not valid Vole syntax")]
        span: SourceSpan,
    },

    #[error("duplicate default arm in external where mapping")]
    #[diagnostic(
        code(E1037),
        help("only one `default => \"...\"` arm is allowed in a where mapping block")
    )]
    DuplicateWhereDefaultArm {
        #[label("duplicate default arm")]
        span: SourceSpan,
    },

    #[error("`let mut` is not valid Vole syntax")]
    #[diagnostic(
        code(E1038),
        help("use `var` instead of `let mut` for mutable bindings")
    )]
    LetMutDeprecated {
        #[label("replace `let mut` with `var`")]
        span: SourceSpan,
    },
}
