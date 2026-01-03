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

    #[error("non-exhaustive match")]
    #[diagnostic(
        code(E2030),
        help("add a wildcard pattern '_' or identifier to catch remaining cases")
    )]
    NonExhaustiveMatch {
        #[label("match may not cover all cases")]
        span: SourceSpan,
    },

    #[error("match arms have incompatible types: expected {expected}, found {found}")]
    #[diagnostic(code(E2031))]
    MatchArmTypeMismatch {
        expected: String,
        found: String,
        #[label("first arm has type {expected}")]
        first_arm: SourceSpan,
        #[label("this arm has type {found}")]
        span: SourceSpan,
    },

    #[error("match guard must be boolean, found {found}")]
    #[diagnostic(code(E2032))]
    MatchGuardNotBool {
        found: String,
        #[label("expected bool")]
        span: SourceSpan,
    },

    #[error("pattern type mismatch: expected {expected}, found {found}")]
    #[diagnostic(code(E2033))]
    PatternTypeMismatch {
        expected: String,
        found: String,
        #[label("pattern doesn't match scrutinee type")]
        span: SourceSpan,
    },

    #[error("cannot use return value of void function")]
    #[diagnostic(code(E2040), help("void functions don't return a usable value"))]
    VoidReturnUsed {
        #[label("void function called here")]
        span: SourceSpan,
    },

    #[error("null coalescing requires optional type, found {found}")]
    #[diagnostic(code(E2041))]
    NullCoalesceNotOptional {
        found: String,
        #[label("expected optional type")]
        span: SourceSpan,
    },

    #[error("type '{tested}' is not a variant of '{union_type}'")]
    #[diagnostic(code(E2042))]
    IsNotVariant {
        tested: String,
        union_type: String,
        #[label("not a variant of the union")]
        span: SourceSpan,
    },

    #[error("cannot infer type of lambda parameter '{name}'")]
    #[diagnostic(
        code(E2043),
        help("add a type annotation: ({name}: Type) => ...")
    )]
    CannotInferLambdaParam {
        name: String,
        #[label("type cannot be inferred")]
        span: SourceSpan,
    },

    #[error("cannot call non-function type '{ty}'")]
    #[diagnostic(code(E2044))]
    NotCallable {
        ty: String,
        #[label("not a function")]
        span: SourceSpan,
    },
}
