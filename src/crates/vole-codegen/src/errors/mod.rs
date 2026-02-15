// src/errors/codegen.rs
//! Code generation errors.
//!
//! These are internal compiler errors (ICEs) that indicate bugs in the compiler
//! or unimplemented features, not user errors. They provide structured context
//! for debugging.
//!
//! Error code ranges:
//! - E0xxx: Lexer errors
//! - E1xxx: Parser errors
//! - E2xxx: Semantic errors
//! - E3xxx: Codegen errors (this module)

use miette::{Diagnostic, LabeledSpan};
use std::fmt;
use thiserror::Error;
use vole_frontend::Span;

/// The kind of code generation error.
#[derive(Debug, Clone)]
pub enum CodegenErrorKind {
    /// Feature not yet implemented in codegen
    UnsupportedFeature {
        feature: &'static str,
        context: Option<String>,
    },

    /// Wrong number of arguments to a builtin or intrinsic
    ArgumentCount {
        function: String,
        expected: usize,
        found: usize,
    },

    /// Type mismatch in codegen (should have been caught by sema)
    TypeMismatch {
        context: &'static str,
        expected: String,
        found: String,
    },

    /// Function, variable, or type not found
    NotFound { kind: &'static str, name: String },

    /// Internal invariant violation (compiler bug)
    InternalError {
        message: &'static str,
        context: Option<String>,
    },

    /// Required resource not available
    MissingResource {
        resource: &'static str,
        context: Option<String>,
    },
}

/// Code generation error with optional source span for diagnostics.
#[derive(Debug, Clone, Error)]
#[error("{kind}")]
pub struct CodegenError {
    /// The kind of error.
    pub kind: CodegenErrorKind,
    /// Source location where the error occurred, if available.
    pub span: Option<Span>,
}

impl CodegenError {
    /// Create an unsupported feature error
    pub fn unsupported(feature: &'static str) -> Self {
        CodegenErrorKind::UnsupportedFeature {
            feature,
            context: None,
        }
        .into()
    }

    /// Create an unsupported feature error with context
    pub fn unsupported_with_context(feature: &'static str, context: impl Into<String>) -> Self {
        CodegenErrorKind::UnsupportedFeature {
            feature,
            context: Some(context.into()),
        }
        .into()
    }

    /// Create an argument count error
    pub fn arg_count(function: impl Into<String>, expected: usize, found: usize) -> Self {
        CodegenErrorKind::ArgumentCount {
            function: function.into(),
            expected,
            found,
        }
        .into()
    }

    /// Create a type mismatch error
    pub fn type_mismatch(
        context: &'static str,
        expected: impl Into<String>,
        found: impl Into<String>,
    ) -> Self {
        CodegenErrorKind::TypeMismatch {
            context,
            expected: expected.into(),
            found: found.into(),
        }
        .into()
    }

    /// Create a not found error
    pub fn not_found(kind: &'static str, name: impl Into<String>) -> Self {
        CodegenErrorKind::NotFound {
            kind,
            name: name.into(),
        }
        .into()
    }

    /// Create an internal error
    pub fn internal(message: &'static str) -> Self {
        CodegenErrorKind::InternalError {
            message,
            context: None,
        }
        .into()
    }

    /// Create an internal error with context
    pub fn internal_with_context(message: &'static str, context: impl Into<String>) -> Self {
        CodegenErrorKind::InternalError {
            message,
            context: Some(context.into()),
        }
        .into()
    }

    /// Wrap a Cranelift module error
    pub fn cranelift(e: impl fmt::Display) -> Self {
        CodegenErrorKind::InternalError {
            message: "cranelift error",
            context: Some(e.to_string()),
        }
        .into()
    }

    /// Wrap an IO error
    pub fn io(e: impl fmt::Display) -> Self {
        CodegenErrorKind::InternalError {
            message: "io error",
            context: Some(e.to_string()),
        }
        .into()
    }

    /// Create a missing resource error
    pub fn missing_resource(resource: &'static str) -> Self {
        CodegenErrorKind::MissingResource {
            resource,
            context: None,
        }
        .into()
    }

    /// Attach a source span to this error for diagnostics.
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }
}

impl From<CodegenErrorKind> for CodegenError {
    fn from(kind: CodegenErrorKind) -> Self {
        CodegenError { kind, span: None }
    }
}

impl Diagnostic for CodegenError {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        let code: &'static str = match &self.kind {
            CodegenErrorKind::UnsupportedFeature { .. } => "E3001",
            CodegenErrorKind::ArgumentCount { .. } => "E3002",
            CodegenErrorKind::TypeMismatch { .. } => "E3003",
            CodegenErrorKind::NotFound { .. } => "E3004",
            CodegenErrorKind::InternalError { .. } => "E3005",
            CodegenErrorKind::MissingResource { .. } => "E3006",
        };
        Some(Box::new(code))
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let span = self.span?;
        let len = span.end.saturating_sub(span.start);
        let label = match &self.kind {
            CodegenErrorKind::UnsupportedFeature { feature, .. } => {
                format!("{} is not supported", feature)
            }
            CodegenErrorKind::ArgumentCount {
                expected, found, ..
            } => {
                format!("expected {} argument(s), found {}", expected, found)
            }
            CodegenErrorKind::TypeMismatch {
                expected, found, ..
            } => {
                format!("expected {}, found {}", expected, found)
            }
            CodegenErrorKind::NotFound { kind, .. } => format!("{} not found", kind),
            CodegenErrorKind::InternalError { message, .. } => message.to_string(),
            CodegenErrorKind::MissingResource { resource, .. } => {
                format!("{} not available", resource)
            }
        };
        let labeled = LabeledSpan::new(Some(label), span.start, len);
        Some(Box::new(std::iter::once(labeled)))
    }
}

impl fmt::Display for CodegenErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CodegenErrorKind::UnsupportedFeature { feature, context } => {
                write!(f, "unsupported feature: {}", feature)?;
                if let Some(ctx) = context {
                    write!(f, " ({})", ctx)?;
                }
                Ok(())
            }
            CodegenErrorKind::ArgumentCount {
                function,
                expected,
                found,
            } => {
                write!(
                    f,
                    "{} expects {} argument(s), got {}",
                    function, expected, found
                )
            }
            CodegenErrorKind::TypeMismatch {
                context,
                expected,
                found,
            } => {
                write!(f, "{}: expected {}, found {}", context, expected, found)
            }
            CodegenErrorKind::NotFound { kind, name } => {
                write!(f, "{} not found: {}", kind, name)
            }
            CodegenErrorKind::InternalError { message, context } => {
                write!(f, "internal error: {}", message)?;
                if let Some(ctx) = context {
                    write!(f, " ({})", ctx)?;
                }
                Ok(())
            }
            CodegenErrorKind::MissingResource { resource, context } => {
                write!(f, "missing resource: {}", resource)?;
                if let Some(ctx) = context {
                    write!(f, " ({})", ctx)?;
                }
                Ok(())
            }
        }
    }
}

/// Result type alias for codegen operations.
pub type CodegenResult<T> = Result<T, CodegenError>;

// Convenience conversion from CodegenError to String
impl From<CodegenError> for String {
    fn from(err: CodegenError) -> String {
        err.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsupported_feature() {
        let err = CodegenError::unsupported("complex call expressions");
        assert_eq!(
            err.to_string(),
            "unsupported feature: complex call expressions"
        );
    }

    #[test]
    fn test_unsupported_with_context() {
        let err = CodegenError::unsupported_with_context("method calls", "on type Option<Person>");
        assert_eq!(
            err.to_string(),
            "unsupported feature: method calls (on type Option<Person>)"
        );
    }

    #[test]
    fn test_arg_count() {
        let err = CodegenError::arg_count("println", 1, 3);
        assert_eq!(err.to_string(), "println expects 1 argument(s), got 3");
    }

    #[test]
    fn test_type_mismatch() {
        let err = CodegenError::type_mismatch("print_char argument", "i32 or i64", "string");
        assert_eq!(
            err.to_string(),
            "print_char argument: expected i32 or i64, found string"
        );
    }

    #[test]
    fn test_not_found() {
        let err = CodegenError::not_found("function", "calculate_sum");
        assert_eq!(err.to_string(), "function not found: calculate_sum");
    }

    #[test]
    fn test_internal_error() {
        let err = CodegenError::internal("And/Or should use short-circuit evaluation");
        assert_eq!(
            err.to_string(),
            "internal error: And/Or should use short-circuit evaluation"
        );
    }

    #[test]
    fn test_missing_resource() {
        let err = CodegenError::missing_resource("heap allocator");
        assert_eq!(err.to_string(), "missing resource: heap allocator");
    }

    #[test]
    fn test_with_span() {
        let span = Span {
            start: 10,
            end: 20,
            line: 1,
            column: 10,
            end_line: 1,
            end_column: 20,
        };
        let err = CodegenError::unsupported("test feature").with_span(span);
        assert_eq!(err.span, Some(span));
        assert_eq!(err.to_string(), "unsupported feature: test feature");
    }

    #[test]
    fn test_no_span_by_default() {
        let err = CodegenError::internal("test");
        assert_eq!(err.span, None);
    }

    #[test]
    fn test_error_codes() {
        use miette::Diagnostic;
        let cases: Vec<(CodegenError, &str)> = vec![
            (CodegenError::unsupported("x"), "E3001"),
            (CodegenError::arg_count("f", 1, 2), "E3002"),
            (CodegenError::type_mismatch("c", "a", "b"), "E3003"),
            (CodegenError::not_found("fn", "x"), "E3004"),
            (CodegenError::internal("x"), "E3005"),
            (CodegenError::missing_resource("x"), "E3006"),
        ];
        for (err, expected_code) in cases {
            let code = err.code().expect("should have error code");
            assert_eq!(code.to_string(), expected_code);
        }
    }

    #[test]
    fn test_labels_with_span() {
        use miette::Diagnostic;
        let span = Span {
            start: 10,
            end: 20,
            line: 1,
            column: 10,
            end_line: 1,
            end_column: 20,
        };
        let err = CodegenError::unsupported("closures").with_span(span);
        let labels: Vec<_> = err.labels().unwrap().collect();
        assert_eq!(labels.len(), 1);
    }

    #[test]
    fn test_labels_without_span() {
        use miette::Diagnostic;
        let err = CodegenError::unsupported("closures");
        assert!(err.labels().is_none());
    }
}
