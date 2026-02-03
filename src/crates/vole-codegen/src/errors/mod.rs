// src/errors/codegen.rs
//! Code generation errors.
//!
//! These are internal compiler errors (ICEs) that indicate bugs in the compiler
//! or unimplemented features, not user errors. They provide structured context
//! for debugging.

use std::fmt;

/// Code generation error with context for debugging.
#[derive(Debug, Clone)]
pub enum CodegenError {
    /// Feature not yet implemented in codegen
    UnsupportedFeature {
        feature: &'static str,
        context: Option<String>,
    },

    /// Wrong number of arguments to a builtin or intrinsic
    ArgumentCount {
        function: &'static str,
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

impl CodegenError {
    /// Create an unsupported feature error
    pub fn unsupported(feature: &'static str) -> Self {
        CodegenError::UnsupportedFeature {
            feature,
            context: None,
        }
    }

    /// Create an unsupported feature error with context
    pub fn unsupported_with_context(feature: &'static str, context: impl Into<String>) -> Self {
        CodegenError::UnsupportedFeature {
            feature,
            context: Some(context.into()),
        }
    }

    /// Create an argument count error
    pub fn arg_count(function: &'static str, expected: usize, found: usize) -> Self {
        CodegenError::ArgumentCount {
            function,
            expected,
            found,
        }
    }

    /// Create a type mismatch error
    pub fn type_mismatch(
        context: &'static str,
        expected: impl Into<String>,
        found: impl Into<String>,
    ) -> Self {
        CodegenError::TypeMismatch {
            context,
            expected: expected.into(),
            found: found.into(),
        }
    }

    /// Create a not found error
    pub fn not_found(kind: &'static str, name: impl Into<String>) -> Self {
        CodegenError::NotFound {
            kind,
            name: name.into(),
        }
    }

    /// Create an internal error
    pub fn internal(message: &'static str) -> Self {
        CodegenError::InternalError {
            message,
            context: None,
        }
    }

    /// Create an internal error with context
    pub fn internal_with_context(message: &'static str, context: impl Into<String>) -> Self {
        CodegenError::InternalError {
            message,
            context: Some(context.into()),
        }
    }

    /// Create a missing resource error
    pub fn missing_resource(resource: &'static str) -> Self {
        CodegenError::MissingResource {
            resource,
            context: None,
        }
    }
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CodegenError::UnsupportedFeature { feature, context } => {
                write!(f, "unsupported feature: {}", feature)?;
                if let Some(ctx) = context {
                    write!(f, " ({})", ctx)?;
                }
                Ok(())
            }
            CodegenError::ArgumentCount {
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
            CodegenError::TypeMismatch {
                context,
                expected,
                found,
            } => {
                write!(f, "{}: expected {}, found {}", context, expected, found)
            }
            CodegenError::NotFound { kind, name } => {
                write!(f, "{} not found: {}", kind, name)
            }
            CodegenError::InternalError { message, context } => {
                write!(f, "internal error: {}", message)?;
                if let Some(ctx) = context {
                    write!(f, " ({})", ctx)?;
                }
                Ok(())
            }
            CodegenError::MissingResource { resource, context } => {
                write!(f, "missing resource: {}", resource)?;
                if let Some(ctx) = context {
                    write!(f, " ({})", ctx)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for CodegenError {}

/// Result type alias for codegen operations.
pub type CodegenResult<T> = Result<T, CodegenError>;

// Convenience conversion from CodegenError to String
impl From<CodegenError> for String {
    fn from(err: CodegenError) -> String {
        err.to_string()
    }
}

// Convenience conversion from String to CodegenError (for legacy error strings)
// This wraps arbitrary strings as internal errors during migration.
impl From<String> for CodegenError {
    fn from(msg: String) -> Self {
        // Parse common patterns into appropriate variants, otherwise InternalError
        CodegenError::InternalError {
            message: "legacy error",
            context: Some(msg),
        }
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
}
