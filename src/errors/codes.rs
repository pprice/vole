// src/errors/codes.rs
//! Error codes and metadata for the Vole compiler.
//!
//! Error codes follow void's numbering scheme:
//! - E0xxx: Lexer errors
//! - E1xxx: Parser errors
//! - E2xxx: Semantic analysis errors

/// Error severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

/// Error metadata - static definition
#[derive(Debug, Clone)]
pub struct ErrorInfo {
    pub code: u16,
    pub message: &'static str,
    pub severity: Severity,
    pub hint: Option<&'static str>,
    pub related_template: Option<&'static str>,
}

impl ErrorInfo {
    /// Format error code as "Exxxx" for errors or "Wxxxx" for warnings
    pub fn code_string(&self) -> String {
        let prefix = if self.severity == Severity::Warning {
            "W"
        } else {
            "E"
        };
        format!("{}{:04}", prefix, self.code)
    }
}

// =============================================================================
// Lexer Errors (E0xxx)
// =============================================================================

/// E0001: Unexpected character encountered during lexing
pub const LEXER_UNEXPECTED_CHARACTER: ErrorInfo = ErrorInfo {
    code: 1,
    message: "unexpected character '{}'",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E0002: String literal was not properly terminated
pub const LEXER_UNTERMINATED_STRING: ErrorInfo = ErrorInfo {
    code: 2,
    message: "unterminated string literal",
    severity: Severity::Error,
    hint: Some("add a closing '\"' to terminate the string"),
    related_template: None,
};

/// E0005: Invalid number literal format
pub const LEXER_INVALID_NUMBER: ErrorInfo = ErrorInfo {
    code: 5,
    message: "invalid number literal",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

// =============================================================================
// Parser Errors (E1xxx)
// =============================================================================

/// E1001: Expected an expression but found something else
pub const PARSER_EXPECTED_EXPRESSION: ErrorInfo = ErrorInfo {
    code: 1001,
    message: "expected expression, found '{}'",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E1002: Expected a specific token but found something else
pub const PARSER_EXPECTED_TOKEN: ErrorInfo = ErrorInfo {
    code: 1002,
    message: "expected '{}', found '{}'",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E1003: Encountered an unexpected token
pub const PARSER_UNEXPECTED_TOKEN: ErrorInfo = ErrorInfo {
    code: 1003,
    message: "unexpected token '{}'",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E1004: Expected a type annotation
pub const PARSER_EXPECTED_TYPE: ErrorInfo = ErrorInfo {
    code: 1004,
    message: "expected type annotation",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E1006: Expected an identifier
pub const PARSER_EXPECTED_IDENTIFIER: ErrorInfo = ErrorInfo {
    code: 1006,
    message: "expected identifier",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E1007: Expected a block
pub const PARSER_EXPECTED_BLOCK: ErrorInfo = ErrorInfo {
    code: 1007,
    message: "expected block",
    severity: Severity::Error,
    hint: Some("blocks start with '{'"),
    related_template: None,
};

// =============================================================================
// Semantic Analysis Errors (E2xxx)
// =============================================================================

/// E2001: Type mismatch between expected and actual types
pub const SEMA_TYPE_MISMATCH: ErrorInfo = ErrorInfo {
    code: 2001,
    message: "expected {}, found {}",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E2002: Reference to an undefined variable
pub const SEMA_UNDEFINED_VARIABLE: ErrorInfo = ErrorInfo {
    code: 2002,
    message: "undefined variable '{}'",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E2006: Attempted assignment to an immutable variable
pub const SEMA_IMMUTABLE_VARIABLE: ErrorInfo = ErrorInfo {
    code: 2006,
    message: "cannot assign to immutable variable '{}'",
    severity: Severity::Error,
    hint: Some("consider declaring with 'let mut' to make it mutable"),
    related_template: Some("'{}' declared as immutable here"),
};

/// E2008: Break statement used outside of a loop
pub const SEMA_INVALID_BREAK: ErrorInfo = ErrorInfo {
    code: 2008,
    message: "break outside of loop",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E2012: Wrong number of arguments in function call
pub const SEMA_WRONG_ARGUMENT_COUNT: ErrorInfo = ErrorInfo {
    code: 2012,
    message: "expected {} arguments, found {}",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

/// E2027: Condition expression is not a boolean
pub const SEMA_CONDITION_NOT_BOOL: ErrorInfo = ErrorInfo {
    code: 2027,
    message: "condition must be boolean, found {}",
    severity: Severity::Error,
    hint: None,
    related_template: None,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_code_format() {
        assert_eq!(SEMA_TYPE_MISMATCH.code_string(), "E2001");
        assert_eq!(LEXER_UNEXPECTED_CHARACTER.code_string(), "E0001");
    }

    #[test]
    fn lexer_error_codes() {
        assert_eq!(LEXER_UNEXPECTED_CHARACTER.code, 1);
        assert_eq!(LEXER_UNTERMINATED_STRING.code, 2);
        assert_eq!(LEXER_INVALID_NUMBER.code, 5);
    }

    #[test]
    fn parser_error_codes() {
        assert_eq!(PARSER_EXPECTED_EXPRESSION.code, 1001);
        assert_eq!(PARSER_EXPECTED_TOKEN.code, 1002);
        assert_eq!(PARSER_UNEXPECTED_TOKEN.code, 1003);
        assert_eq!(PARSER_EXPECTED_TYPE.code, 1004);
        assert_eq!(PARSER_EXPECTED_IDENTIFIER.code, 1006);
        assert_eq!(PARSER_EXPECTED_BLOCK.code, 1007);
    }

    #[test]
    fn sema_error_codes() {
        assert_eq!(SEMA_TYPE_MISMATCH.code, 2001);
        assert_eq!(SEMA_UNDEFINED_VARIABLE.code, 2002);
        assert_eq!(SEMA_IMMUTABLE_VARIABLE.code, 2006);
        assert_eq!(SEMA_INVALID_BREAK.code, 2008);
        assert_eq!(SEMA_WRONG_ARGUMENT_COUNT.code, 2012);
        assert_eq!(SEMA_CONDITION_NOT_BOOL.code, 2027);
    }

    #[test]
    fn warning_code_format() {
        // Create a warning to test W prefix
        let warning = ErrorInfo {
            code: 1,
            message: "test warning",
            severity: Severity::Warning,
            hint: None,
            related_template: None,
        };
        assert_eq!(warning.code_string(), "W0001");
    }

    #[test]
    fn severity_equality() {
        assert_eq!(Severity::Error, Severity::Error);
        assert_ne!(Severity::Error, Severity::Warning);
        assert_ne!(Severity::Warning, Severity::Note);
    }

    #[test]
    fn error_info_has_related_template() {
        assert!(SEMA_IMMUTABLE_VARIABLE.related_template.is_some());
        assert!(SEMA_TYPE_MISMATCH.related_template.is_none());
    }
}
