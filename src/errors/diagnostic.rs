// src/errors/diagnostic.rs
//! Diagnostic types for structured error reporting.

use super::codes::{ErrorInfo, Severity};
use crate::frontend::Span;

/// Related information attached to a diagnostic (e.g., "declared here")
#[derive(Debug, Clone)]
pub struct RelatedInfo {
    pub span: Span,
    pub file: String,
    pub message: String,
    pub source_line: Option<String>,
}

/// A structured diagnostic with location, message, and related info
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub info: &'static ErrorInfo,
    pub span: Span,
    pub file: String,
    pub formatted_message: String,
    pub source_line: Option<String>,
    pub related: Vec<RelatedInfo>,
}

impl Diagnostic {
    /// Get severity from the error info
    pub fn severity(&self) -> Severity {
        self.info.severity
    }

    /// Get error code
    pub fn code(&self) -> u16 {
        self.info.code
    }

    /// Format error code as "Exxxx" or "Wxxxx"
    pub fn code_string(&self) -> String {
        self.info.code_string()
    }
}

/// Extract a line from source by line number (1-indexed)
pub fn get_line_from_source(source: &str, line_number: u32) -> Option<String> {
    if line_number == 0 {
        return None;
    }
    source
        .lines()
        .nth((line_number - 1) as usize)
        .map(|s| s.to_string())
}

/// Builder for creating diagnostics with source context
pub struct DiagnosticBuilder {
    file: String,
    source: String,
}

impl DiagnosticBuilder {
    pub fn new(file: &str, source: &str) -> Self {
        Self {
            file: file.to_string(),
            source: source.to_string(),
        }
    }

    /// Get a specific line from source (1-indexed)
    pub fn get_line(&self, line: u32) -> Option<String> {
        get_line_from_source(&self.source, line)
    }

    /// Create a diagnostic with source context
    pub fn error(&self, info: &'static ErrorInfo, span: Span, message: String) -> Diagnostic {
        Diagnostic {
            info,
            span,
            file: self.file.clone(),
            formatted_message: message,
            source_line: self.get_line(span.line),
            related: vec![],
        }
    }

    /// Create a diagnostic with related info
    pub fn error_with_related(
        &self,
        info: &'static ErrorInfo,
        span: Span,
        message: String,
        related: Vec<RelatedInfo>,
    ) -> Diagnostic {
        Diagnostic {
            info,
            span,
            file: self.file.clone(),
            formatted_message: message,
            source_line: self.get_line(span.line),
            related,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::codes::SEMA_TYPE_MISMATCH;

    #[test]
    fn get_line_from_source_works() {
        let source = "line one\nline two\nline three";
        assert_eq!(
            get_line_from_source(source, 1),
            Some("line one".to_string())
        );
        assert_eq!(
            get_line_from_source(source, 2),
            Some("line two".to_string())
        );
        assert_eq!(
            get_line_from_source(source, 3),
            Some("line three".to_string())
        );
        assert_eq!(get_line_from_source(source, 4), None);
        assert_eq!(get_line_from_source(source, 0), None);
    }

    #[test]
    fn diagnostic_builder_creates_diagnostic() {
        let builder = DiagnosticBuilder::new("test.vole", "let x = 1\nlet y = 2");
        let span = Span::new(0, 9, 1, 1);
        let diag = builder.error(
            &SEMA_TYPE_MISMATCH,
            span,
            "expected i64, found bool".to_string(),
        );

        assert_eq!(diag.code(), 2001);
        assert_eq!(diag.code_string(), "E2001");
        assert_eq!(diag.file, "test.vole");
        assert_eq!(diag.source_line, Some("let x = 1".to_string()));
    }
}
