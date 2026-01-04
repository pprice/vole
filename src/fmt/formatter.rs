// src/fmt/formatter.rs
//! Main entry point for the Vole formatter.
//!
//! Coordinates parsing and rendering to produce formatted output.
//! Currently a stub that returns input unchanged.

use super::config::FormatConfig;

/// Error type for formatting operations.
#[derive(Debug, Clone)]
pub enum FormatError {
    /// Source code failed to parse
    ParseError(String),
}

impl std::fmt::Display for FormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FormatError::ParseError(msg) => write!(f, "parse error: {}", msg),
        }
    }
}

impl std::error::Error for FormatError {}

/// Result of formatting source code.
#[derive(Debug)]
pub struct FormatResult {
    /// The formatted output
    pub output: String,
    /// Whether the output differs from the input
    pub changed: bool,
}

/// Format source code and return the formatted result.
///
/// Currently a stub that returns the input unchanged. The actual formatter
/// will parse the source into an AST and render it back with canonical style.
pub fn format(source: &str, _config: FormatConfig) -> Result<FormatResult, FormatError> {
    // TODO: Implement actual formatting:
    // 1. Parse source into AST
    // 2. Render AST back with canonical formatting
    // 3. Preserve comments from original source

    // Stub: return input unchanged (ensures trailing newline)
    let output = if source.ends_with('\n') {
        source.to_string()
    } else {
        format!("{}\n", source)
    };

    let changed = output != source;

    Ok(FormatResult { output, changed })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fmt::CANONICAL;

    #[test]
    fn test_format_stub_unchanged() {
        let source = "let x = 1\n";
        let result = format(source, CANONICAL).unwrap();
        assert_eq!(result.output, source);
        assert!(!result.changed);
    }

    #[test]
    fn test_format_adds_trailing_newline() {
        let source = "let x = 1";
        let result = format(source, CANONICAL).unwrap();
        assert_eq!(result.output, "let x = 1\n");
        assert!(result.changed);
    }
}
