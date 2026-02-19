// src/formatter/mod.rs
//! Main entry point for the Vole formatter.
//!
//! Coordinates parsing and rendering to produce formatted output.
//! Currently a stub that returns input unchanged.

use super::config::FormatConfig;
use super::printer;
use pretty::Arena;
use vole_frontend::{ModuleId, Parser};

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
/// Parses the source into an AST and renders it back with canonical style.
pub fn format(source: &str, config: FormatConfig) -> Result<FormatResult, FormatError> {
    // Parse source into AST
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .map_err(|e| FormatError::ParseError(format!("{:?}", e.error)))?;
    let interner = parser.into_interner();

    // Convert AST to Doc and render
    let arena = Arena::new();
    let doc = printer::print_program(&arena, &program, &interner);
    let mut output = String::new();
    doc.render_fmt(config.max_line_width as usize, &mut output)
        .expect("render to string cannot fail");

    // Remove trailing whitespace from blank lines (artifact of nesting with hardlines)
    output = output
        .lines()
        .map(|line| line.trim_end())
        .collect::<Vec<_>>()
        .join("\n");

    // Ensure trailing newline
    if !output.ends_with('\n') {
        output.push('\n');
    }

    let changed = output != source;

    Ok(FormatResult { output, changed })
}

#[cfg(test)]
mod tests;
