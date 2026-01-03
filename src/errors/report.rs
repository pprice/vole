// src/errors/report.rs
//! Rendering utilities for miette diagnostics.

use miette::{Diagnostic, GraphicalReportHandler, GraphicalTheme, ThemeCharacters, ThemeStyles};
use std::io::Write as IoWrite;

/// Create a handler for terminal output (unicode + colors).
pub fn terminal_handler() -> GraphicalReportHandler {
    let theme = GraphicalTheme {
        characters: ThemeCharacters::unicode(),
        styles: ThemeStyles::ansi(),
    };
    GraphicalReportHandler::new_themed(theme)
}

/// Create a handler for snapshot testing (ascii + no colors).
pub fn snapshot_handler() -> GraphicalReportHandler {
    let theme = GraphicalTheme {
        characters: ThemeCharacters::ascii(),
        styles: ThemeStyles::none(),
    };
    GraphicalReportHandler::new_themed(theme)
}

/// Render to stderr with unicode/colors.
pub fn render_to_stderr(report: &dyn Diagnostic) {
    let handler = terminal_handler();
    let mut output = String::new();
    if handler.render_report(&mut output, report).is_ok() {
        eprint!("{}", output);
    }
}

/// Render to a buffer without colors (for snapshots/testing).
pub fn render_to_string(report: &dyn Diagnostic) -> String {
    let mut output = String::new();
    let handler = snapshot_handler();
    let _ = handler.render_report(&mut output, report);
    output
}

/// Render to any Write impl.
pub fn render_to_writer<W: IoWrite>(report: &dyn Diagnostic, mut writer: W) -> std::io::Result<()> {
    let output = render_to_string(report);
    writer.write_all(output.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::LexerError;
    use miette::NamedSource;

    #[test]
    fn render_lexer_error_to_string() {
        let err = LexerError::UnexpectedCharacter {
            ch: '@',
            span: (0, 1).into(),
        };
        let report = miette::Report::new(err)
            .with_source_code(NamedSource::new("test.vole", "@".to_string()));

        let output = render_to_string(report.as_ref());
        assert!(output.contains("E0001"), "should contain error code");
        assert!(
            output.contains("unexpected character"),
            "should contain message"
        );
        assert!(output.contains("@"), "should contain the character");
    }

    #[test]
    fn render_with_help() {
        let err = LexerError::UnterminatedString {
            span: (0, 5).into(),
        };
        let report = miette::Report::new(err)
            .with_source_code(NamedSource::new("test.vole", "\"hello".to_string()));

        let output = render_to_string(report.as_ref());
        assert!(output.contains("E0002"), "should contain error code");
        assert!(output.contains("help"), "should contain help text");
    }
}
