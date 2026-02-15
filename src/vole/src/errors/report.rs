// src/errors/report.rs
//! Rendering utilities for miette diagnostics.
//!
//! We wrap diagnostics to inline the error code with the message.
//! miette displays: `CODE\n\n  × message`
//! We display: `  × [CODE]: message`

use miette::{
    Diagnostic, GraphicalReportHandler, GraphicalTheme, LabeledSpan, Severity, SourceCode,
    ThemeCharacters, ThemeStyles,
};
use std::fmt;
use std::io::Write as IoWrite;

use crate::cli::ColorMode;

/// Check if colors should be used for the given mode.
fn should_use_color(color_mode: ColorMode) -> bool {
    match color_mode {
        ColorMode::Auto => crate::commands::common::stdout_supports_color(),
        ColorMode::Always => true,
        ColorMode::Never => false,
    }
}

/// Wrapper that inlines the error code into the message.
/// Returns None for code() so miette won't print it separately.
struct InlineCodeDiagnostic<'a> {
    inner: &'a dyn Diagnostic,
    message: String,
}

impl<'a> InlineCodeDiagnostic<'a> {
    fn new(inner: &'a dyn Diagnostic) -> Self {
        let message = if let Some(code) = inner.code() {
            format!("[{}]: {}", code, inner)
        } else {
            inner.to_string()
        };
        Self { inner, message }
    }
}

impl fmt::Debug for InlineCodeDiagnostic<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.inner, f)
    }
}

impl fmt::Display for InlineCodeDiagnostic<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for InlineCodeDiagnostic<'_> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.inner.source()
    }
}

impl Diagnostic for InlineCodeDiagnostic<'_> {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None // Don't show code separately - it's in the message
    }

    fn severity(&self) -> Option<Severity> {
        self.inner.severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.inner.help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.inner.url()
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        self.inner.source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        self.inner.labels()
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        self.inner.related()
    }

    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.inner.diagnostic_source()
    }
}

/// Wrapper that adds additional help text to a diagnostic.
/// Used to provide context-sensitive hints (e.g., "wrap in func main" for vole run).
pub struct WithExtraHelp<'a> {
    inner: &'a dyn Diagnostic,
    extra_help: String,
}

impl<'a> WithExtraHelp<'a> {
    /// Create a wrapper that adds extra help text to the inner diagnostic.
    pub fn new(inner: &'a dyn Diagnostic, extra_help: impl Into<String>) -> Self {
        Self {
            inner,
            extra_help: extra_help.into(),
        }
    }
}

impl fmt::Debug for WithExtraHelp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.inner, f)
    }
}

impl fmt::Display for WithExtraHelp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.inner, f)
    }
}

impl std::error::Error for WithExtraHelp<'_> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.inner.source()
    }
}

impl Diagnostic for WithExtraHelp<'_> {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.inner.code()
    }

    fn severity(&self) -> Option<Severity> {
        self.inner.severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        // Combine original help with extra help
        let original_help = self.inner.help().map(|h| h.to_string());
        let combined = match original_help {
            Some(orig) => format!("{}\n  {}", orig, self.extra_help),
            None => self.extra_help.clone(),
        };
        Some(Box::new(combined))
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.inner.url()
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        self.inner.source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        self.inner.labels()
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn Diagnostic> + 'a>> {
        self.inner.related()
    }

    fn diagnostic_source(&self) -> Option<&dyn Diagnostic> {
        self.inner.diagnostic_source()
    }
}

/// Create a handler for terminal output (unicode + colors based on mode).
fn terminal_handler(color_mode: ColorMode) -> GraphicalReportHandler {
    let styles = if should_use_color(color_mode) {
        ThemeStyles::ansi()
    } else {
        ThemeStyles::none()
    };
    let theme = GraphicalTheme {
        characters: ThemeCharacters::unicode(),
        styles,
    };
    GraphicalReportHandler::new_themed(theme)
}

/// Create a handler for snapshot testing (ascii + no colors).
fn snapshot_handler() -> GraphicalReportHandler {
    let theme = GraphicalTheme {
        characters: ThemeCharacters::ascii(),
        styles: ThemeStyles::none(),
    };
    GraphicalReportHandler::new_themed(theme)
}

/// Render to stderr with unicode/colors.
pub fn render_to_stderr(report: &dyn Diagnostic, color_mode: ColorMode) {
    let handler = terminal_handler(color_mode);
    let wrapped = InlineCodeDiagnostic::new(report);
    let mut output = String::new();
    if handler.render_report(&mut output, &wrapped).is_ok() {
        eprint!("{}", output);
    }
}

/// Render to a buffer without colors (for snapshots/testing).
pub fn render_to_string(report: &dyn Diagnostic) -> String {
    let handler = snapshot_handler();
    let wrapped = InlineCodeDiagnostic::new(report);
    let mut output = String::new();
    let _ = handler.render_report(&mut output, &wrapped);
    output
}

/// Render to any Write impl (ASCII, for snapshots).
pub fn render_to_writer<W: IoWrite>(report: &dyn Diagnostic, mut writer: W) -> std::io::Result<()> {
    let output = render_to_string(report);
    writer.write_all(output.as_bytes())
}

/// Render to any Write impl with terminal formatting (unicode + colors).
pub fn render_to_writer_terminal<W: IoWrite>(
    report: &dyn Diagnostic,
    mut writer: W,
    color_mode: ColorMode,
) -> std::io::Result<()> {
    let handler = terminal_handler(color_mode);
    let wrapped = InlineCodeDiagnostic::new(report);
    let mut output = String::new();
    if handler.render_report(&mut output, &wrapped).is_ok() {
        writer.write_all(output.as_bytes())?;
    }
    Ok(())
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
