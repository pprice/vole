// src/errors/render.rs
//! Console rendering for diagnostics with ANSI color support.

use std::io::Write;
use super::diagnostic::{Diagnostic, RelatedInfo};
use super::codes::Severity;

/// ANSI color codes
struct Colors {
    use_color: bool,
}

impl Colors {
    fn new(use_color: bool) -> Self {
        Self { use_color }
    }

    fn bold_red(&self) -> &'static str {
        if self.use_color { "\x1b[1;31m" } else { "" }
    }

    fn bold_yellow(&self) -> &'static str {
        if self.use_color { "\x1b[1;33m" } else { "" }
    }

    fn cyan(&self) -> &'static str {
        if self.use_color { "\x1b[36m" } else { "" }
    }

    fn green(&self) -> &'static str {
        if self.use_color { "\x1b[32m" } else { "" }
    }

    fn reset(&self) -> &'static str {
        if self.use_color { "\x1b[0m" } else { "" }
    }
}

/// Console renderer for diagnostics
pub struct ConsoleRenderer<W: Write> {
    writer: W,
    colors: Colors,
}

impl<W: Write> ConsoleRenderer<W> {
    pub fn new(writer: W, use_color: bool) -> Self {
        Self {
            writer,
            colors: Colors::new(use_color),
        }
    }

    /// Render a single diagnostic
    pub fn render(&mut self, diag: &Diagnostic) -> std::io::Result<()> {
        self.render_header(diag)?;
        self.render_location(diag)?;
        if let Some(ref line) = diag.source_line {
            self.render_snippet(diag, line)?;
        }
        for related in &diag.related {
            self.render_related(related)?;
        }
        if let Some(hint) = diag.info.hint {
            self.render_hint(hint)?;
        }
        Ok(())
    }

    fn render_header(&mut self, diag: &Diagnostic) -> std::io::Result<()> {
        let style = self.severity_style(diag.severity());
        let severity_name = match diag.severity() {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
        };
        writeln!(
            self.writer,
            "{}{}{}[{}]: {}",
            style,
            severity_name,
            self.colors.reset(),
            diag.code_string(),
            diag.formatted_message
        )
    }

    fn render_location(&mut self, diag: &Diagnostic) -> std::io::Result<()> {
        writeln!(
            self.writer,
            "  {}-->{} {}:{}:{}",
            self.colors.cyan(),
            self.colors.reset(),
            diag.file,
            diag.span.line,
            diag.span.column
        )
    }

    fn render_snippet(&mut self, diag: &Diagnostic, source_line: &str) -> std::io::Result<()> {
        let line_num_width = count_digits(diag.span.line);

        // Empty line with pipe
        self.render_pipe(line_num_width)?;
        writeln!(self.writer)?;

        // Source line
        writeln!(
            self.writer,
            "{}{}{} | {}",
            self.colors.cyan(),
            diag.span.line,
            self.colors.reset(),
            source_line
        )?;

        // Caret line
        self.render_pipe(line_num_width)?;
        write!(self.writer, " ")?;

        // Spaces before caret (column is 1-indexed)
        let caret_pos = if diag.span.column > 0 { diag.span.column - 1 } else { 0 };
        for _ in 0..caret_pos {
            write!(self.writer, " ")?;
        }

        // Calculate caret length from span
        let caret_len = if diag.span.end_line == diag.span.line && diag.span.end_column > diag.span.column {
            (diag.span.end_column - diag.span.column) as usize
        } else {
            1 // Default to single caret for multi-line spans
        };

        // Render carets
        let style = self.severity_style(diag.severity());
        write!(self.writer, "{}", style)?;
        for _ in 0..caret_len {
            write!(self.writer, "^")?;
        }
        writeln!(self.writer, "{}", self.colors.reset())
    }

    fn render_related(&mut self, rel: &RelatedInfo) -> std::io::Result<()> {
        // Empty line
        writeln!(self.writer, "   |")?;

        // Note header
        writeln!(
            self.writer,
            "{}note{}: {}",
            self.colors.cyan(),
            self.colors.reset(),
            rel.message
        )?;

        // Location
        writeln!(
            self.writer,
            "  {}-->{} {}:{}:{}",
            self.colors.cyan(),
            self.colors.reset(),
            rel.file,
            rel.span.line,
            rel.span.column
        )?;

        // Source snippet if available
        if let Some(ref line) = rel.source_line {
            let line_num_width = count_digits(rel.span.line);
            self.render_pipe(line_num_width)?;
            writeln!(self.writer)?;

            writeln!(
                self.writer,
                "{}{}{} | {}",
                self.colors.cyan(),
                rel.span.line,
                self.colors.reset(),
                line
            )?;

            self.render_pipe(line_num_width)?;
            write!(self.writer, " ")?;
            let caret_pos = if rel.span.column > 0 { rel.span.column - 1 } else { 0 };
            for _ in 0..caret_pos {
                write!(self.writer, " ")?;
            }

            // Calculate caret length from span
            let caret_len = if rel.span.end_line == rel.span.line && rel.span.end_column > rel.span.column {
                (rel.span.end_column - rel.span.column) as usize
            } else {
                1 // Default to single caret for multi-line spans
            };

            // Render carets
            write!(self.writer, "{}", self.colors.cyan())?;
            for _ in 0..caret_len {
                write!(self.writer, "^")?;
            }
            writeln!(self.writer, "{}", self.colors.reset())?;
        }

        Ok(())
    }

    fn render_hint(&mut self, hint: &str) -> std::io::Result<()> {
        writeln!(
            self.writer,
            "   {}= hint{}: {}",
            self.colors.green(),
            self.colors.reset(),
            hint
        )
    }

    fn render_pipe(&mut self, padding: u32) -> std::io::Result<()> {
        for _ in 0..padding {
            write!(self.writer, " ")?;
        }
        write!(self.writer, " {}|{}", self.colors.cyan(), self.colors.reset())
    }

    fn severity_style(&self, severity: Severity) -> &'static str {
        match severity {
            Severity::Error => self.colors.bold_red(),
            Severity::Warning => self.colors.bold_yellow(),
            Severity::Note => self.colors.cyan(),
        }
    }
}

fn count_digits(n: u32) -> u32 {
    if n == 0 { return 1; }
    let mut count = 0;
    let mut num = n;
    while num > 0 {
        count += 1;
        num /= 10;
    }
    count
}

/// Render diagnostics to stderr with auto-detected color
pub fn render_diagnostics(diagnostics: &[Diagnostic]) {
    use std::io::IsTerminal;
    let stderr = std::io::stderr();
    let use_color = stderr.is_terminal();
    let mut renderer = ConsoleRenderer::new(stderr.lock(), use_color);
    for diag in diagnostics {
        let _ = renderer.render(diag);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::codes::SEMA_TYPE_MISMATCH;
    use crate::frontend::Span;

    #[test]
    fn render_basic_diagnostic() {
        let diag = Diagnostic {
            info: &SEMA_TYPE_MISMATCH,
            span: Span::new(0, 10, 1, 5),
            file: "test.vole".to_string(),
            formatted_message: "expected i64, found bool".to_string(),
            source_line: Some("let x = true".to_string()),
            related: vec![],
        };

        let mut output = Vec::new();
        let mut renderer = ConsoleRenderer::new(&mut output, false);
        renderer.render(&diag).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(output_str.contains("error[E2001]"));
        assert!(output_str.contains("expected i64, found bool"));
        assert!(output_str.contains("test.vole:1:5"));
        assert!(output_str.contains("let x = true"));
        assert!(output_str.contains("^"));
    }

    #[test]
    fn render_multi_char_caret() {
        // Create a span from column 5 to column 10 (5 characters)
        let span = Span::new_with_end(4, 9, 1, 5, 1, 10);
        let diag = Diagnostic {
            info: &SEMA_TYPE_MISMATCH,
            span,
            file: "test.vole".to_string(),
            formatted_message: "multi-char span test".to_string(),
            source_line: Some("let hello = 42".to_string()),
            related: vec![],
        };

        let mut output = Vec::new();
        let mut renderer = ConsoleRenderer::new(&mut output, false);
        renderer.render(&diag).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        // 5 carets for the span from column 5 to 10
        assert!(output_str.contains("^^^^^"), "Expected 5 carets, got: {}", output_str);
    }

    #[test]
    fn render_single_char_caret_for_multiline_span() {
        // Create a multi-line span (should render single caret)
        let span = Span::new_with_end(0, 20, 1, 5, 2, 8);
        let diag = Diagnostic {
            info: &SEMA_TYPE_MISMATCH,
            span,
            file: "test.vole".to_string(),
            formatted_message: "multiline span".to_string(),
            source_line: Some("let x = 42".to_string()),
            related: vec![],
        };

        let mut output = Vec::new();
        let mut renderer = ConsoleRenderer::new(&mut output, false);
        renderer.render(&diag).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        // Should have single caret for multi-line span
        // Check that we have exactly one caret (not followed by another)
        assert!(output_str.contains("^\n") || output_str.contains("^ "),
                "Expected single caret for multiline span, got: {}", output_str);
    }

    #[test]
    fn count_digits_works() {
        assert_eq!(count_digits(0), 1);
        assert_eq!(count_digits(5), 1);
        assert_eq!(count_digits(42), 2);
        assert_eq!(count_digits(100), 3);
        assert_eq!(count_digits(9999), 4);
    }
}
