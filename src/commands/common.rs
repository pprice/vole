// src/commands/common.rs
//! Shared utilities for CLI commands.

use std::io::IsTerminal;

use crate::errors::render_diagnostics;
use crate::frontend::{ast::Program, Interner, Parser};
use crate::sema::Analyzer;

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Interner,
}

/// Parse and analyze a source file, rendering any diagnostics on error.
///
/// Returns `Ok(AnalyzedProgram)` on success, or `Err(())` if there were
/// errors (diagnostics are rendered to stderr before returning).
pub fn parse_and_analyze(source: &str, file_path: &str) -> Result<AnalyzedProgram, ()> {
    // Parse
    let mut parser = Parser::with_file(source, file_path);
    let program = match parser.parse_program() {
        Ok(prog) => prog,
        Err(e) => {
            // Render any lexer errors first
            let lexer_errors = parser.take_lexer_errors();
            if !lexer_errors.is_empty() {
                render_diagnostics(&lexer_errors);
                // If we have lexer errors, the parse error is likely a consequence
                // of trying to parse an error token - don't show duplicate
            } else {
                // Render the parse error only if no lexer errors
                render_diagnostics(&[e.diagnostic]);
            }
            return Err(());
        }
    };

    // Check for lexer errors that didn't cause parse failure
    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        render_diagnostics(&lexer_errors);
        return Err(());
    }

    let interner = parser.into_interner();

    // Type check
    let mut analyzer = Analyzer::new(file_path, source);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        let diagnostics: Vec<_> = errors.iter().map(|e| e.diagnostic.clone()).collect();
        render_diagnostics(&diagnostics);
        return Err(());
    }

    Ok(AnalyzedProgram { program, interner })
}

/// Check if stdout supports color output.
pub fn stdout_supports_color() -> bool {
    std::io::stdout().is_terminal()
}

/// ANSI color codes for terminal output.
pub struct TermColors {
    use_color: bool,
}

impl TermColors {
    /// Create a new TermColors that auto-detects stdout terminal support.
    pub fn auto() -> Self {
        Self {
            use_color: stdout_supports_color(),
        }
    }

    /// Green text (for success).
    pub fn green(&self) -> &'static str {
        if self.use_color { "\x1b[32m" } else { "" }
    }

    /// Red text (for errors/failures).
    pub fn red(&self) -> &'static str {
        if self.use_color { "\x1b[31m" } else { "" }
    }

    /// Dim/gray text (for secondary info like timing).
    pub fn dim(&self) -> &'static str {
        if self.use_color { "\x1b[90m" } else { "" }
    }

    /// Reset to default colors.
    pub fn reset(&self) -> &'static str {
        if self.use_color { "\x1b[0m" } else { "" }
    }
}
