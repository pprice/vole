// src/commands/common.rs
//! Shared utilities for CLI commands.

use std::io::{self, IsTerminal, Read, Write};

use miette::NamedSource;

use std::collections::HashMap;

use crate::cli::ColorMode;
use crate::codegen::{Compiler, JitContext};
use crate::errors::{LexerError, render_to_stderr, render_to_writer};
use crate::frontend::{AstPrinter, Interner, NodeId, ParseError, Parser, Symbol, ast::Program};
use crate::runtime::set_stdout_capture;
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::{Analyzer, MethodResolutions, Type, TypeError};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Interner,
    pub type_aliases: HashMap<Symbol, Type>,
    pub expr_types: HashMap<NodeId, Type>,
    pub method_resolutions: MethodResolutions,
    pub interface_registry: InterfaceRegistry,
}

/// Render a lexer error to stderr with source context
fn render_lexer_error(err: &LexerError, file_path: &str, source: &str) {
    let report = miette::Report::new(err.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    render_to_stderr(report.as_ref());
}

/// Render a parser error to stderr with source context
fn render_parser_error(err: &ParseError, file_path: &str, source: &str) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    render_to_stderr(report.as_ref());
}

/// Render a lexer error to a writer (for snapshots)
fn render_lexer_error_to<W: Write>(
    err: &LexerError,
    file_path: &str,
    source: &str,
    writer: &mut W,
) {
    let report = miette::Report::new(err.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), writer);
}

/// Render a parser error to a writer (for snapshots)
fn render_parser_error_to<W: Write>(
    err: &ParseError,
    file_path: &str,
    source: &str,
    writer: &mut W,
) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), writer);
}

/// Render a semantic error to stderr with source context
fn render_sema_error(err: &TypeError, file_path: &str, source: &str) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    render_to_stderr(report.as_ref());
}

/// Render a semantic error to a writer (for snapshots)
fn render_sema_error_to<W: Write>(err: &TypeError, file_path: &str, source: &str, writer: &mut W) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), writer);
}

/// Parse and analyze a source file, rendering any diagnostics on error.
///
/// Returns `Ok(AnalyzedProgram)` on success, or `Err(())` if there were
/// errors (diagnostics are rendered to stderr before returning).
#[allow(clippy::result_unit_err)] // Error details are rendered internally
pub fn parse_and_analyze(source: &str, file_path: &str) -> Result<AnalyzedProgram, ()> {
    // Parse
    let mut parser = Parser::with_file(source, file_path);
    let program = match parser.parse_program() {
        Ok(prog) => prog,
        Err(e) => {
            // Render any lexer errors first
            let lexer_errors = parser.take_lexer_errors();
            if !lexer_errors.is_empty() {
                for err in &lexer_errors {
                    render_lexer_error(err, file_path, source);
                }
            } else {
                render_parser_error(&e, file_path, source);
            }
            return Err(());
        }
    };

    // Check for lexer errors that didn't cause parse failure
    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        for err in &lexer_errors {
            render_lexer_error(err, file_path, source);
        }
        return Err(());
    }

    let interner = parser.into_interner();

    // Type check
    let mut analyzer = Analyzer::new(file_path, source);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        for err in &errors {
            render_sema_error(err, file_path, source);
        }
        return Err(());
    }

    let (type_aliases, expr_types, method_resolutions, interface_registry) =
        analyzer.into_analysis_results();
    Ok(AnalyzedProgram {
        program,
        interner,
        type_aliases,
        expr_types,
        method_resolutions,
        interface_registry,
    })
}

/// Check if stdout supports color output.
pub fn stdout_supports_color() -> bool {
    // Respect NO_COLOR environment variable (https://no-color.org/)
    if std::env::var_os("NO_COLOR").is_some() {
        return false;
    }
    io::stdout().is_terminal()
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

    /// Create a new TermColors with explicit color mode.
    pub fn with_mode(mode: ColorMode) -> Self {
        let use_color = match mode {
            ColorMode::Auto => stdout_supports_color(),
            ColorMode::Always => true,
            ColorMode::Never => false,
        };
        Self { use_color }
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

/// Read source code from stdin
pub fn read_stdin() -> io::Result<String> {
    let mut source = String::new();
    io::stdin().read_to_string(&mut source)?;
    Ok(source)
}

/// Check a program with captured stderr output
#[allow(clippy::result_unit_err)] // Error details are rendered internally
pub fn check_captured<W: Write + Send + 'static>(
    source: &str,
    file_path: &str,
    mut stderr: W,
) -> Result<(), ()> {
    // Parse
    let mut parser = Parser::with_file(source, file_path);
    let program = match parser.parse_program() {
        Ok(prog) => prog,
        Err(e) => {
            let lexer_errors = parser.take_lexer_errors();
            if !lexer_errors.is_empty() {
                for err in &lexer_errors {
                    render_lexer_error_to(err, file_path, source, &mut stderr);
                }
            } else {
                render_parser_error_to(&e, file_path, source, &mut stderr);
            }
            return Err(());
        }
    };

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        for err in &lexer_errors {
            render_lexer_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    let interner = parser.into_interner();

    // Type check
    let mut analyzer = Analyzer::new(file_path, source);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        for err in &errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    Ok(())
}

/// Run a program with captured stdout and stderr
#[allow(clippy::result_unit_err)] // Error details are rendered internally
pub fn run_captured<W: Write + Send + 'static>(
    source: &str,
    file_path: &str,
    stdout: W,
    mut stderr: W,
) -> Result<(), ()> {
    // Parse and analyze
    let mut parser = Parser::with_file(source, file_path);
    let program = match parser.parse_program() {
        Ok(prog) => prog,
        Err(e) => {
            let lexer_errors = parser.take_lexer_errors();
            if !lexer_errors.is_empty() {
                for err in &lexer_errors {
                    render_lexer_error_to(err, file_path, source, &mut stderr);
                }
            } else {
                render_parser_error_to(&e, file_path, source, &mut stderr);
            }
            return Err(());
        }
    };

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        for err in &lexer_errors {
            render_lexer_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    let interner = parser.into_interner();

    // Type check
    let mut analyzer = Analyzer::new(file_path, source);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        for err in &errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }
    let (type_aliases, expr_types, method_resolutions, interface_registry) =
        analyzer.into_analysis_results();

    // Compile
    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(
            &mut jit,
            &interner,
            type_aliases,
            expr_types,
            method_resolutions,
            interface_registry,
        );
        if let Err(e) = compiler.compile_program(&program) {
            let _ = writeln!(stderr, "compilation error: {}", e);
            return Err(());
        }
    }
    jit.finalize();

    // Execute with captured stdout
    let fn_ptr = match jit.get_function_ptr("main") {
        Some(ptr) => ptr,
        None => {
            let _ = writeln!(stderr, "error: no 'main' function found");
            return Err(());
        }
    };

    // Set up stdout capture
    set_stdout_capture(Some(Box::new(stdout)));

    let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };
    main();

    // Restore normal stdout
    set_stdout_capture(None);

    Ok(())
}

/// Inspect AST with captured stdout and stderr
#[allow(clippy::result_unit_err)]
pub fn inspect_ast_captured<W: Write>(
    source: &str,
    file_path: &str,
    mut stdout: W,
    mut stderr: W,
) -> Result<(), ()> {
    // Parse
    let mut parser = Parser::with_file(source, file_path);
    let program = match parser.parse_program() {
        Ok(prog) => prog,
        Err(e) => {
            let lexer_errors = parser.take_lexer_errors();
            if !lexer_errors.is_empty() {
                for err in &lexer_errors {
                    render_lexer_error_to(err, file_path, source, &mut stderr);
                }
            } else {
                render_parser_error_to(&e, file_path, source, &mut stderr);
            }
            return Err(());
        }
    };

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        for err in &lexer_errors {
            render_lexer_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    let interner = parser.into_interner();

    // Print file header to stderr
    let _ = writeln!(stderr, "// {}", file_path);

    // Print AST to stdout
    let printer = AstPrinter::new(&interner, false);
    let _ = write!(stdout, "{}", printer.print_program(&program));

    Ok(())
}
