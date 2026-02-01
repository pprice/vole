// src/commands/common.rs
//! Shared utilities for CLI commands.

use std::io::{self, IsTerminal, Read, Write};

use miette::NamedSource;

use std::cell::RefCell;
use std::rc::Rc;

use crate::cli::ColorMode;
use crate::codegen::{Compiler, JitContext};
use crate::errors::{LexerError, render_to_stderr, render_to_writer};
use crate::frontend::{AstPrinter, ParseError, Parser};
use crate::runtime::{
    JmpBuf, call_setjmp, clear_test_jmp_buf, set_capture_mode, set_stderr_capture,
    set_stdout_capture, set_test_jmp_buf,
};
use crate::sema::{Analyzer, ModuleCache, TypeError, TypeWarning, optimize_all};
use crate::transforms;

// Re-export AnalyzedProgram from codegen
pub use crate::codegen::AnalyzedProgram;

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

/// Render a semantic warning to stderr
fn render_sema_warning(warn: &TypeWarning, file_path: &str, source: &str) {
    let report = miette::Report::new(warn.warning.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    render_to_stderr(report.as_ref());
}

/// Render a semantic warning to a writer (for snapshots)
fn render_sema_warning_to<W: Write>(
    warn: &TypeWarning,
    file_path: &str,
    source: &str,
    writer: &mut W,
) {
    let report = miette::Report::new(warn.warning.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), writer);
}

/// Parse and analyze a source file, rendering any diagnostics on error.
///
/// Returns `Ok(AnalyzedProgram)` on success, or `Err(())` if there were
/// errors (diagnostics are rendered to stderr before returning).
#[allow(clippy::result_unit_err)] // Error details are rendered internally
pub fn parse_and_analyze(
    source: &str,
    file_path: &str,
    project_root: Option<&std::path::Path>,
) -> Result<AnalyzedProgram, ()> {
    parse_and_analyze_opts(source, file_path, project_root, false)
}

/// Parse and analyze a source file, skipping tests blocks.
///
/// Used by `vole run` to avoid sema cost for tests blocks in production.
#[allow(clippy::result_unit_err)]
pub fn parse_and_analyze_skip_tests(
    source: &str,
    file_path: &str,
    project_root: Option<&std::path::Path>,
) -> Result<AnalyzedProgram, ()> {
    parse_and_analyze_opts(source, file_path, project_root, true)
}

/// Parse and analyze a source file, optionally skipping tests blocks.
///
/// When `skip_tests` is true, `Decl::Tests` is ignored in all sema passes.
/// This is used by `vole run` to avoid sema cost for tests blocks in production.
#[allow(clippy::result_unit_err)]
fn parse_and_analyze_opts(
    source: &str,
    file_path: &str,
    project_root: Option<&std::path::Path>,
    skip_tests: bool,
) -> Result<AnalyzedProgram, ()> {
    // Parse phase
    let (mut program, mut interner) = {
        let _span = tracing::info_span!("parse", file = %file_path).entered();
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

        let mut interner = parser.into_interner();
        interner.seed_builtin_symbols();
        tracing::debug!(declarations = program.declarations.len(), "parsed");
        (program, interner)
    };

    // Transform phase (generators to state machines)
    {
        let _span = tracing::info_span!("transform").entered();
        let (_, transform_errors) = transforms::transform_generators(&mut program, &mut interner);
        if !transform_errors.is_empty() {
            for err in &transform_errors {
                render_sema_error(err, file_path, source);
            }
            return Err(());
        }
    }

    // Sema phase (type checking)
    let mut analyzer = {
        let _span = tracing::info_span!("sema").entered();
        let mut analyzer = Analyzer::with_project_root(file_path, source, project_root);
        analyzer.set_skip_tests(skip_tests);
        if let Err(errors) = analyzer.analyze(&program, &interner) {
            for err in &errors {
                render_sema_error(err, file_path, source);
            }
            return Err(());
        }
        tracing::debug!("type checking complete");
        analyzer
    };

    // Render any warnings (non-fatal diagnostics)
    for warn in &analyzer.take_warnings() {
        render_sema_warning(warn, file_path, source);
    }

    let mut output = analyzer.into_analysis_results();

    // Optimizer phase (constant folding, algebraic simplifications)
    {
        let _span = tracing::info_span!("optimize").entered();
        let stats = optimize_all(&mut program, &interner, &mut output.expression_data);
        tracing::debug!(
            constants_folded = stats.constants_folded,
            div_to_mul = stats.div_to_mul,
            div_to_shift = stats.div_to_shift,
            "optimization complete"
        );
    }

    Ok(AnalyzedProgram::from_analysis(program, interner, output))
}

/// Parse and analyze a source file with a shared module cache.
/// The cache is used to avoid re-analyzing modules that have already been analyzed.
#[allow(clippy::result_unit_err)]
pub fn parse_and_analyze_with_cache(
    source: &str,
    file_path: &str,
    cache: Rc<RefCell<ModuleCache>>,
    project_root: Option<&std::path::Path>,
) -> Result<AnalyzedProgram, ()> {
    // Parse phase
    let (mut program, mut interner) = {
        let _span = tracing::info_span!("parse", file = %file_path).entered();
        let mut parser = Parser::with_file(source, file_path);
        let program = match parser.parse_program() {
            Ok(prog) => prog,
            Err(e) => {
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

        let lexer_errors = parser.take_lexer_errors();
        if !lexer_errors.is_empty() {
            for err in &lexer_errors {
                render_lexer_error(err, file_path, source);
            }
            return Err(());
        }

        let mut interner = parser.into_interner();
        interner.seed_builtin_symbols();
        tracing::debug!(declarations = program.declarations.len(), "parsed");
        (program, interner)
    };

    // Transform phase
    {
        let _span = tracing::info_span!("transform").entered();
        let (_, transform_errors) = transforms::transform_generators(&mut program, &mut interner);
        if !transform_errors.is_empty() {
            for err in &transform_errors {
                render_sema_error(err, file_path, source);
            }
            return Err(());
        }
    }

    // Sema phase with cache
    let mut analyzer = {
        let _span = tracing::info_span!("sema").entered();
        let mut analyzer =
            Analyzer::with_cache_and_project_root(file_path, source, cache, project_root);
        if let Err(errors) = analyzer.analyze(&program, &interner) {
            for err in &errors {
                render_sema_error(err, file_path, source);
            }
            return Err(());
        }
        tracing::debug!("type checking complete");
        analyzer
    };

    for warn in &analyzer.take_warnings() {
        render_sema_warning(warn, file_path, source);
    }

    let mut output = analyzer.into_analysis_results();

    // Optimizer phase (constant folding, algebraic simplifications)
    {
        let _span = tracing::info_span!("optimize").entered();
        let stats = optimize_all(&mut program, &interner, &mut output.expression_data);
        tracing::debug!(
            constants_folded = stats.constants_folded,
            div_to_mul = stats.div_to_mul,
            div_to_shift = stats.div_to_shift,
            "optimization complete"
        );
    }

    Ok(AnalyzedProgram::from_analysis(program, interner, output))
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
    let mut program = match parser.parse_program() {
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

    let mut interner = parser.into_interner();
    interner.seed_builtin_symbols();

    // Transform generators to state machines (before type checking)
    let (_, transform_errors) = transforms::transform_generators(&mut program, &mut interner);
    if !transform_errors.is_empty() {
        for err in &transform_errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    // Type check
    let mut analyzer = Analyzer::new(file_path, source);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        for err in &errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    // Render warnings (non-fatal diagnostics)
    for warn in &analyzer.take_warnings() {
        render_sema_warning_to(warn, file_path, source, &mut stderr);
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
    let mut program = match parser.parse_program() {
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

    let mut interner = parser.into_interner();
    interner.seed_builtin_symbols();

    // Transform generators to state machines (before type checking)
    let (_, transform_errors) = transforms::transform_generators(&mut program, &mut interner);
    if !transform_errors.is_empty() {
        for err in &transform_errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }

    // Type check (skip tests blocks, matching `vole run` behavior)
    let mut analyzer = Analyzer::new(file_path, source);
    analyzer.set_skip_tests(true);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        for err in &errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }
    let mut output = analyzer.into_analysis_results();

    // Optimizer phase (constant folding, algebraic simplifications)
    let _stats = optimize_all(&mut program, &interner, &mut output.expression_data);

    let analyzed = AnalyzedProgram::from_analysis(program, interner, output);

    // Compile (skip tests blocks, matching `vole run` behavior)
    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler.set_source_file(file_path);
        compiler.set_skip_tests(true);
        if let Err(e) = compiler.compile_program(&analyzed.program) {
            let _ = writeln!(stderr, "compilation error: {}", e);
            return Err(());
        }
    }
    if let Err(e) = jit.finalize() {
        let _ = writeln!(stderr, "finalization error: {}", e);
        return Err(());
    }

    // Execute with captured stdout
    let fn_ptr = match jit.get_function_ptr("main") {
        Some(ptr) => ptr,
        None => {
            let _ = writeln!(stderr, "error: no 'main' function found");
            return Err(());
        }
    };

    // Set up stdout and stderr capture, and enable capture mode for panic
    set_stdout_capture(Some(Box::new(stdout)));
    set_stderr_capture(Some(Box::new(stderr)));
    set_capture_mode(true);

    // Set up jmp_buf for panic recovery
    let mut jmp_buf = JmpBuf::zeroed();
    set_test_jmp_buf(&mut jmp_buf);

    let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };

    unsafe {
        if call_setjmp(&mut jmp_buf) == 0 {
            // Normal execution path
            main();
        }
        // If longjmp occurred (from panic), we just continue
    }

    // Restore normal stdout and stderr, disable capture mode
    clear_test_jmp_buf();
    set_stdout_capture(None);
    set_stderr_capture(None);
    set_capture_mode(false);

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
