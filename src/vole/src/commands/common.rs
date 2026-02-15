// src/commands/common.rs
//! Shared utilities for CLI commands.

use std::io::{self, IsTerminal, Read, Write};

use miette::NamedSource;

use std::cell::RefCell;
use std::rc::Rc;

use crate::cli::ColorMode;
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::errors::{
    CodegenError, LexerError, ParserError, WithExtraHelp, render_to_writer_terminal,
};
use crate::frontend::{AstPrinter, ParseError, Parser};
use crate::runtime::{
    JmpBuf, call_setjmp, clear_test_jmp_buf, recover_from_signal, set_capture_mode,
    set_stderr_capture, set_stdout_capture, set_test_jmp_buf, take_stack_overflow,
    write_to_stderr_capture,
};
use crate::sema::{ModuleCache, TypeError, TypeWarning, optimize_all};
use crate::transforms;

// Re-export AnalyzedProgram from codegen
pub use crate::codegen::AnalyzedProgram;

/// Errors that can occur during the compilation pipeline.
///
/// The actual error details are rendered to the `errors` writer at the point
/// of failure. This enum exists to provide typed error handling instead of
/// unit errors, improving readability and allowing callers to know which
/// phase failed if needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PipelineError {
    /// Lexer encountered invalid tokens
    Lex,
    /// Parser encountered syntax errors
    Parse,
    /// Generator transformation failed
    Transform,
    /// Type checking failed
    Sema,
    /// Code generation failed
    Codegen,
    /// Program finalization failed
    Finalize,
    /// No main function found
    NoMain,
    /// I/O error (file not found, permission denied, etc.)
    Io,
}

/// Render a lexer error to a writer with source context.
fn render_lexer_error(
    err: &LexerError,
    file_path: &str,
    source: &str,
    w: &mut dyn Write,
    color_mode: ColorMode,
) {
    let report = miette::Report::new(err.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer_terminal(report.as_ref(), w, color_mode);
}

/// Render a parser error to a writer with source context.
/// If `run_mode` is true and the error is StatementAtTopLevel, adds a hint
/// about wrapping code in `func main() { ... }`.
fn render_parser_error(
    err: &ParseError,
    file_path: &str,
    source: &str,
    run_mode: bool,
    w: &mut dyn Write,
    color_mode: ColorMode,
) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));

    // Add extra hint for StatementAtTopLevel errors in run mode
    if run_mode && matches!(err.error, ParserError::StatementAtTopLevel { .. }) {
        let wrapped = WithExtraHelp::new(
            report.as_ref(),
            "wrap your code in `func main() { ... }` to make it runnable",
        );
        let _ = render_to_writer_terminal(&wrapped, w, color_mode);
    } else {
        let _ = render_to_writer_terminal(report.as_ref(), w, color_mode);
    }
}

/// Render a semantic error to a writer with source context.
fn render_sema_error(
    err: &TypeError,
    file_path: &str,
    source: &str,
    w: &mut dyn Write,
    color_mode: ColorMode,
) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer_terminal(report.as_ref(), w, color_mode);
}

/// Render a semantic warning to a writer with source context.
fn render_sema_warning(
    warn: &TypeWarning,
    file_path: &str,
    source: &str,
    w: &mut dyn Write,
    color_mode: ColorMode,
) {
    let report = miette::Report::new(warn.warning.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer_terminal(report.as_ref(), w, color_mode);
}

/// Render a codegen error to a writer with source context.
///
/// If the error has a span, renders a full miette diagnostic with labeled source.
/// Otherwise, falls back to a plain "compilation error: ..." message since some
/// codegen errors (e.g., cranelift internal, IO) genuinely have no source location.
fn render_codegen_error(
    err: &CodegenError,
    file_path: &str,
    source: &str,
    w: &mut dyn Write,
    color_mode: ColorMode,
) {
    if err.span.is_some() {
        let report = miette::Report::new(err.clone())
            .with_source_code(NamedSource::new(file_path, source.to_string()));
        let _ = render_to_writer_terminal(report.as_ref(), w, color_mode);
    } else {
        let _ = writeln!(w, "compilation error: {}", err);
    }
}

/// Options for the compile_source pipeline.
pub struct PipelineOptions<'a> {
    pub source: &'a str,
    pub file_path: &'a str,
    pub skip_tests: bool,
    pub project_root: Option<&'a std::path::Path>,
    pub module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// When true, adds context-specific hints for `vole run` (e.g., "wrap in func main").
    pub run_mode: bool,
    /// Color mode for diagnostic rendering.
    pub color_mode: ColorMode,
}

/// Compile source through the full pipeline: parse -> transform -> analyze -> optimize.
///
/// All diagnostics (errors and warnings) are rendered to the provided `errors` writer.
/// Returns `Ok(AnalyzedProgram)` on success, or `Err(PipelineError)` indicating which
/// phase failed.
pub fn compile_source(
    opts: PipelineOptions,
    errors: &mut dyn Write,
) -> Result<AnalyzedProgram, PipelineError> {
    let PipelineOptions {
        source,
        file_path,
        skip_tests,
        project_root,
        module_cache,
        run_mode,
        color_mode,
    } = opts;

    // Parse phase
    let (mut program, mut interner) = {
        let _span = tracing::info_span!("parse", file = %file_path).entered();
        let mut parser = Parser::new(source);
        parser.set_skip_tests(skip_tests);
        let program = match parser.parse_program() {
            Ok(prog) => prog,
            Err(e) => {
                let lexer_errors = parser.take_lexer_errors();
                if !lexer_errors.is_empty() {
                    for err in &lexer_errors {
                        render_lexer_error(err, file_path, source, errors, color_mode);
                    }
                    return Err(PipelineError::Lex);
                } else {
                    render_parser_error(&e, file_path, source, run_mode, errors, color_mode);
                    return Err(PipelineError::Parse);
                }
            }
        };

        // Check for lexer errors that didn't cause parse failure
        let lexer_errors = parser.take_lexer_errors();
        if !lexer_errors.is_empty() {
            for err in &lexer_errors {
                render_lexer_error(err, file_path, source, errors, color_mode);
            }
            return Err(PipelineError::Lex);
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
                render_sema_error(err, file_path, source, errors, color_mode);
            }
            return Err(PipelineError::Transform);
        }
    }

    // Sema phase (type checking)
    let mut analyzer = {
        let _span = tracing::info_span!("sema").entered();
        let mut builder =
            crate::sema::AnalyzerBuilder::new(file_path).with_project_root(project_root);
        if let Some(cache) = module_cache {
            builder = builder.with_cache(cache);
        }
        let mut analyzer = builder.build();
        analyzer.set_skip_tests(skip_tests);
        if let Err(errs) = analyzer.analyze(&program, &interner) {
            for err in &errs {
                render_sema_error(err, file_path, source, errors, color_mode);
            }
            return Err(PipelineError::Sema);
        }
        tracing::debug!("type checking complete");
        analyzer
    };

    // Render any warnings (non-fatal diagnostics)
    for warn in &analyzer.take_warnings() {
        render_sema_warning(warn, file_path, source, errors, color_mode);
    }

    let mut output = analyzer.into_analysis_results();

    // Optimizer phase (constant folding, algebraic simplifications)
    {
        let _span = tracing::info_span!("optimize").entered();
        let stats = optimize_all(&mut program, &mut output.expression_data);
        tracing::debug!(
            constants_folded = stats.constants_folded,
            div_to_mul = stats.div_to_mul,
            div_to_shift = stats.div_to_shift,
            "optimization complete"
        );
    }

    Ok(AnalyzedProgram::from_analysis(program, interner, output))
}

/// Options for the compile_and_run codegen+execution pipeline.
pub struct RunOptions<'a> {
    pub file_path: &'a str,
    pub source: &'a str,
    pub jit_options: JitOptions,
    pub skip_tests: bool,
    pub color_mode: ColorMode,
}

/// Compile an analyzed program to machine code and execute it.
///
/// Handles: JIT compilation, finalization, main lookup, and execution
/// with jmp_buf panic recovery. Compilation errors are written to `errors`.
///
/// The caller is responsible for setting up stdout/stderr capture (via
/// `set_stdout_capture`/`set_stderr_capture`) before calling if needed.
pub fn compile_and_run(
    analyzed: &AnalyzedProgram,
    opts: &RunOptions,
    errors: &mut dyn Write,
) -> Result<(), PipelineError> {
    // Codegen phase
    let jit = {
        let _span = tracing::info_span!("codegen").entered();
        let mut jit = JitContext::with_options(opts.jit_options);
        {
            let mut compiler = Compiler::new(&mut jit, analyzed);
            compiler.set_source_file(opts.file_path);
            compiler.set_skip_tests(opts.skip_tests);
            if let Err(e) = compiler.compile_program(&analyzed.program) {
                render_codegen_error(&e, opts.file_path, opts.source, errors, opts.color_mode);
                return Err(PipelineError::Codegen);
            }
        }
        if let Err(e) = jit.finalize() {
            render_codegen_error(&e, opts.file_path, opts.source, errors, opts.color_mode);
            return Err(PipelineError::Finalize);
        }
        tracing::debug!("compilation complete");
        jit
    };

    // Execute phase
    let fn_ptr = match jit.get_function_ptr("main") {
        Some(ptr) => ptr,
        None => {
            let _ = writeln!(
                errors,
                "error: no 'main' function found in {}",
                opts.file_path
            );
            if let Some(hint) = suggest_main_function(&jit) {
                let _ = writeln!(errors, "hint: {}", hint);
            }
            return Err(PipelineError::NoMain);
        }
    };

    let _span = tracing::info_span!("execute").entered();
    let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };

    // Use jmp_buf for panic recovery — safely handles runtime panics
    // instead of crashing the host process.
    let mut jmp_buf = JmpBuf::zeroed();
    set_test_jmp_buf(&mut jmp_buf);

    unsafe {
        let setjmp_val = call_setjmp(&mut jmp_buf);
        if setjmp_val == 0 {
            main();
        } else {
            // Returned via longjmp — reset global state that may have
            // been left locked by the interrupted execution.
            recover_from_signal();
            if take_stack_overflow() {
                // Stack overflow detected by signal handler
                eprintln!("error: stack overflow (infinite recursion)");
            }
            // If longjmp occurred (from panic), we just continue
        }
    }

    clear_test_jmp_buf();

    Ok(())
}

/// Suggest a similar function name when 'main' is not found.
///
/// Checks for common mistakes:
/// - Case variants: Main, MAIN
/// - Common alternatives: run, Run, start, Start
/// - Typos: main_
fn suggest_main_function(jit: &JitContext) -> Option<String> {
    // Case variants of "main" - most likely mistake
    let case_variants = ["Main", "MAIN", "mAIN", "maiN"];

    // Common alternative entry point names from other languages
    let common_alternatives = ["run", "Run", "RUN", "start", "Start", "START"];

    // Common typos
    let typos = ["main_", "_main", "mainn", "mian", "mains"];

    for &name in &case_variants {
        if jit.has_function(name) {
            return Some(format!(
                "did you mean '{}'? The entry point must be lowercase 'main'.",
                name
            ));
        }
    }

    for &name in &common_alternatives {
        if jit.has_function(name) {
            return Some(format!(
                "found '{}', but Vole uses 'main' as the entry point.",
                name
            ));
        }
    }

    for &name in &typos {
        if jit.has_function(name) {
            return Some(format!(
                "did you mean 'main'? Found similar function '{}'.",
                name
            ));
        }
    }

    None
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

    /// Yellow text (for warnings/file errors).
    pub fn yellow(&self) -> &'static str {
        if self.use_color { "\x1b[33m" } else { "" }
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

/// Check a program with captured stderr output.
///
/// Error details are rendered to `stderr`; the returned `PipelineError` indicates
/// which phase failed.
pub fn check_captured<W: Write + Send + 'static>(
    source: &str,
    file_path: &str,
    mut stderr: W,
    color_mode: ColorMode,
) -> Result<(), PipelineError> {
    compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: false,
            project_root: None,
            module_cache: None,
            run_mode: false,
            color_mode,
        },
        &mut stderr,
    )?;
    Ok(())
}

/// Run a program with captured stdout and stderr.
///
/// Error details are rendered to `stderr`; the returned `PipelineError` indicates
/// which phase failed.
pub fn run_captured<W: Write + Send + 'static>(
    source: &str,
    file_path: &str,
    stdout: W,
    mut stderr: W,
    color_mode: ColorMode,
) -> Result<(), PipelineError> {
    let analyzed = compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: true,
            project_root: None,
            module_cache: None,
            run_mode: true,
            color_mode,
        },
        &mut stderr,
    )?;

    let run_opts = RunOptions {
        file_path,
        source,
        jit_options: JitOptions::default(),
        skip_tests: true,
        color_mode,
    };

    // Set up stdout/stderr capture for the JIT program's print() calls
    set_stdout_capture(Some(Box::new(stdout)));
    set_stderr_capture(Some(Box::new(stderr)));
    set_capture_mode(true);

    // Codegen errors go to a buffer (capture has taken ownership of stderr)
    let mut error_buf = Vec::new();
    let result = compile_and_run(&analyzed, &run_opts, &mut error_buf);

    // Route any codegen errors to the captured stderr before tearing down
    if !error_buf.is_empty() {
        write_to_stderr_capture(&error_buf);
    }

    // Restore normal stdout and stderr, disable capture mode
    set_stdout_capture(None);
    set_stderr_capture(None);
    set_capture_mode(false);

    result
}

/// Inspect AST with captured stdout and stderr.
///
/// Error details are rendered to `stderr`; the returned `PipelineError` indicates
/// which phase failed.
pub fn inspect_ast_captured<W: Write>(
    source: &str,
    file_path: &str,
    mut stdout: W,
    mut stderr: W,
    color_mode: ColorMode,
) -> Result<(), PipelineError> {
    // Parse
    let mut parser = Parser::new(source);
    let program = match parser.parse_program() {
        Ok(prog) => prog,
        Err(e) => {
            let lexer_errors = parser.take_lexer_errors();
            if !lexer_errors.is_empty() {
                for err in &lexer_errors {
                    render_lexer_error(err, file_path, source, &mut stderr, color_mode);
                }
                return Err(PipelineError::Lex);
            } else {
                render_parser_error(&e, file_path, source, false, &mut stderr, color_mode);
                return Err(PipelineError::Parse);
            }
        }
    };

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        for err in &lexer_errors {
            render_lexer_error(err, file_path, source, &mut stderr, color_mode);
        }
        return Err(PipelineError::Lex);
    }

    let interner = parser.into_interner();

    // Print file header to stderr
    let _ = writeln!(stderr, "// {}", file_path);

    // Print AST to stdout
    let printer = AstPrinter::new(&interner, false);
    let _ = write!(stdout, "{}", printer.print_program(&program));

    Ok(())
}

/// Unicode box-drawing characters (matching miette's style).
pub mod box_chars {
    pub const TOP_LEFT: char = '╭';
    pub const TOP_RIGHT: char = '╮';
    pub const BOTTOM_LEFT: char = '╰';
    pub const BOTTOM_RIGHT: char = '╯';
    pub const HORIZONTAL: char = '─';
    pub const VERTICAL: char = '│';
}

/// Calculate the visible width of a string, ignoring ANSI escape codes.
pub fn visible_width(s: &str) -> usize {
    let mut width = 0;
    let mut in_escape = false;
    for c in s.chars() {
        if c == '\x1b' {
            in_escape = true;
        } else if in_escape {
            if c == 'm' {
                in_escape = false;
            }
        } else {
            width += 1;
        }
    }
    width
}

/// Options for styling a labeled box.
#[derive(Default)]
pub struct BoxStyle<'a> {
    /// Color/style for the border (e.g., dim)
    pub border: &'a str,
    /// Color/style for the label
    pub label: &'a str,
    /// Reset sequence
    pub reset: &'a str,
}

/// Print a labeled box around content lines.
///
/// ```text
/// ╭─ Label ──────────╮
/// │ content line 1   │
/// │ content line 2   │
/// ╰──────────────────╯
/// ```
pub fn print_labeled_box(label: &str, lines: &[&str], indent: usize, style: BoxStyle) {
    use box_chars::*;

    // Calculate the maximum visible width of content
    let max_content_width = lines.iter().map(|l| visible_width(l)).max().unwrap_or(0);

    // Inner width is the wider of: content or label, no extra padding
    let inner_width = max_content_width.max(label.len());

    let indent_str = " ".repeat(indent);
    let h = |n: usize| HORIZONTAL.to_string().repeat(n);

    // Top: ╭─ Label ─────╮
    // Structure: ╭ + ─ + space + label + space + bars + ╮
    // Bars needed: inner_width - label.len() to align with content
    let top_bar_len = inner_width.saturating_sub(label.len());
    println!(
        "{}{}{}{} {}{}{} {}{}{}",
        indent_str,
        style.border,
        TOP_LEFT,
        HORIZONTAL,
        style.label,
        label,
        style.border,
        h(top_bar_len),
        TOP_RIGHT,
        style.reset
    );

    // Content lines: │ content │
    for line in lines {
        let vis_width = visible_width(line);
        // +1 because top line has: ─ + space + label + space + bars
        // content line has: space + content + padding + space
        // need to match the width
        let padding = inner_width.saturating_sub(vis_width) + 1;
        println!(
            "{}{}{}{} {}{} {}{}",
            indent_str,
            style.border,
            VERTICAL,
            style.reset,
            line,
            " ".repeat(padding),
            style.border,
            VERTICAL,
        );
    }

    // Bottom: ╰──────────────────╯
    // Width: 1 (space after ╭) + 1 (─) + 1 (space) + label.len() + 1 (space) + top_bar_len
    let bottom_bar_len = 3 + label.len() + top_bar_len;
    println!(
        "{}{}{}{}{}{}",
        indent_str,
        style.border,
        BOTTOM_LEFT,
        h(bottom_bar_len),
        BOTTOM_RIGHT,
        style.reset
    );
}
