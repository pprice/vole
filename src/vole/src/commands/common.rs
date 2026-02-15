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
/// Each variant carries the structured error data from the failed phase,
/// allowing callers to inspect errors programmatically or render them
/// via [`render_pipeline_error`].
#[derive(Debug)]
pub enum PipelineError {
    /// Lexer encountered invalid tokens
    Lex(Vec<LexerError>),
    /// Parser encountered syntax errors
    Parse(ParseError),
    /// Generator transformation failed
    Transform(Vec<TypeError>),
    /// Type checking failed
    Sema(Vec<TypeError>),
    /// Code generation failed
    Codegen(CodegenError),
    /// Program finalization failed
    Finalize(CodegenError),
    /// No main function found
    NoMain {
        file_path: String,
        hint: Option<String>,
    },
    /// I/O error (file not found, permission denied, etc.)
    Io(io::Error),
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

/// Render a pipeline error to a writer with source context.
///
/// This is the top-level rendering entry point for all compilation errors.
/// Callers should use this after receiving an `Err(PipelineError)` from
/// `compile_source` or `compile_and_run`.
pub fn render_pipeline_error(
    err: &PipelineError,
    file_path: &str,
    source: &str,
    w: &mut dyn Write,
    color_mode: ColorMode,
    run_mode: bool,
) {
    match err {
        PipelineError::Lex(errors) => {
            for e in errors {
                render_lexer_error(e, file_path, source, w, color_mode);
            }
        }
        PipelineError::Parse(e) => {
            render_parser_error(e, file_path, source, run_mode, w, color_mode);
        }
        PipelineError::Transform(errors) | PipelineError::Sema(errors) => {
            for e in errors {
                render_sema_error(e, file_path, source, w, color_mode);
            }
        }
        PipelineError::Codegen(e) | PipelineError::Finalize(e) => {
            render_codegen_error(e, file_path, source, w, color_mode);
        }
        PipelineError::NoMain { file_path, hint } => {
            let _ = writeln!(w, "error: no 'main' function found in {}", file_path);
            if let Some(h) = hint {
                let _ = writeln!(w, "hint: {}", h);
            }
        }
        PipelineError::Io(e) => {
            let _ = writeln!(w, "error: {}", e);
        }
    }
}

/// Options for the compile_source pipeline.
pub struct PipelineOptions<'a> {
    pub source: &'a str,
    pub file_path: &'a str,
    pub skip_tests: bool,
    pub project_root: Option<&'a std::path::Path>,
    pub module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// Color mode for diagnostic rendering (used for warnings).
    pub color_mode: ColorMode,
}

/// Compile source through the full pipeline: parse -> transform -> analyze -> optimize.
///
/// Warnings are rendered to the `warnings` writer as they are discovered.
/// Errors are returned as structured `PipelineError` variants for the caller
/// to render via [`render_pipeline_error`].
pub fn compile_source(
    opts: PipelineOptions,
    warnings: &mut dyn Write,
) -> Result<AnalyzedProgram, PipelineError> {
    let PipelineOptions {
        source,
        file_path,
        skip_tests,
        project_root,
        module_cache,
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
                    return Err(PipelineError::Lex(lexer_errors));
                } else {
                    return Err(PipelineError::Parse(e));
                }
            }
        };

        // Check for lexer errors that didn't cause parse failure
        let lexer_errors = parser.take_lexer_errors();
        if !lexer_errors.is_empty() {
            return Err(PipelineError::Lex(lexer_errors));
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
            return Err(PipelineError::Transform(transform_errors));
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
            return Err(PipelineError::Sema(errs));
        }
        tracing::debug!("type checking complete");
        analyzer
    };

    // Render any warnings (non-fatal diagnostics)
    for warn in &analyzer.take_warnings() {
        render_sema_warning(warn, file_path, source, warnings, color_mode);
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
    pub jit_options: JitOptions,
    pub skip_tests: bool,
}

/// Compile an analyzed program to machine code and execute it.
///
/// Handles: JIT compilation, finalization, main lookup, and execution
/// with jmp_buf panic recovery. Returns structured errors in `PipelineError`
/// for the caller to render.
///
/// The caller is responsible for setting up stdout/stderr capture (via
/// `set_stdout_capture`/`set_stderr_capture`) before calling if needed.
pub fn compile_and_run(analyzed: &AnalyzedProgram, opts: &RunOptions) -> Result<(), PipelineError> {
    // Codegen phase
    let jit = {
        let _span = tracing::info_span!("codegen").entered();
        let mut jit = JitContext::with_options(opts.jit_options);
        {
            let mut compiler = Compiler::new(&mut jit, analyzed);
            compiler.set_source_file(opts.file_path);
            compiler.set_skip_tests(opts.skip_tests);
            if let Err(e) = compiler.compile_program(&analyzed.program) {
                return Err(PipelineError::Codegen(e));
            }
        }
        if let Err(e) = jit.finalize() {
            return Err(PipelineError::Finalize(e));
        }
        tracing::debug!("compilation complete");
        jit
    };

    // Execute phase
    let fn_ptr = match jit.get_function_ptr("main") {
        Some(ptr) => ptr,
        None => {
            return Err(PipelineError::NoMain {
                file_path: opts.file_path.to_string(),
                hint: suggest_main_function(&jit),
            });
        }
    };

    let _span = tracing::info_span!("execute").entered();
    // SAFETY: `fn_ptr` is obtained from `JitContext::get_function_ptr("main")`, which
    // returns a pointer to JIT-compiled code with the extern "C" fn() calling convention.
    // The codegen backend guarantees the "main" entry point takes no arguments and returns
    // void, matching the target signature.
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
/// Errors and warnings are rendered to `stderr`; the returned `PipelineError`
/// indicates which phase failed.
pub fn check_captured<W: Write + Send + 'static>(
    source: &str,
    file_path: &str,
    mut stderr: W,
    color_mode: ColorMode,
) -> Result<(), PipelineError> {
    let result = compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: false,
            project_root: None,
            module_cache: None,
            color_mode,
        },
        &mut stderr,
    );
    if let Err(ref e) = result {
        render_pipeline_error(e, file_path, source, &mut stderr, color_mode, false);
    }
    result?;
    Ok(())
}

/// Run a program with captured stdout and stderr.
///
/// Errors and warnings are rendered to `stderr`; the returned `PipelineError`
/// indicates which phase failed.
pub fn run_captured<W: Write + Send + 'static>(
    source: &str,
    file_path: &str,
    stdout: W,
    mut stderr: W,
    color_mode: ColorMode,
) -> Result<(), PipelineError> {
    let compile_result = compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: true,
            project_root: None,
            module_cache: None,
            color_mode,
        },
        &mut stderr,
    );
    if let Err(ref e) = compile_result {
        render_pipeline_error(e, file_path, source, &mut stderr, color_mode, true);
    }
    let analyzed = compile_result?;

    let run_opts = RunOptions {
        file_path,
        jit_options: JitOptions::default(),
        skip_tests: true,
    };

    // Set up stdout/stderr capture for the JIT program's print() calls
    set_stdout_capture(Some(Box::new(stdout)));
    set_stderr_capture(Some(Box::new(stderr)));
    set_capture_mode(true);

    let result = compile_and_run(&analyzed, &run_opts);

    // Render any codegen errors to the captured stderr before tearing down
    if let Err(ref e) = result {
        let mut error_buf = Vec::new();
        render_pipeline_error(e, file_path, source, &mut error_buf, color_mode, true);
        if !error_buf.is_empty() {
            write_to_stderr_capture(&error_buf);
        }
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
            let err = if !lexer_errors.is_empty() {
                PipelineError::Lex(lexer_errors)
            } else {
                PipelineError::Parse(e)
            };
            render_pipeline_error(&err, file_path, source, &mut stderr, color_mode, false);
            return Err(err);
        }
    };

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        let err = PipelineError::Lex(lexer_errors);
        render_pipeline_error(&err, file_path, source, &mut stderr, color_mode, false);
        return Err(err);
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
