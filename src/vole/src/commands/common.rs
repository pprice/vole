// src/commands/common.rs
//! Shared utilities for CLI commands.

use std::io::{self, IsTerminal, Read, Write};

use miette::NamedSource;

use std::cell::RefCell;
use std::rc::Rc;

use crate::cli::ColorMode;
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::errors::{LexerError, render_to_writer};
use crate::frontend::{AstPrinter, ParseError, Parser};
use crate::runtime::{
    JmpBuf, call_setjmp, clear_test_jmp_buf, set_capture_mode, set_stderr_capture,
    set_stdout_capture, set_test_jmp_buf, write_to_stderr_capture,
};
use crate::sema::{ModuleCache, TypeError, TypeWarning, optimize_all};
use crate::transforms;

// Re-export AnalyzedProgram from codegen
pub use crate::codegen::AnalyzedProgram;

/// Render a lexer error to a writer with source context.
fn render_lexer_error(err: &LexerError, file_path: &str, source: &str, w: &mut dyn Write) {
    let report = miette::Report::new(err.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), w);
}

/// Render a parser error to a writer with source context.
fn render_parser_error(err: &ParseError, file_path: &str, source: &str, w: &mut dyn Write) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), w);
}

/// Render a semantic error to a writer with source context.
fn render_sema_error(err: &TypeError, file_path: &str, source: &str, w: &mut dyn Write) {
    let report = miette::Report::new(err.error.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), w);
}

/// Render a semantic warning to a writer with source context.
fn render_sema_warning(warn: &TypeWarning, file_path: &str, source: &str, w: &mut dyn Write) {
    let report = miette::Report::new(warn.warning.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    let _ = render_to_writer(report.as_ref(), w);
}

/// Options for the compile_source pipeline.
pub struct PipelineOptions<'a> {
    pub source: &'a str,
    pub file_path: &'a str,
    pub skip_tests: bool,
    pub project_root: Option<&'a std::path::Path>,
    pub module_cache: Option<Rc<RefCell<ModuleCache>>>,
}

/// Compile source through the full pipeline: parse -> transform -> analyze -> optimize.
///
/// All diagnostics (errors and warnings) are rendered to the provided `errors` writer.
/// Returns `Ok(AnalyzedProgram)` on success, or `Err(())` if there were errors.
#[allow(clippy::result_unit_err)]
pub fn compile_source(
    opts: PipelineOptions,
    errors: &mut dyn Write,
) -> Result<AnalyzedProgram, ()> {
    let PipelineOptions {
        source,
        file_path,
        skip_tests,
        project_root,
        module_cache,
    } = opts;

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
                        render_lexer_error(err, file_path, source, errors);
                    }
                } else {
                    render_parser_error(&e, file_path, source, errors);
                }
                return Err(());
            }
        };

        // Check for lexer errors that didn't cause parse failure
        let lexer_errors = parser.take_lexer_errors();
        if !lexer_errors.is_empty() {
            for err in &lexer_errors {
                render_lexer_error(err, file_path, source, errors);
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
                render_sema_error(err, file_path, source, errors);
            }
            return Err(());
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
                render_sema_error(err, file_path, source, errors);
            }
            return Err(());
        }
        tracing::debug!("type checking complete");
        analyzer
    };

    // Render any warnings (non-fatal diagnostics)
    for warn in &analyzer.take_warnings() {
        render_sema_warning(warn, file_path, source, errors);
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

/// Options for the compile_and_run codegen+execution pipeline.
pub struct RunOptions<'a> {
    pub file_path: &'a str,
    pub jit_options: JitOptions,
    pub skip_tests: bool,
}

/// Compile an analyzed program to machine code and execute it.
///
/// Handles: JIT compilation, finalization, main lookup, and execution
/// with jmp_buf panic recovery. Compilation errors are written to `errors`.
///
/// The caller is responsible for setting up stdout/stderr capture (via
/// `set_stdout_capture`/`set_stderr_capture`) before calling if needed.
#[allow(clippy::result_unit_err)]
pub fn compile_and_run(
    analyzed: &AnalyzedProgram,
    opts: &RunOptions,
    errors: &mut dyn Write,
) -> Result<(), ()> {
    // Codegen phase
    let jit = {
        let _span = tracing::info_span!("codegen").entered();
        let mut jit = JitContext::with_options(opts.jit_options);
        {
            let mut compiler = Compiler::new(&mut jit, analyzed);
            compiler.set_source_file(opts.file_path);
            compiler.set_skip_tests(opts.skip_tests);
            if let Err(e) = compiler.compile_program(&analyzed.program) {
                let _ = writeln!(errors, "compilation error: {}", e);
                return Err(());
            }
        }
        if let Err(e) = jit.finalize() {
            let _ = writeln!(errors, "finalization error: {}", e);
            return Err(());
        }
        tracing::debug!("compilation complete");
        jit
    };

    // Execute phase
    let fn_ptr = match jit.get_function_ptr("main") {
        Some(ptr) => ptr,
        None => {
            let _ = writeln!(errors, "error: no 'main' function found");
            return Err(());
        }
    };

    let _span = tracing::info_span!("execute").entered();
    let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };

    // Use jmp_buf for panic recovery — safely handles runtime panics
    // instead of crashing the host process.
    let mut jmp_buf = JmpBuf::zeroed();
    set_test_jmp_buf(&mut jmp_buf);

    unsafe {
        if call_setjmp(&mut jmp_buf) == 0 {
            main();
        }
        // If longjmp occurred (from panic), we just continue
    }

    clear_test_jmp_buf();

    Ok(())
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
    compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: false,
            project_root: None,
            module_cache: None,
        },
        &mut stderr,
    )?;
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
    let analyzed = compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: true,
            project_root: None,
            module_cache: None,
        },
        &mut stderr,
    )?;

    let run_opts = RunOptions {
        file_path,
        jit_options: JitOptions::default(),
        skip_tests: true,
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
                    render_lexer_error(err, file_path, source, &mut stderr);
                }
            } else {
                render_parser_error(&e, file_path, source, &mut stderr);
            }
            return Err(());
        }
    };

    let lexer_errors = parser.take_lexer_errors();
    if !lexer_errors.is_empty() {
        for err in &lexer_errors {
            render_lexer_error(err, file_path, source, &mut stderr);
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
