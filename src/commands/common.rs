// src/commands/common.rs
//! Shared utilities for CLI commands.

use std::io::{self, IsTerminal, Read, Write};

use miette::NamedSource;

use std::collections::HashMap;

use crate::cli::ColorMode;
use crate::codegen::{Compiler, JitContext};
use crate::errors::{LexerError, render_to_stderr, render_to_writer};
use crate::frontend::{AstPrinter, Interner, ParseError, Parser, ast::Program};
use crate::identity::NameTable;
use crate::runtime::set_stdout_capture;
use crate::sema::generic::MonomorphCache;
use crate::sema::{
    AnalysisOutput, Analyzer, EntityRegistry, ExpressionData, ImplementRegistry, ProgramQuery,
    TypeError, TypeTable, TypeWarning, WellKnownTypes,
};
use crate::transforms;

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Interner,
    /// All expression-level metadata (types, method resolutions, generic calls)
    pub expression_data: ExpressionData,
    pub implement_registry: ImplementRegistry,
    /// Parsed module programs for compiling pure Vole functions
    pub module_programs: HashMap<String, (Program, Interner)>,
    /// Cache of monomorphized function instances
    pub monomorph_cache: MonomorphCache,
    /// External function info by string name (module path and native name) for prelude functions
    pub external_func_info: HashMap<String, crate::sema::implement_registry::ExternalMethodInfo>,
    /// Qualified name interner for printable identities
    pub name_table: NameTable,
    /// Opaque type identities for named types
    pub type_table: TypeTable,
    /// Well-known stdlib type NameIds for fast comparison
    pub well_known: WellKnownTypes,
    /// Entity registry for first-class type/method/field/function identity
    pub entity_registry: EntityRegistry,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    pub fn from_analysis(program: Program, interner: Interner, output: AnalysisOutput) -> Self {
        Self {
            program,
            interner,
            expression_data: output.expression_data,
            implement_registry: output.implement_registry,
            module_programs: output.module_programs,
            monomorph_cache: output.monomorph_cache,
            external_func_info: output.external_func_info,
            name_table: output.name_table,
            type_table: output.type_table,
            well_known: output.well_known,
            entity_registry: output.entity_registry,
        }
    }

    /// Get a query interface for accessing type information and analysis results.
    pub fn query(&self) -> ProgramQuery<'_> {
        ProgramQuery::new(&self.entity_registry, &self.expression_data)
    }
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

/// Render a semantic warning to stderr
fn render_sema_warning(warn: &TypeWarning, file_path: &str, source: &str) {
    let report = miette::Report::new(warn.warning.clone())
        .with_source_code(NamedSource::new(file_path, source.to_string()));
    render_to_stderr(report.as_ref());
}

/// Parse and analyze a source file, rendering any diagnostics on error.
///
/// Returns `Ok(AnalyzedProgram)` on success, or `Err(())` if there were
/// errors (diagnostics are rendered to stderr before returning).
#[allow(clippy::result_unit_err)] // Error details are rendered internally
pub fn parse_and_analyze(source: &str, file_path: &str) -> Result<AnalyzedProgram, ()> {
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
        let mut analyzer = Analyzer::new(file_path, source);
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

    let output = analyzer.into_analysis_results();
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

    // Type check
    let mut analyzer = Analyzer::new(file_path, source);
    if let Err(errors) = analyzer.analyze(&program, &interner) {
        for err in &errors {
            render_sema_error_to(err, file_path, source, &mut stderr);
        }
        return Err(());
    }
    let output = analyzer.into_analysis_results();
    let analyzed = AnalyzedProgram::from_analysis(program, interner, output);

    // Compile
    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        if let Err(e) = compiler.compile_program(&analyzed.program) {
            let _ = writeln!(stderr, "compilation error: {}", e);
            return Err(());
        }
    }
    let _ = jit.finalize();

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
