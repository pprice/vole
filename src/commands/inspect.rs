// src/commands/inspect.rs

use std::fs;
use std::process::ExitCode;

use miette::NamedSource;

use crate::cli::{InspectType, expand_paths};
use crate::codegen::{Compiler, JitContext};
use crate::errors::render_to_stderr;
use crate::frontend::{AstPrinter, Parser};
use crate::sema::Analyzer;

/// Inspect compilation output for the given files
pub fn inspect_files(
    patterns: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    _imports: Option<&str>,
) -> ExitCode {
    // Expand patterns and collect unique files
    let files = match expand_paths(patterns) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::FAILURE;
        }
    };

    if files.is_empty() {
        eprintln!("error: no .vole files found");
        return ExitCode::FAILURE;
    }

    let mut had_error = false;

    for (i, path) in files.iter().enumerate() {
        // Print separator between files
        if i > 0 {
            println!();
        }

        // Print file header to stderr
        eprintln!("// {}", path.display());

        // Read source
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: could not read '{}': {}", path.display(), e);
                had_error = true;
                continue;
            }
        };

        let file_path = path.to_string_lossy();

        match inspect_type {
            InspectType::Ast => {
                // Parse
                let mut parser = Parser::with_file(&source, &file_path);
                let program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        let report = miette::Report::new(e.error.clone())
                            .with_source_code(NamedSource::new(&file_path, source.clone()));
                        render_to_stderr(report.as_ref());
                        had_error = true;
                        continue;
                    }
                };

                let interner = parser.into_interner();
                let printer = AstPrinter::new(&interner, no_tests);
                print!("{}", printer.print_program(&program));
            }
            InspectType::Ir => {
                // Parse
                let mut parser = Parser::with_file(&source, &file_path);
                let program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        let report = miette::Report::new(e.error.clone())
                            .with_source_code(NamedSource::new(&file_path, source.clone()));
                        render_to_stderr(report.as_ref());
                        had_error = true;
                        continue;
                    }
                };

                let interner = parser.into_interner();

                // Type check
                let mut analyzer = Analyzer::new(&file_path, &source);
                if let Err(errors) = analyzer.analyze(&program, &interner) {
                    for err in &errors {
                        let report = miette::Report::new(err.error.clone())
                            .with_source_code(NamedSource::new(&file_path, source.clone()));
                        render_to_stderr(report.as_ref());
                    }
                    had_error = true;
                    continue;
                }
                let (
                    type_aliases,
                    expr_types,
                    method_resolutions,
                    interface_registry,
                    type_implements,
                    error_types,
                    module_programs,
                    generic_functions,
                    monomorph_cache,
                    generic_calls,
                ) = analyzer.into_analysis_results();

                // Generate IR
                let mut jit = JitContext::new();
                let mut compiler = Compiler::new(
                    &mut jit,
                    &interner,
                    type_aliases,
                    expr_types,
                    method_resolutions,
                    interface_registry,
                    type_implements,
                    error_types,
                    module_programs,
                    generic_functions,
                    monomorph_cache,
                    generic_calls,
                );
                let include_tests = !no_tests;

                if let Err(e) =
                    compiler.compile_to_ir(&program, &mut std::io::stdout(), include_tests)
                {
                    eprintln!("error: {}", e);
                    had_error = true;
                }
            }
        }
    }

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
