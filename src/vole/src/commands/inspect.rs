// src/commands/inspect.rs

use std::fs;
use std::process::ExitCode;

use miette::NamedSource;

use crate::cli::{InspectType, expand_paths_flat};
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::commands::common::AnalyzedProgram;
use crate::commands::mir_format::format_mir;
use crate::errors::render_to_stderr;
use crate::frontend::{AstPrinter, Parser};
use crate::sema::{Analyzer, optimize_all};

/// Inspect compilation output for the given files
pub fn inspect_files(
    patterns: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    _imports: Option<&str>,
    release: bool,
    show_all: bool,
) -> ExitCode {
    // Expand patterns and collect unique files
    let files = match expand_paths_flat(patterns) {
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
                let mut program = match parser.parse_program() {
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
                let mut output = analyzer.into_analysis_results();

                // Optimizer phase (constant folding, algebraic simplifications)
                let _stats = optimize_all(&mut program, &interner, &mut output.expression_data);

                // Generate IR
                let analyzed = AnalyzedProgram::from_analysis(program, interner, output);
                // For IR inspection, always enable loop optimization to show optimized IR
                let options = if release {
                    JitOptions::release()
                } else {
                    JitOptions::disasm() // Use disasm options to enable loop optimization
                };
                let mut jit = JitContext::with_options(options);
                let mut compiler = Compiler::new(&mut jit, &analyzed);
                let include_tests = !no_tests;

                if let Err(e) =
                    compiler.compile_to_ir(&analyzed.program, &mut std::io::stdout(), include_tests)
                {
                    eprintln!("error: {}", e);
                    had_error = true;
                }
            }
            InspectType::Mir => {
                // Parse
                let mut parser = Parser::with_file(&source, &file_path);
                let mut program = match parser.parse_program() {
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
                let mut output = analyzer.into_analysis_results();

                // Optimizer phase (constant folding, algebraic simplifications)
                let _stats = optimize_all(&mut program, &interner, &mut output.expression_data);

                // Generate assembly with disasm enabled
                let analyzed = AnalyzedProgram::from_analysis(program, interner, output);
                let options = JitOptions::disasm();
                let mut jit = JitContext::with_options(options);
                let mut compiler = Compiler::new(&mut jit, &analyzed);
                let _include_tests = !no_tests; // TODO: filter tests from asm output

                if let Err(e) = compiler.compile_program(&analyzed.program) {
                    eprintln!("error: {}", e);
                    had_error = true;
                    continue;
                }

                // Print disassembly
                for (func_name, asm) in jit.get_disasm() {
                    // Skip prelude/std functions unless --all is specified
                    if !show_all && is_prelude_function(func_name) {
                        continue;
                    }

                    println!("// func {}", func_name);
                    println!("{}", format_mir(asm));
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

/// Check if a function name is from the prelude/std library.
fn is_prelude_function(name: &str) -> bool {
    // Prelude functions have paths like "std:prelude/bool::bool::default_value"
    name.starts_with("std:")
        || name.starts_with("prelude/")
        || name.contains("::default_value")
        || name.contains("::min_value")
        || name.contains("::max_value")
}
