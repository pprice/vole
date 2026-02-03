// src/commands/inspect.rs

use std::fs;
use std::process::ExitCode;

use miette::NamedSource;

use crate::cli::{InspectType, expand_paths_flat};
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::commands::common::{PipelineOptions, compile_source};
use crate::commands::mir_format::format_mir;
use crate::errors::render_to_stderr;
use crate::frontend::{AstPrinter, Parser};

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
                let analyzed = match compile_source(
                    PipelineOptions {
                        source: &source,
                        file_path: &file_path,
                        skip_tests: false,
                        project_root: None,
                        module_cache: None,
                    },
                    &mut std::io::stderr(),
                ) {
                    Ok(a) => a,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                };
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
                let analyzed = match compile_source(
                    PipelineOptions {
                        source: &source,
                        file_path: &file_path,
                        skip_tests: false,
                        project_root: None,
                        module_cache: None,
                    },
                    &mut std::io::stderr(),
                ) {
                    Ok(a) => a,
                    Err(_) => {
                        had_error = true;
                        continue;
                    }
                };
                let options = JitOptions::disasm();
                let mut jit = JitContext::with_options(options);
                let mut compiler = Compiler::new(&mut jit, &analyzed);
                let include_tests = !no_tests;

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

                    // Skip test functions when --no-tests is specified
                    if !include_tests && is_test_function(func_name) {
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

/// Check if a function name is a test function.
fn is_test_function(name: &str) -> bool {
    // Test functions are named "__test_{idx}" by the compiler
    name.starts_with("__test_")
}
