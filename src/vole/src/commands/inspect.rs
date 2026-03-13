// src/commands/inspect.rs

use std::cell::RefCell;
use std::fs;
use std::process::ExitCode;
use std::rc::Rc;

use crate::cli::{ColorMode, InspectType, expand_paths_flat};
use crate::codegen::VirPrinter;
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::commands::common::{PipelineOptions, compile_source, render_pipeline_error};
use crate::commands::mir_format::format_mir;
use crate::frontend::{AstPrinter, ModuleId, Parser};
use crate::sema::ModuleCache;

/// Inspect compilation output for the given files
pub fn inspect_files(
    patterns: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    release: bool,
    show_all: bool,
    color_mode: ColorMode,
    function_filter: Option<&str>,
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

    // Derive project root from the first file's parent directory so that
    // module imports resolve correctly when inspecting multi-module projects.
    let project_root = files
        .first()
        .and_then(|f| f.parent())
        .map(|p| p.to_path_buf());

    // Shared module cache so imported modules are resolved once across files.
    let module_cache = Rc::new(RefCell::new(ModuleCache::new()));

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
                let mut parser = Parser::new(&source, ModuleId::new(0));
                let program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        let lexer_errors = parser.take_lexer_errors();
                        let err = if !lexer_errors.is_empty() {
                            super::common::PipelineError::Lex(lexer_errors)
                        } else {
                            super::common::PipelineError::Parse(e)
                        };
                        render_pipeline_error(
                            &err,
                            &file_path,
                            &source,
                            &mut std::io::stderr(),
                            color_mode,
                            false,
                        );
                        had_error = true;
                        continue;
                    }
                };

                let interner = parser.into_interner();
                let printer = AstPrinter::new(&interner, no_tests);
                print!("{}", printer.print_program(&program));
            }
            InspectType::Ir => {
                let result = compile_source(
                    PipelineOptions {
                        source: &source,
                        file_path: &file_path,
                        skip_tests: no_tests,
                        project_root: project_root.as_deref(),
                        module_cache: Some(module_cache.clone()),
                        module_vir_cache: None,
                        color_mode,
                    },
                    &mut std::io::stderr(),
                );
                let analyzed = match result {
                    Ok(a) => a,
                    Err(ref e) => {
                        render_pipeline_error(
                            e,
                            &file_path,
                            &source,
                            &mut std::io::stderr(),
                            color_mode,
                            false,
                        );
                        had_error = true;
                        continue;
                    }
                };
                let mut options = if release {
                    JitOptions::release()
                } else {
                    JitOptions::default()
                };
                options.capture_ir = true;
                options.lazy_modules = false; // Inspect needs all bodies compiled
                let mut jit = JitContext::with_options(options);
                let mut compiler = Compiler::new(&mut jit, &analyzed);
                compiler.set_skip_tests(no_tests);

                if let Err(e) = compiler.compile_program() {
                    eprintln!("error: {}", e);
                    had_error = true;
                    continue;
                }

                let include_tests = !no_tests;
                for (func_name, ir_text) in jit.get_ir() {
                    if !matches_function_filter(func_name, function_filter, show_all, include_tests)
                    {
                        continue;
                    }

                    println!("// func {}", func_name);
                    println!("{}", ir_text);
                }
            }
            InspectType::Mir => {
                let result = compile_source(
                    PipelineOptions {
                        source: &source,
                        file_path: &file_path,
                        skip_tests: false,
                        project_root: project_root.as_deref(),
                        module_cache: Some(module_cache.clone()),
                        module_vir_cache: None,
                        color_mode,
                    },
                    &mut std::io::stderr(),
                );
                let analyzed = match result {
                    Ok(a) => a,
                    Err(ref e) => {
                        render_pipeline_error(
                            e,
                            &file_path,
                            &source,
                            &mut std::io::stderr(),
                            color_mode,
                            false,
                        );
                        had_error = true;
                        continue;
                    }
                };
                let options = JitOptions::disasm();
                let mut jit = JitContext::with_options(options);
                let mut compiler = Compiler::new(&mut jit, &analyzed);
                let include_tests = !no_tests;

                if let Err(e) = compiler.compile_program() {
                    eprintln!("error: {}", e);
                    had_error = true;
                    continue;
                }

                // Print disassembly
                for (func_name, asm) in jit.get_disasm() {
                    if !matches_function_filter(func_name, function_filter, show_all, include_tests)
                    {
                        continue;
                    }

                    println!("// func {}", func_name);
                    println!("{}", format_mir(asm));
                }
            }
            InspectType::Vir => {
                inspect_vir(
                    &source,
                    &file_path,
                    project_root.as_deref(),
                    &module_cache,
                    color_mode,
                    no_tests,
                    show_all,
                    function_filter,
                    &mut had_error,
                );
            }
        }
    }

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Run parse + sema + VIR lowering, then pretty-print all VIR functions.
#[allow(clippy::too_many_arguments)]
fn inspect_vir(
    source: &str,
    file_path: &str,
    project_root: Option<&std::path::Path>,
    module_cache: &Rc<RefCell<ModuleCache>>,
    color_mode: ColorMode,
    no_tests: bool,
    show_all: bool,
    function_filter: Option<&str>,
    had_error: &mut bool,
) {
    let result = compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: no_tests,
            project_root,
            module_cache: Some(module_cache.clone()),
            module_vir_cache: None,
            color_mode,
        },
        &mut std::io::stderr(),
    );
    let analyzed = match result {
        Ok(a) => a,
        Err(ref e) => {
            render_pipeline_error(
                e,
                file_path,
                source,
                &mut std::io::stderr(),
                color_mode,
                false,
            );
            *had_error = true;
            return;
        }
    };

    let printer = VirPrinter::new(&analyzed);

    let include_tests = !no_tests;
    let main_module = analyzed.module_id;

    for func in &analyzed.functions {
        if !matches_function_filter(&func.name, function_filter, show_all, include_tests) {
            continue;
        }
        if !show_all && !analyzed.vir_function_in_module(func, main_module) {
            continue;
        }
        print!("{}", printer.print_function(func));
    }

    // Print generic VIR function templates (pre-monomorphization)
    let has_generic_match = analyzed
        .generic_functions
        .iter()
        .any(|func| matches_function_filter(&func.name, function_filter, show_all, include_tests));
    if has_generic_match {
        println!("// --- generic VIR templates ---");
        for func in &analyzed.generic_functions {
            if !matches_function_filter(&func.name, function_filter, show_all, include_tests) {
                continue;
            }
            print!("{}", printer.print_function(func));
        }
    }

    // Print VIR test bodies (skip when filtering by function name)
    if function_filter.is_none() && include_tests && !analyzed.tests.is_empty() {
        println!("tests {{");
        for test in &analyzed.tests {
            // Indent each line of the test output
            for line in printer.print_test(test).lines() {
                println!("  {line}");
            }
        }
        println!("}}");
    }
}

/// Check if a function name passes all active filters.
fn matches_function_filter(
    name: &str,
    function_filter: Option<&str>,
    show_all: bool,
    include_tests: bool,
) -> bool {
    if !show_all && is_prelude_function(name) {
        return false;
    }
    if !include_tests && is_test_function(name) {
        return false;
    }
    if let Some(filter) = function_filter
        && !name.contains(filter)
    {
        return false;
    }
    true
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
