// main.rs
//! Leak detection tool for Vole test suites.
//!
//! Runs Vole test files through the same compilation/JIT pipeline as `vole test`,
//! wrapping each test execution with alloc_track snapshots to detect memory leaks.

use std::cell::RefCell;
use std::fs;
use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::rc::Rc;

use clap::Parser;

use vole::cli::{ColorMode, expand_paths, should_skip_path};
use vole::commands::common::{PipelineOptions, compile_source, render_pipeline_error};
use vole_codegen::{AnalyzedProgram, CompiledModules, Compiler, JitContext, JitOptions, TestInfo};
use vole_runtime::{
    JmpBuf, alloc_track, call_setjmp, clear_current_test, clear_test_jmp_buf, recover_from_signal,
    set_current_file, set_current_test, set_stdout_capture, set_test_jmp_buf, take_assert_failure,
    take_stack_overflow,
};
use vole_sema::ModuleCache;

/// Default glob pattern for RC-specific test files.
const DEFAULT_GLOB: &str = "test/unit/codegen/rc_*.vole";

#[derive(Parser)]
#[command(name = "vole-leak")]
#[command(version = "0.1.0")]
#[command(about = "Leak detection for Vole test suites")]
struct Cli {
    /// Paths to test (files, directories, or glob patterns).
    /// Defaults to test/unit/codegen/rc_*.vole when omitted.
    #[arg(value_name = "PATHS")]
    paths: Vec<String>,
}

/// Per-type leak information for a single test.
struct TypeLeak {
    type_name: &'static str,
    count: i64,
}

/// Leak information for a single test.
struct LeakRecord {
    test_name: String,
    file: PathBuf,
    total_delta: i64,
    per_type: Vec<TypeLeak>,
}

/// Results from running leak detection across all files.
struct LeakResults {
    leaks: Vec<LeakRecord>,
    total_tests: usize,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    // Enable allocation tracking before any compilation/execution.
    alloc_track::enable_tracking();

    let paths = if cli.paths.is_empty() {
        vec![DEFAULT_GLOB.to_string()]
    } else {
        cli.paths
    };

    let files = match collect_files(&paths) {
        Ok(f) => f,
        Err(msg) => {
            eprintln!("error: {}", msg);
            return ExitCode::FAILURE;
        }
    };

    if files.is_empty() {
        eprintln!("error: no test files found");
        return ExitCode::FAILURE;
    }

    let results = run_leak_detection(&files);

    print_summary(&results, files.len());

    if results.leaks.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Collect and deduplicate test files from the given paths.
fn collect_files(paths: &[String]) -> Result<Vec<PathBuf>, String> {
    let expanded = expand_paths(paths).map_err(|e| e.to_string())?;

    let files: Vec<PathBuf> = expanded
        .explicit
        .into_iter()
        .chain(
            expanded
                .discovered
                .into_iter()
                .filter(|p| !should_skip_path(p)),
        )
        .collect();

    Ok(files)
}

/// Run all test files and collect leak records.
fn run_leak_detection(files: &[PathBuf]) -> LeakResults {
    let mut results = LeakResults {
        leaks: Vec::new(),
        total_tests: 0,
    };
    let cache = Rc::new(RefCell::new(ModuleCache::new()));
    let mut compiled_modules: Option<CompiledModules> = None;

    for file in files {
        set_current_file(&file.display().to_string());

        match compile_and_run_tests(file, cache.clone(), &mut compiled_modules) {
            Ok((file_leaks, test_count)) => {
                results.leaks.extend(file_leaks);
                results.total_tests += test_count;
            }
            Err(e) => {
                if !e.is_empty() {
                    eprintln!("error: {}: {}", file.display(), e);
                }
            }
        }
    }

    results
}

/// Compile a single file and run its tests with leak detection.
/// Returns leak records and the total number of tests executed.
fn compile_and_run_tests(
    path: &Path,
    cache: Rc<RefCell<ModuleCache>>,
    compiled_modules: &mut Option<CompiledModules>,
) -> Result<(Vec<LeakRecord>, usize), String> {
    let source = fs::read_to_string(path).map_err(|e| format!("could not read file: {}", e))?;
    let file_path = path.to_string_lossy();

    // Parse and type check with shared cache.
    let mut diag_buffer = Vec::new();
    let analyzed = match compile_source(
        PipelineOptions {
            source: &source,
            file_path: &file_path,
            skip_tests: false,
            project_root: None,
            module_cache: Some(cache),
            color_mode: ColorMode::Never,
        },
        &mut diag_buffer,
    ) {
        Ok(a) => a,
        Err(ref e) => {
            render_pipeline_error(
                e,
                &file_path,
                &source,
                &mut io::stderr(),
                ColorMode::Never,
                false,
            );
            return Err(String::new());
        }
    };

    // Check if cached modules cover all dependencies.
    let can_use_cache = compiled_modules.as_ref().is_some_and(|modules| {
        analyzed
            .module_programs
            .keys()
            .all(|module_path| modules.has_module(module_path))
    });

    let options = JitOptions::debug();

    let (jit, compile_result, tests) = if can_use_cache {
        compile_with_cached_modules(&analyzed, compiled_modules, options, &file_path)
    } else {
        compile_fresh(&analyzed, compiled_modules, options, &file_path)
    };

    if let Err(e) = compile_result {
        std::mem::forget(jit);
        return Err(format!("compilation error: {}", e));
    }

    let mut jit = jit;
    jit.finalize()?;

    let test_count = tests.len();
    let leaks = execute_tests_with_tracking(&tests, &jit, path);
    Ok((leaks, test_count))
}

/// Compile using pre-compiled cached modules.
fn compile_with_cached_modules(
    analyzed: &AnalyzedProgram,
    compiled_modules: &mut Option<CompiledModules>,
    options: JitOptions,
    file_path: &str,
) -> (JitContext, Result<(), String>, Vec<TestInfo>) {
    let modules = compiled_modules.as_ref().unwrap();
    let mut jit = JitContext::with_modules_and_options(modules, options);
    let mut compiler = Compiler::new(&mut jit, analyzed);
    compiler.set_source_file(file_path);

    let _ = compiler.import_modules();
    let result = compiler
        .compile_program_only(&analyzed.program)
        .map_err(|e| e.to_string());
    let tests = compiler.take_tests();

    (jit, result, tests)
}

/// Compile from scratch, caching modules for subsequent files.
fn compile_fresh(
    analyzed: &AnalyzedProgram,
    compiled_modules: &mut Option<CompiledModules>,
    options: JitOptions,
    file_path: &str,
) -> (JitContext, Result<(), String>, Vec<TestInfo>) {
    let mut jit = JitContext::with_options(options);
    let mut compiler = Compiler::new(&mut jit, analyzed);
    compiler.set_source_file(file_path);

    let modules_result = compiler.compile_modules_only();
    let result = if modules_result.is_ok() {
        compiler
            .compile_program_only(&analyzed.program)
            .map_err(|e| e.to_string())
    } else {
        modules_result.map_err(|e| e.to_string())
    };
    let tests = compiler.take_tests();

    // Cache modules for future files.
    if result.is_ok() && !analyzed.module_programs.is_empty() {
        let mut modules_jit = JitContext::with_options(options);
        let compile_result = {
            let mut modules_compiler = Compiler::new(&mut modules_jit, analyzed);
            modules_compiler.compile_modules_only()
        };
        match compile_result {
            Ok(()) => {
                let module_paths: Vec<String> = analyzed.module_programs.keys().cloned().collect();
                match CompiledModules::new(modules_jit, module_paths) {
                    Ok(modules) => *compiled_modules = Some(modules),
                    Err(_) => {}
                }
            }
            Err(_) => {
                std::mem::forget(modules_jit);
            }
        }
    }

    (jit, result, tests)
}

/// Execute tests with alloc_track snapshot/delta around each test.
fn execute_tests_with_tracking(
    tests: &[TestInfo],
    jit: &JitContext,
    file: &Path,
) -> Vec<LeakRecord> {
    let mut leaks = Vec::new();
    let file_path = file.to_path_buf();

    for test in tests {
        let func_ptr = match jit.get_function_ptr_by_id(test.func_id) {
            Some(ptr) => ptr,
            None => continue,
        };

        let test_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(func_ptr) };

        set_current_test(&test.name);

        // Reset and snapshot before test.
        alloc_track::reset();
        let snap = alloc_track::snapshot();

        // Suppress stdout during test execution.
        set_stdout_capture(Some(Box::new(io::sink())));

        let mut jmp_buf: JmpBuf = JmpBuf::zeroed();
        set_test_jmp_buf(&mut jmp_buf);

        let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
            if call_setjmp(&mut jmp_buf) == 0 {
                test_fn();
            } else {
                recover_from_signal();
                let _ = take_stack_overflow();
                let _ = take_assert_failure();
            }
        }));

        clear_test_jmp_buf();
        clear_current_test();
        set_stdout_capture(None);

        // Check for leaks.
        let d = alloc_track::delta(snap);
        if d != 0 {
            let per_type: Vec<TypeLeak> = alloc_track::report()
                .into_iter()
                .map(|(type_id, count)| TypeLeak {
                    type_name: alloc_track::type_name(type_id),
                    count,
                })
                .collect();

            leaks.push(LeakRecord {
                test_name: test.name.clone(),
                file: file_path.clone(),
                total_delta: d,
                per_type,
            });
        }
    }

    leaks
}

/// Print the final summary table.
fn print_summary(results: &LeakResults, file_count: usize) {
    if results.leaks.is_empty() {
        println!(
            "\nNo leaks detected ({} tests across {} files)",
            results.total_tests, file_count
        );
        return;
    }

    println!("\nLeak summary:");
    println!("{:-<72}", "");

    let mut current_file: Option<&Path> = None;

    for leak in &results.leaks {
        if current_file != Some(leak.file.as_path()) {
            println!("\n{}", leak.file.display());
            current_file = Some(leak.file.as_path());
        }

        let breakdown: String = leak
            .per_type
            .iter()
            .map(|t| format!("{}: {:+}", t.type_name, t.count))
            .collect::<Vec<_>>()
            .join(", ");

        println!(
            "  {} (delta: {:+}) [{}]",
            leak.test_name, leak.total_delta, breakdown
        );
    }

    println!("\n{:-<72}", "");
    println!(
        "{} leaking test{} ({} tests across {} files)",
        results.leaks.len(),
        if results.leaks.len() == 1 { "" } else { "s" },
        results.total_tests,
        file_count
    );
}
