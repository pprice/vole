// src/commands/test.rs
//
// Test runner command for the Vole compiler.
// Discovers and executes tests from Vole source files.

use std::fs;
use std::io::{self, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use super::common::{PipelineOptions, TermColors, compile_source, read_stdin};
use crate::cli::{ColorMode, expand_paths, should_skip_path};
use crate::codegen::{CompiledModules, Compiler, JitContext, JitOptions, TestInfo};
use crate::runtime::{
    AssertFailure, JmpBuf, call_setjmp, clear_current_test, clear_test_jmp_buf, set_current_file,
    set_current_test, set_stdout_capture, set_test_jmp_buf, take_assert_failure,
};
use crate::sema::ModuleCache;
use crate::util::format_duration;
use std::cell::RefCell;
use std::rc::Rc;

/// Options for running tests, used by the public API.
pub struct TestRunOptions<'a> {
    /// Filter tests by name (substring match)
    pub filter: Option<&'a str>,
    /// Show verbose output (per-test results)
    pub verbose: bool,
    /// Maximum number of failures before stopping (0 = unlimited)
    pub max_failures: u32,
    /// Whether to include files with `_` prefix in discovery
    pub include_skipped: bool,
    /// Root directory for module resolution
    pub project_root: Option<&'a Path>,
    /// Color mode for output
    pub color: ColorMode,
    /// Use release optimizations
    pub release: bool,
}

/// Internal configuration for test execution, reducing argument count across functions.
struct TestRunConfig<'a> {
    /// Filter tests by name (substring match)
    filter: Option<&'a str>,
    /// Show verbose output (per-test results)
    verbose: bool,
    /// Root directory for module resolution
    project_root: Option<&'a Path>,
    /// Use release optimizations
    release: bool,
    /// Terminal color configuration
    colors: TermColors,
}

/// A thread-safe buffer for capturing stdout during test execution
#[derive(Clone)]
struct CaptureBuffer(Arc<Mutex<Vec<u8>>>);

impl CaptureBuffer {
    fn new() -> Self {
        CaptureBuffer(Arc::new(Mutex::new(Vec::new())))
    }

    fn take_string(&self) -> String {
        let bytes = std::mem::take(&mut *self.0.lock().unwrap());
        String::from_utf8_lossy(&bytes).into_owned()
    }
}

impl Write for CaptureBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// Status of an individual test
#[derive(Debug, Clone)]
pub enum TestStatus {
    Passed,
    Failed(Option<AssertFailure>),
    Panicked(String),
}

/// Result of running a single test
#[derive(Debug, Clone)]
pub struct TestResult {
    pub info: TestInfo,
    pub status: TestStatus,
    pub duration: Duration,
    /// File path where this test is defined
    pub file: PathBuf,
    /// Captured stdout from print/println during test execution
    pub captured_output: Option<String>,
}

/// A file that failed to compile, with the formatted error message
#[derive(Debug, Clone)]
pub struct FileError {
    pub file: PathBuf,
    pub error: String,
}

/// Aggregated results from running all tests
#[derive(Debug)]
pub struct TestResults {
    pub passed: usize,
    pub failed: usize,
    pub results: Vec<TestResult>,
    pub total_duration: Duration,
    /// Number of files that failed to compile (critical errors)
    pub file_errors: usize,
    /// Detailed information about files that failed to compile
    pub file_error_details: Vec<FileError>,
    /// Number of files skipped due to max_failures cap
    pub skipped_files: usize,
    /// Number of tests that didn't run (due to max-failures or file compile errors)
    pub not_run: usize,
}

impl TestResults {
    fn new() -> Self {
        TestResults {
            passed: 0,
            failed: 0,
            results: Vec::new(),
            total_duration: Duration::ZERO,
            file_errors: 0,
            file_error_details: Vec::new(),
            skipped_files: 0,
            not_run: 0,
        }
    }

    fn add(&mut self, result: TestResult) {
        match &result.status {
            TestStatus::Passed => self.passed += 1,
            TestStatus::Failed(_) | TestStatus::Panicked(_) => self.failed += 1,
        }
        self.results.push(result);
    }

    fn merge(&mut self, other: TestResults) {
        self.passed += other.passed;
        self.failed += other.failed;
        self.results.extend(other.results);
        self.total_duration += other.total_duration;
        self.file_errors += other.file_errors;
        self.file_error_details.extend(other.file_error_details);
        self.skipped_files += other.skipped_files;
        self.not_run += other.not_run;
    }

    fn add_file_error(&mut self, file: PathBuf, error: String) {
        self.file_errors += 1;
        self.file_error_details.push(FileError { file, error });
    }
}

/// Main entry point for the test command
/// Use "-" alone to read from stdin.
pub fn run_tests(paths: &[String], options: TestRunOptions) -> ExitCode {
    // Validate project root if provided
    if let Some(root) = options.project_root {
        if !root.exists() {
            eprintln!("error: --root path does not exist: {}", root.display());
            return ExitCode::FAILURE;
        }
        if !root.is_dir() {
            eprintln!("error: --root path is not a directory: {}", root.display());
            return ExitCode::FAILURE;
        }
    }

    let start = Instant::now();
    let config = TestRunConfig {
        filter: options.filter,
        verbose: options.verbose,
        project_root: options.project_root,
        release: options.release,
        colors: TermColors::with_mode(options.color),
    };

    // Handle stdin specially (must be alone)
    if paths.len() == 1 && paths[0] == "-" {
        return run_stdin_tests(&config, start);
    }

    // Collect all test files from the given paths
    let expanded = match expand_paths(paths) {
        Ok(files) => files,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::FAILURE;
        }
    };

    // Filter out underscore-prefixed files from DISCOVERED files only (not explicit paths).
    // Direct paths like `vole test _wip.vole` should always run.
    let (files, skipped_count): (Vec<_>, usize) = if options.include_skipped {
        (
            expanded
                .explicit
                .into_iter()
                .chain(expanded.discovered)
                .collect(),
            0,
        )
    } else {
        let mut skipped = 0;
        let discovered_filtered: Vec<_> = expanded
            .discovered
            .into_iter()
            .filter(|p| {
                if should_skip_path(p) {
                    skipped += 1;
                    false
                } else {
                    true
                }
            })
            .collect();
        // Explicit files are never filtered
        let mut all = expanded.explicit;
        all.extend(discovered_filtered);
        (all, skipped)
    };

    if files.is_empty() {
        if skipped_count > 0 {
            eprintln!(
                "error: no test files found ({} skipped with '_' prefix, use --include-skipped)",
                skipped_count
            );
        } else {
            eprintln!("error: no test files found");
        }
        return ExitCode::FAILURE;
    }

    // Run tests from each file
    let mut all_results = TestResults::new();
    let failure_cap = if options.max_failures == 0 {
        usize::MAX
    } else {
        options.max_failures as usize
    };

    // Create shared module cache for all test files (sema caching)
    let cache = Rc::new(RefCell::new(ModuleCache::new()));

    // Compiled modules cache (codegen caching) - populated on first file
    let mut compiled_modules: Option<CompiledModules> = None;

    for (idx, file) in files.iter().enumerate() {
        // Check if we've hit the failure cap
        if all_results.failed >= failure_cap {
            all_results.skipped_files = files.len() - idx;
            break;
        }

        // Print file path BEFORE processing for immediate feedback
        // (verbose mode shows per-test output)
        if config.verbose {
            println!("\n{}", file.display());
            let _ = io::stdout().flush();
        }

        // Set current file for signal handler
        set_current_file(&file.display().to_string());

        match run_file_tests_with_modules(file, &config, cache.clone(), &mut compiled_modules) {
            Ok(results) => {
                all_results.merge(results);
            }
            Err(e) => {
                // Store the error for later grouped display
                all_results.add_file_error(file.to_path_buf(), e);
            }
        }
    }

    all_results.total_duration = start.elapsed();

    // Print failure/error details (in both modes)
    if all_results.failed > 0 || all_results.file_errors > 0 {
        print_failures_summary(&all_results, &config.colors);
    }

    // Print summary
    print_summary(&all_results, &config.colors);

    if all_results.failed > 0 || all_results.file_errors > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Run tests from stdin
fn run_stdin_tests(config: &TestRunConfig, start: Instant) -> ExitCode {
    let source = match read_stdin() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read stdin: {}", e);
            return ExitCode::FAILURE;
        }
    };

    let stdin_path = PathBuf::from("<stdin>");
    let mut all_results = TestResults::new();

    // Create cache for stdin test (single file, but still useful for prelude)
    let cache = Rc::new(RefCell::new(ModuleCache::new()));

    // Print file path in verbose mode
    if config.verbose {
        println!("\n{}", stdin_path.display());
        let _ = io::stdout().flush();
    }

    match run_source_tests_with_progress(&source, "<stdin>", &stdin_path, config, cache) {
        Ok(results) => {
            all_results.merge(results);
        }
        Err(e) => {
            // Store the error for later grouped display
            all_results.add_file_error(stdin_path.clone(), e);
        }
    }

    all_results.total_duration = start.elapsed();

    // Print failure/error details (in both modes)
    if all_results.failed > 0 || all_results.file_errors > 0 {
        print_failures_summary(&all_results, &config.colors);
    }

    print_summary(&all_results, &config.colors);

    if all_results.failed > 0 || all_results.file_errors > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Parse, type check, compile, and run tests with shared compiled modules
fn run_file_tests_with_modules(
    path: &Path,
    config: &TestRunConfig,
    cache: Rc<RefCell<ModuleCache>>,
    compiled_modules: &mut Option<CompiledModules>,
) -> Result<TestResults, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("could not read file: {}", e))?;
    let file_path = path.to_string_lossy();
    run_source_tests_with_modules(&source, &file_path, path, config, cache, compiled_modules)
}

/// Parse, type check, compile, and run tests with shared compiled modules
fn run_source_tests_with_modules(
    source: &str,
    file_path: &str,
    path: &Path,
    config: &TestRunConfig,
    cache: Rc<RefCell<ModuleCache>>,
    compiled_modules: &mut Option<CompiledModules>,
) -> Result<TestResults, String> {
    // Parse and type check with shared cache, capturing errors
    let mut error_buffer = Vec::new();
    let analyzed = match compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: false,
            project_root: config.project_root,
            module_cache: Some(cache),
            run_mode: false,
        },
        &mut error_buffer,
    ) {
        Ok(a) => a,
        Err(_) => {
            let error_str = String::from_utf8_lossy(&error_buffer).into_owned();
            return Err(error_str);
        }
    };

    // Check if cached modules contain all modules needed by this file
    let can_use_cache = compiled_modules.as_ref().is_some_and(|modules| {
        analyzed
            .module_programs
            .keys()
            .all(|module_path| modules.has_module(module_path))
    });

    let options = if config.release {
        JitOptions::release()
    } else {
        JitOptions::debug()
    };

    let (jit, compile_result, tests) = if can_use_cache {
        let modules = compiled_modules.as_ref().unwrap();
        // Subsequent files: use pre-compiled modules
        let mut jit = JitContext::with_modules_and_options(modules, options);
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler.set_source_file(file_path);

        // Import module functions (fast - just declarations, no codegen)
        let _ = compiler.import_modules();

        // Compile just the main program
        let result = compiler.compile_program_only(&analyzed.program);

        let tests = compiler.take_tests();
        (jit, result, tests)
    } else {
        // First file: compile normally and cache modules for future files
        let mut jit = JitContext::with_options(options);
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler.set_source_file(file_path);

        // Compile modules (this is the expensive part)
        let modules_result = compiler.compile_modules_only();

        // Compile main program
        let result = if modules_result.is_ok() {
            compiler.compile_program_only(&analyzed.program)
        } else {
            modules_result
        };

        let tests = compiler.take_tests();

        // If successful, create a separate modules JIT for caching
        if result.is_ok() && !analyzed.module_programs.is_empty() {
            let mut modules_jit = JitContext::with_options(options);
            let compile_result = {
                let mut modules_compiler = Compiler::new(&mut modules_jit, &analyzed);
                modules_compiler.compile_modules_only()
            };
            match compile_result {
                Ok(()) => {
                    let module_paths: Vec<String> =
                        analyzed.module_programs.keys().cloned().collect();
                    match CompiledModules::new(modules_jit, module_paths) {
                        Ok(modules) => *compiled_modules = Some(modules),
                        Err(e) => {
                            tracing::warn!("Modules finalization failed: {}", e);
                        }
                    }
                }
                Err(e) => {
                    tracing::warn!("Modules compilation failed: {}", e);
                    std::mem::forget(modules_jit);
                }
            }
        }

        (jit, result, tests)
    };

    // Check compilation result
    if let Err(e) = compile_result {
        std::mem::forget(jit);
        return Err(format!("compilation error: {}", e));
    }

    // Finalize only on successful compilation
    let mut jit = jit;
    jit.finalize()?;

    // Filter tests if a filter is provided
    let tests = if let Some(pattern) = config.filter {
        tests
            .into_iter()
            .filter(|t| t.name.contains(pattern))
            .collect()
    } else {
        tests
    };

    // Execute tests with progress output
    let results = execute_tests_with_progress(tests, &jit, path, config);

    Ok(results)
}

/// Parse, type check, compile, and run tests with incremental progress output
fn run_source_tests_with_progress(
    source: &str,
    file_path: &str,
    path: &Path,
    config: &TestRunConfig,
    cache: Rc<RefCell<ModuleCache>>,
) -> Result<TestResults, String> {
    // Parse and type check with shared cache, capturing errors
    let mut error_buffer = Vec::new();
    let analyzed = match compile_source(
        PipelineOptions {
            source,
            file_path,
            skip_tests: false,
            project_root: config.project_root,
            module_cache: Some(cache),
            run_mode: false,
        },
        &mut error_buffer,
    ) {
        Ok(a) => a,
        Err(_) => {
            let error_str = String::from_utf8_lossy(&error_buffer).into_owned();
            return Err(error_str);
        }
    };

    // Compile
    let options = if config.release {
        JitOptions::release()
    } else {
        JitOptions::debug()
    };
    let mut jit = JitContext::with_options(options);
    let (compile_result, tests) = {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler.set_source_file(file_path);

        // Compile modules first (prelude functions)
        let modules_result = compiler.compile_modules_only();

        // Then compile just the main program
        let result = if modules_result.is_ok() {
            compiler.compile_program_only(&analyzed.program)
        } else {
            modules_result
        };

        let tests = compiler.take_tests();
        (result, tests)
    };

    // Check compilation result
    if let Err(e) = compile_result {
        // CRITICAL: On compilation error, leak the JIT module to prevent cleanup
        // Cranelift's Drop implementation can corrupt global state when dropping
        // a module with partial/broken function definitions
        std::mem::forget(jit);
        return Err(format!("compilation error: {}", e));
    }

    // Finalize only on successful compilation
    jit.finalize()?;

    // Filter tests if a filter is provided
    let tests = if let Some(pattern) = config.filter {
        tests
            .into_iter()
            .filter(|t| t.name.contains(pattern))
            .collect()
    } else {
        tests
    };

    // Execute tests with progress output
    let results = execute_tests_with_progress(tests, &jit, path, config);

    Ok(results)
}

/// Execute compiled tests with incremental progress output
fn execute_tests_with_progress(
    tests: Vec<TestInfo>,
    jit: &JitContext,
    file: &Path,
    config: &TestRunConfig,
) -> TestResults {
    let mut results = TestResults::new();
    let start = Instant::now();
    let file_path = file.to_path_buf();

    for test in tests {
        let func_ptr = match jit.get_function_ptr_by_id(test.func_id) {
            Some(ptr) => ptr,
            None => {
                // Print failure immediately in verbose mode
                if config.verbose {
                    println!(
                        "  {}\u{2718}{} {} - could not find test function",
                        config.colors.red(),
                        config.colors.reset(),
                        test.name,
                    );
                    let _ = io::stdout().flush();
                }
                results.add(TestResult {
                    info: test,
                    status: TestStatus::Failed(None),
                    duration: Duration::ZERO,
                    file: file_path.clone(),
                    captured_output: None,
                });
                continue;
            }
        };

        // Test functions have signature () -> i64
        let test_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(func_ptr) };

        // Set current test for signal handler
        set_current_test(&test.name);

        let test_start = Instant::now();

        // Set up stdout capture for this test
        let capture_buffer = CaptureBuffer::new();
        set_stdout_capture(Some(Box::new(capture_buffer.clone())));

        // Set up jump buffer for assertion failure recovery
        let mut jmp_buf: JmpBuf = JmpBuf::zeroed();
        set_test_jmp_buf(&mut jmp_buf);

        // Wrap test execution in catch_unwind to catch panics
        let panic_result = catch_unwind(AssertUnwindSafe(|| unsafe {
            if call_setjmp(&mut jmp_buf) == 0 {
                // Normal execution path
                test_fn();
                TestStatus::Passed
            } else {
                // Returned via longjmp from assertion failure
                TestStatus::Failed(take_assert_failure())
            }
        }));

        clear_test_jmp_buf();
        clear_current_test();

        // Stop capturing and get the output
        set_stdout_capture(None);
        let captured_output = capture_buffer.take_string();
        let captured_output = if captured_output.is_empty() {
            None
        } else {
            Some(captured_output)
        };

        let status = match panic_result {
            Ok(status) => status,
            Err(panic_info) => {
                // Extract panic message
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                TestStatus::Panicked(msg)
            }
        };

        let duration = test_start.elapsed();
        let duration_str = format_duration(duration);

        // Print result immediately after test completes in verbose mode
        if config.verbose {
            match &status {
                TestStatus::Passed => {
                    println!(
                        "  {}\u{2022}{} {} {}({}){}",
                        config.colors.green(),
                        config.colors.reset(),
                        test.name,
                        config.colors.dim(),
                        duration_str,
                        config.colors.reset()
                    );
                    let _ = io::stdout().flush();
                }
                TestStatus::Failed(failure) => {
                    print!(
                        "  {}\u{2718}{} {} {}({}){}",
                        config.colors.red(),
                        config.colors.reset(),
                        test.name,
                        config.colors.dim(),
                        duration_str,
                        config.colors.reset()
                    );
                    if let Some(info) = failure {
                        println!(" - assertion failed at {}:{}", info.file, info.line);
                    } else {
                        println!();
                    }
                    // Print captured output on failure
                    if let Some(output) = &captured_output {
                        println!(
                            "    {}--- captured output ---{}",
                            config.colors.dim(),
                            config.colors.reset()
                        );
                        for line in output.lines() {
                            println!("    {}", line);
                        }
                    }
                    let _ = io::stdout().flush();
                }
                TestStatus::Panicked(msg) => {
                    println!(
                        "  {}\u{2620}{} {} {}({}){}",
                        config.colors.red(),
                        config.colors.reset(),
                        test.name,
                        config.colors.dim(),
                        duration_str,
                        config.colors.reset()
                    );
                    eprintln!("    PANIC: {}", msg);
                    // Print captured output on panic
                    if let Some(output) = &captured_output {
                        println!(
                            "    {}--- captured output ---{}",
                            config.colors.dim(),
                            config.colors.reset()
                        );
                        for line in output.lines() {
                            println!("    {}", line);
                        }
                    }
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                }
            }
        }

        results.add(TestResult {
            info: test.clone(),
            status,
            duration,
            file: file_path.clone(),
            captured_output,
        });
    }

    results.total_duration = start.elapsed();
    results
}

/// Print detailed failure information grouped by file
fn print_failures_summary(results: &TestResults, colors: &TermColors) {
    // Print FAILURES section if there are any test failures
    let has_failures = results
        .results
        .iter()
        .any(|r| matches!(r.status, TestStatus::Failed(_) | TestStatus::Panicked(_)));

    if has_failures {
        println!(
            "\n{}FAILURES {}────────────────────────────────────{}",
            colors.red(),
            colors.reset(),
            colors.reset()
        );
        print_failure_details(results, colors);
    }

    // Print ERRORS section if there are any file compile errors
    if !results.file_error_details.is_empty() {
        println!(
            "\n{}ERRORS {}──────────────────────────────────────{}",
            colors.yellow(),
            colors.reset(),
            colors.reset()
        );
        print_error_details(results, colors);
    }
}

/// Print individual failure details grouped by file
fn print_failure_details(results: &TestResults, colors: &TermColors) {
    let mut current_file: Option<&Path> = None;

    for result in &results.results {
        match &result.status {
            TestStatus::Failed(_) => {
                // Print file header if changed
                if current_file != Some(result.file.as_path()) {
                    println!("{}", result.file.display());
                    current_file = Some(result.file.as_path());
                }

                // Print failure line: ✘ test_name · file:line
                println!(
                    "  {}\u{2718}{} {} {}· {}:{}{}",
                    colors.red(),
                    colors.reset(),
                    result.info.name,
                    colors.dim(),
                    result.info.file,
                    result.info.line,
                    colors.reset()
                );

                // Print message line
                println!("    assertion failed");

                // Print captured output if present
                print_captured_output(&result.captured_output, colors);
            }
            TestStatus::Panicked(msg) => {
                // Print file header if changed
                if current_file != Some(result.file.as_path()) {
                    println!("{}", result.file.display());
                    current_file = Some(result.file.as_path());
                }

                // Print failure line: ✘ test_name · file:line
                println!(
                    "  {}\u{2718}{} {} {}· {}:{}{}",
                    colors.red(),
                    colors.reset(),
                    result.info.name,
                    colors.dim(),
                    result.info.file,
                    result.info.line,
                    colors.reset()
                );

                // Print panic message
                println!("    panicked: {}", msg);

                // Print captured output if present
                print_captured_output(&result.captured_output, colors);
            }
            TestStatus::Passed => {}
        }
    }
}

/// Print captured output with │ gutter
fn print_captured_output(output: &Option<String>, colors: &TermColors) {
    if let Some(output) = output.as_ref().filter(|s| !s.is_empty()) {
        println!("    {}Output:{}", colors.dim(), colors.reset());
        for line in output.lines() {
            println!("    {}\u{2502}{} {}", colors.dim(), colors.reset(), line);
        }
    }
}

/// Print file compile error details
fn print_error_details(results: &TestResults, colors: &TermColors) {
    for file_error in &results.file_error_details {
        println!(
            "{}{}{}",
            colors.yellow(),
            file_error.file.display(),
            colors.reset()
        );
        // The error is already formatted by miette, just print it indented
        for line in file_error.error.lines() {
            println!("  {}", line);
        }
    }
}

/// Print overall test summary
fn print_summary(results: &TestResults, colors: &TermColors) {
    let duration = format_duration(results.total_duration);

    println!();

    // Show file errors first - these are critical and should not be ignored
    if results.file_errors > 0 {
        println!(
            "{}Files: {} error{}{} (tests in these files did not run)",
            colors.red(),
            results.file_errors,
            if results.file_errors == 1 { "" } else { "s" },
            colors.reset()
        );
    }

    // Show test results
    if results.failed == 0 && results.file_errors == 0 {
        println!(
            "{}Tests: {} passed{} {}({}){}",
            colors.green(),
            results.passed,
            colors.reset(),
            colors.dim(),
            duration,
            colors.reset()
        );
    } else if results.failed == 0 {
        println!(
            "Tests: {}{} passed{} {}({}){}",
            colors.green(),
            results.passed,
            colors.reset(),
            colors.dim(),
            duration,
            colors.reset()
        );
    } else {
        println!(
            "Tests: {}{} failed{}, {}{} passed{} {}({}){}",
            colors.red(),
            results.failed,
            colors.reset(),
            colors.green(),
            results.passed,
            colors.reset(),
            colors.dim(),
            duration,
            colors.reset()
        );
    }

    // Show skipped files if failure cap was hit
    if results.skipped_files > 0 {
        println!(
            "{}{} file{} skipped{} (max failures reached)",
            colors.dim(),
            results.skipped_files,
            if results.skipped_files == 1 { "" } else { "s" },
            colors.reset()
        );
    }
}
