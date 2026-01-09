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
use std::time::{Duration, Instant};

use super::common::{TermColors, parse_and_analyze, read_stdin};
use crate::cli::{ColorMode, ReportMode, expand_paths};
use crate::codegen::{Compiler, JitContext, TestInfo};
use crate::runtime::{
    AssertFailure, JmpBuf, call_setjmp, clear_current_test, clear_test_jmp_buf, set_current_file,
    set_current_test, set_test_jmp_buf, take_assert_failure,
};
use crate::util::format_duration;

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
}

/// Aggregated results from running all tests
#[derive(Debug)]
pub struct TestResults {
    pub passed: usize,
    pub failed: usize,
    pub results: Vec<TestResult>,
    pub total_duration: Duration,
    /// Number of files skipped due to max_failures cap
    pub skipped_files: usize,
}

impl TestResults {
    fn new() -> Self {
        TestResults {
            passed: 0,
            failed: 0,
            results: Vec::new(),
            total_duration: Duration::ZERO,
            skipped_files: 0,
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
        self.skipped_files += other.skipped_files;
    }
}

/// Main entry point for the test command
/// Use "-" alone to read from stdin.
pub fn run_tests(
    paths: &[String],
    filter: Option<&str>,
    report: ReportMode,
    max_failures: u32,
    color: ColorMode,
) -> ExitCode {
    let start = Instant::now();
    let colors = TermColors::with_mode(color);

    // Handle stdin specially (must be alone)
    if paths.len() == 1 && paths[0] == "-" {
        return run_stdin_tests(filter, &report, &colors, start);
    }

    // Collect all test files from the given paths
    let files = match expand_paths(paths) {
        Ok(files) => files,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::FAILURE;
        }
    };

    if files.is_empty() {
        eprintln!("error: no test files found");
        return ExitCode::FAILURE;
    }

    // Run tests from each file
    let mut all_results = TestResults::new();
    let failure_cap = if max_failures == 0 {
        usize::MAX
    } else {
        max_failures as usize
    };

    for (idx, file) in files.iter().enumerate() {
        // Check if we've hit the failure cap
        if all_results.failed >= failure_cap {
            all_results.skipped_files = files.len() - idx;
            break;
        }

        // Print file path BEFORE processing for immediate feedback
        if !matches!(report, ReportMode::Results) {
            println!("\n{}", file.display());
            let _ = io::stdout().flush();
        }

        // Set current file for signal handler
        set_current_file(&file.display().to_string());

        match run_file_tests_with_progress(file, filter, &colors, &report) {
            Ok(results) => {
                all_results.merge(results);
            }
            Err(e) => {
                // Empty error means diagnostics were already rendered
                if !e.is_empty() {
                    eprintln!("  error: {}", e);
                }
                all_results.failed += 1;
            }
        }
    }

    all_results.total_duration = start.elapsed();

    // For 'all' mode, reprint failures at the end
    if matches!(report, ReportMode::All) && all_results.failed > 0 {
        print_failures_summary(&all_results, &colors);
    }

    // Print summary
    print_summary(&all_results, &colors);

    if all_results.failed > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Run tests from stdin
fn run_stdin_tests(
    filter: Option<&str>,
    report: &ReportMode,
    colors: &TermColors,
    start: Instant,
) -> ExitCode {
    let source = match read_stdin() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read stdin: {}", e);
            return ExitCode::FAILURE;
        }
    };

    let stdin_path = PathBuf::from("<stdin>");
    let mut all_results = TestResults::new();

    // Print file path BEFORE processing
    if !matches!(report, ReportMode::Results) {
        println!("\n{}", stdin_path.display());
        let _ = io::stdout().flush();
    }

    match run_source_tests_with_progress(&source, "<stdin>", &stdin_path, filter, colors, report) {
        Ok(results) => {
            all_results.merge(results);
        }
        Err(e) => {
            if !e.is_empty() {
                eprintln!("  error: {}", e);
            }
            all_results.failed += 1;
        }
    }

    all_results.total_duration = start.elapsed();

    // For 'all' mode, reprint failures at the end
    if matches!(report, ReportMode::All) && all_results.failed > 0 {
        print_failures_summary(&all_results, colors);
    }

    print_summary(&all_results, colors);

    if all_results.failed > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Parse, type check, compile, and run tests with incremental progress output
fn run_file_tests_with_progress(
    path: &Path,
    filter: Option<&str>,
    colors: &TermColors,
    report: &ReportMode,
) -> Result<TestResults, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("could not read file: {}", e))?;
    let file_path = path.to_string_lossy();
    run_source_tests_with_progress(&source, &file_path, path, filter, colors, report)
}

/// Parse, type check, compile, and run tests with incremental progress output
fn run_source_tests_with_progress(
    source: &str,
    file_path: &str,
    path: &Path,
    filter: Option<&str>,
    colors: &TermColors,
    report: &ReportMode,
) -> Result<TestResults, String> {
    // Parse and type check
    let analyzed = parse_and_analyze(source, file_path).map_err(|()| String::new())?;

    // Compile
    let mut jit = JitContext::new();
    let (compile_result, tests) = {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler.set_source_file(file_path);
        let result = compiler.compile_program(&analyzed.program);
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
    let _ = jit.finalize();

    // Filter tests if a filter is provided
    let tests = if let Some(pattern) = filter {
        tests
            .into_iter()
            .filter(|t| t.name.contains(pattern))
            .collect()
    } else {
        tests
    };

    // Execute tests with progress output
    let results = execute_tests_with_progress(tests, &jit, path, colors, report);

    Ok(results)
}

/// Execute compiled tests with incremental progress output
fn execute_tests_with_progress(
    tests: Vec<TestInfo>,
    jit: &JitContext,
    file: &Path,
    colors: &TermColors,
    report: &ReportMode,
) -> TestResults {
    let mut results = TestResults::new();
    let start = Instant::now();
    let file_path = file.to_path_buf();

    for test in tests {
        let func_ptr = match jit.get_function_ptr_by_id(test.func_id) {
            Some(ptr) => ptr,
            None => {
                // Print failure immediately
                if !matches!(report, ReportMode::Results) {
                    println!(
                        "  {}\u{2717}{} {} - could not find test function",
                        colors.red(),
                        colors.reset(),
                        test.name,
                    );
                    let _ = io::stdout().flush();
                }
                results.add(TestResult {
                    info: test,
                    status: TestStatus::Failed(None),
                    duration: Duration::ZERO,
                    file: file_path.clone(),
                });
                continue;
            }
        };

        // Test functions have signature () -> i64
        let test_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(func_ptr) };

        // Set current test for signal handler
        set_current_test(&test.name);

        let test_start = Instant::now();

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

        // Print result immediately after test completes
        if !matches!(report, ReportMode::Results) {
            match &status {
                TestStatus::Passed => {
                    if !matches!(report, ReportMode::Failures) {
                        println!(
                            "  {}\u{2713}{} {} {}({}){}",
                            colors.green(),
                            colors.reset(),
                            test.name,
                            colors.dim(),
                            duration_str,
                            colors.reset()
                        );
                        let _ = io::stdout().flush();
                    }
                }
                TestStatus::Failed(failure) => {
                    print!(
                        "  {}\u{2717}{} {} {}({}){}",
                        colors.red(),
                        colors.reset(),
                        test.name,
                        colors.dim(),
                        duration_str,
                        colors.reset()
                    );
                    if let Some(info) = failure {
                        println!(" - assertion failed at {}:{}", info.file, info.line);
                    } else {
                        println!();
                    }
                    let _ = io::stdout().flush();
                }
                TestStatus::Panicked(msg) => {
                    println!(
                        "  {}\u{2620}{} {} {}({}){}",
                        colors.red(),
                        colors.reset(),
                        test.name,
                        colors.dim(),
                        duration_str,
                        colors.reset()
                    );
                    eprintln!("    PANIC: {}", msg);
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
        });
    }

    results.total_duration = start.elapsed();
    results
}

/// Print a single test result
fn print_test_result(result: &TestResult, colors: &TermColors) {
    let duration = format_duration(result.duration);

    match &result.status {
        TestStatus::Passed => {
            println!(
                "  {}\u{2713}{} {} {}({}){}",
                colors.green(),
                colors.reset(),
                result.info.name,
                colors.dim(),
                duration,
                colors.reset()
            );
        }
        TestStatus::Failed(failure) => {
            print!(
                "  {}\u{2717}{} {} {}({}){}",
                colors.red(),
                colors.reset(),
                result.info.name,
                colors.dim(),
                duration,
                colors.reset()
            );
            if let Some(info) = failure {
                println!(" - assertion failed at {}:{}", info.file, info.line);
            } else {
                println!();
            }
        }
        TestStatus::Panicked(msg) => {
            println!(
                "  {}\u{2620}{} {} {}({}){}",
                colors.red(),
                colors.reset(),
                result.info.name,
                colors.dim(),
                duration,
                colors.reset()
            );
            eprintln!("    PANIC: {}", msg);
        }
    }
}

/// Print a summary of all failures at the end (for 'all' mode)
fn print_failures_summary(results: &TestResults, colors: &TermColors) {
    println!("\n{}Failures:{}", colors.red(), colors.reset());

    // Group failures by file
    let mut current_file: Option<&Path> = None;

    for result in &results.results {
        if matches!(
            result.status,
            TestStatus::Failed(_) | TestStatus::Panicked(_)
        ) {
            // Print file header if changed
            if current_file != Some(result.file.as_path()) {
                println!("\n{}", result.file.display());
                current_file = Some(result.file.as_path());
            }

            print_test_result(result, colors);
        }
    }
}

/// Print overall test summary
fn print_summary(results: &TestResults, colors: &TermColors) {
    let total = results.passed + results.failed;
    let duration = format_duration(results.total_duration);

    println!();
    if results.failed == 0 {
        println!(
            "{}{} test{} passed{} {}({}){}",
            colors.green(),
            total,
            if total == 1 { "" } else { "s" },
            colors.reset(),
            colors.dim(),
            duration,
            colors.reset()
        );
    } else {
        println!(
            "{}{} failed{}, {}{} passed{} {}({}){}",
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
