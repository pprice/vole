// src/commands/test.rs
//
// Test runner command for the Vole compiler.
// Discovers and executes tests from Vole source files.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use super::common::{TermColors, parse_and_analyze, read_stdin};
use crate::cli::{ColorMode, ReportMode, expand_paths};
use crate::codegen::{Compiler, JitContext, TestInfo};
use crate::runtime::{
    AssertFailure, JmpBuf, call_setjmp, clear_test_jmp_buf, set_test_jmp_buf, take_assert_failure,
};
use crate::util::format_duration;

/// Status of an individual test
#[derive(Debug, Clone)]
pub enum TestStatus {
    Passed,
    Failed(Option<AssertFailure>),
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
            TestStatus::Failed(_) => self.failed += 1,
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

        match run_file_tests(file, filter) {
            Ok(results) => {
                print_file_results(file, &results, &colors, &report);
                all_results.merge(results);
            }
            Err(e) => {
                // Empty error means diagnostics were already rendered
                if !e.is_empty() {
                    eprintln!("\n{}: error: {}", file.display(), e);
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

    match run_source_tests(&source, "<stdin>", &stdin_path, filter) {
        Ok(results) => {
            print_file_results(&stdin_path, &results, colors, report);
            all_results.merge(results);
        }
        Err(e) => {
            if !e.is_empty() {
                eprintln!("error: {}", e);
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

/// Parse, type check, compile, and run tests from a single file
fn run_file_tests(path: &Path, filter: Option<&str>) -> Result<TestResults, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("could not read file: {}", e))?;
    let file_path = path.to_string_lossy();
    run_source_tests(&source, &file_path, path, filter)
}

/// Parse, type check, compile, and run tests from source code
fn run_source_tests(
    source: &str,
    file_path: &str,
    path: &Path,
    filter: Option<&str>,
) -> Result<TestResults, String> {
    // Parse and type check
    let analyzed = parse_and_analyze(source, file_path).map_err(|()| String::new())?;

    // Compile
    let mut jit = JitContext::new();
    let tests = {
        let mut compiler = Compiler::new(
            &mut jit,
            &analyzed.interner,
            analyzed.type_aliases.clone(),
            analyzed.expr_types.clone(),
            analyzed.method_resolutions.clone(),
            analyzed.interface_registry.clone(),
            analyzed.type_implements.clone(),
            analyzed.error_types.clone(),
            analyzed.module_programs.clone(),
        );
        compiler.set_source_file(file_path);
        compiler
            .compile_program(&analyzed.program)
            .map_err(|e| format!("compilation error: {}", e))?;
        compiler.take_tests()
    };
    jit.finalize();

    // Filter tests if a filter is provided
    let tests = if let Some(pattern) = filter {
        tests
            .into_iter()
            .filter(|t| t.name.contains(pattern))
            .collect()
    } else {
        tests
    };

    // Execute tests
    let results = execute_tests(tests, &jit, path);

    Ok(results)
}

/// Execute compiled tests with setjmp/longjmp for assertion failure handling
fn execute_tests(tests: Vec<TestInfo>, jit: &JitContext, file: &Path) -> TestResults {
    let mut results = TestResults::new();
    let start = Instant::now();
    let file_path = file.to_path_buf();

    for test in tests {
        let func_ptr = match jit.get_function_ptr(&test.func_name) {
            Some(ptr) => ptr,
            None => {
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

        let test_start = Instant::now();

        // Set up jump buffer for assertion failure recovery
        let mut jmp_buf: JmpBuf = JmpBuf::zeroed();
        set_test_jmp_buf(&mut jmp_buf);

        let status = unsafe {
            if call_setjmp(&mut jmp_buf) == 0 {
                // Normal execution path
                test_fn();
                TestStatus::Passed
            } else {
                // Returned via longjmp from assertion failure
                TestStatus::Failed(take_assert_failure())
            }
        };

        clear_test_jmp_buf();

        let duration = test_start.elapsed();

        results.add(TestResult {
            info: test,
            status,
            duration,
            file: file_path.clone(),
        });
    }

    results.total_duration = start.elapsed();
    results
}

/// Print results for tests from a single file
fn print_file_results(
    path: &Path,
    results: &TestResults,
    colors: &TermColors,
    report: &ReportMode,
) {
    if results.results.is_empty() {
        return;
    }

    // In results mode, don't print individual tests
    if matches!(report, ReportMode::Results) {
        return;
    }

    // Check if we should print this file's header
    let has_relevant_results = match report {
        ReportMode::All => true,
        ReportMode::Failures => results.failed > 0,
        ReportMode::Results => false,
    };

    if !has_relevant_results {
        return;
    }

    println!("\n{}", path.display());

    for result in &results.results {
        // In failures mode, skip passed tests
        if matches!(report, ReportMode::Failures) && matches!(result.status, TestStatus::Passed) {
            continue;
        }

        print_test_result(result, colors);
    }
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
    }
}

/// Print a summary of all failures at the end (for 'all' mode)
fn print_failures_summary(results: &TestResults, colors: &TermColors) {
    println!("\n{}Failures:{}", colors.red(), colors.reset());

    // Group failures by file
    let mut current_file: Option<&Path> = None;

    for result in &results.results {
        if matches!(result.status, TestStatus::Failed(_)) {
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
