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

use super::common::{TermColors, parse_and_analyze, read_stdin};
use crate::cli::{ColorMode, ReportMode, expand_paths, should_skip_path};
use crate::codegen::{Compiler, JitContext, TestInfo};
use crate::runtime::{
    AssertFailure, JmpBuf, call_setjmp, clear_current_test, clear_test_jmp_buf, set_current_file,
    set_current_test, set_stdout_capture, set_test_jmp_buf, take_assert_failure,
};
use crate::util::format_duration;

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

/// Aggregated results from running all tests
#[derive(Debug)]
pub struct TestResults {
    pub passed: usize,
    pub failed: usize,
    pub results: Vec<TestResult>,
    pub total_duration: Duration,
    /// Number of files that failed to compile (critical errors)
    pub file_errors: usize,
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
            file_errors: 0,
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
        self.file_errors += other.file_errors;
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
    include_skipped: bool,
    color: ColorMode,
) -> ExitCode {
    let start = Instant::now();
    let colors = TermColors::with_mode(color);

    // Handle stdin specially (must be alone)
    if paths.len() == 1 && paths[0] == "-" {
        return run_stdin_tests(filter, &report, &colors, start);
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
    let (files, skipped_count): (Vec<_>, usize) = if include_skipped {
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
        // (only in 'all' mode - failures/results modes show less output)
        if matches!(report, ReportMode::All) {
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
                all_results.file_errors += 1;
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

    if all_results.failed > 0 || all_results.file_errors > 0 {
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

    // Print file path only in 'all' mode
    if matches!(report, ReportMode::All) {
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
            all_results.file_errors += 1;
        }
    }

    all_results.total_duration = start.elapsed();

    // For 'all' mode, reprint failures at the end
    if matches!(report, ReportMode::All) && all_results.failed > 0 {
        print_failures_summary(&all_results, colors);
    }

    print_summary(&all_results, colors);

    if all_results.failed > 0 || all_results.file_errors > 0 {
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
                    // In failures mode, print file path before failure
                    if matches!(report, ReportMode::Failures) {
                        println!("\n{}", file_path.display());
                    }
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
                    // In failures mode, print file path before failure
                    if matches!(report, ReportMode::Failures) {
                        println!("\n{}", file_path.display());
                    }
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
                    // Print captured output on failure
                    if let Some(output) = &captured_output {
                        println!(
                            "    {}--- captured output ---{}",
                            colors.dim(),
                            colors.reset()
                        );
                        for line in output.lines() {
                            println!("    {}", line);
                        }
                    }
                    let _ = io::stdout().flush();
                }
                TestStatus::Panicked(msg) => {
                    // In failures mode, print file path before failure
                    if matches!(report, ReportMode::Failures) {
                        println!("\n{}", file_path.display());
                    }
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
                    // Print captured output on panic
                    if let Some(output) = &captured_output {
                        println!(
                            "    {}--- captured output ---{}",
                            colors.dim(),
                            colors.reset()
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
            // Print captured output on failure
            if let Some(output) = &result.captured_output {
                println!(
                    "    {}--- captured output ---{}",
                    colors.dim(),
                    colors.reset()
                );
                for line in output.lines() {
                    println!("    {}", line);
                }
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
            // Print captured output on panic
            if let Some(output) = &result.captured_output {
                println!(
                    "    {}--- captured output ---{}",
                    colors.dim(),
                    colors.reset()
                );
                for line in output.lines() {
                    println!("    {}", line);
                }
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
