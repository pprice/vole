// src/commands/test.rs
//
// Test runner command for the Vole compiler.
// Discovers and executes tests from Vole source files.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use glob::glob;

use crate::codegen::{Compiler, JitContext, TestInfo};
use crate::frontend::Parser;
use crate::runtime::{call_setjmp, clear_test_jmp_buf, set_test_jmp_buf, take_assert_failure, AssertFailure, JmpBuf};
use crate::sema::Analyzer;

/// Status of an individual test
#[derive(Debug, Clone)]
pub enum TestStatus {
    Passed,
    Failed(Option<AssertFailure>),
}

/// Result of running a single test
#[derive(Debug)]
pub struct TestResult {
    pub info: TestInfo,
    pub status: TestStatus,
    pub duration: Duration,
}

/// Aggregated results from running all tests
#[derive(Debug)]
pub struct TestResults {
    pub passed: usize,
    pub failed: usize,
    pub results: Vec<TestResult>,
    pub total_duration: Duration,
}

impl TestResults {
    fn new() -> Self {
        TestResults {
            passed: 0,
            failed: 0,
            results: Vec::new(),
            total_duration: Duration::ZERO,
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
    }
}

/// Main entry point for the test command
pub fn run_tests(paths: &[String]) -> ExitCode {
    let start = Instant::now();

    // Collect all test files from the given paths
    let files = match collect_test_files(paths) {
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

    for file in &files {
        match run_file_tests(file) {
            Ok(results) => {
                print_file_results(file, &results);
                all_results.merge(results);
            }
            Err(e) => {
                eprintln!("\n{}: error: {}", file.display(), e);
                all_results.failed += 1;
            }
        }
    }

    all_results.total_duration = start.elapsed();

    // Print summary
    print_summary(&all_results);

    if all_results.failed > 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Collect all .vole files from the given paths (files, directories, or glob patterns)
fn collect_test_files(paths: &[String]) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();

    for path_str in paths {
        let path = Path::new(path_str);

        if path.is_file() {
            // Direct file path
            if path.extension().is_some_and(|ext| ext == "vole") {
                files.push(path.to_path_buf());
            } else {
                return Err(format!("'{}' is not a .vole file", path_str));
            }
        } else if path.is_dir() {
            // Directory - find all .vole files recursively
            let pattern = format!("{}/**/*.vole", path_str);
            collect_glob_matches(&pattern, &mut files)?;
        } else {
            // Treat as glob pattern
            collect_glob_matches(path_str, &mut files)?;
        }
    }

    // Sort for deterministic ordering
    files.sort();
    files.dedup();

    Ok(files)
}

/// Expand a glob pattern and add matching files
fn collect_glob_matches(pattern: &str, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = glob(pattern)
        .map_err(|e| format!("invalid glob pattern '{}': {}", pattern, e))?;

    for entry in entries {
        match entry {
            Ok(path) => {
                if path.is_file() && path.extension().is_some_and(|ext| ext == "vole") {
                    files.push(path);
                }
            }
            Err(e) => {
                return Err(format!("error reading path: {}", e));
            }
        }
    }

    Ok(())
}

/// Parse, type check, compile, and run tests from a single file
fn run_file_tests(path: &Path) -> Result<TestResults, String> {
    // Read source file
    let source = fs::read_to_string(path)
        .map_err(|e| format!("could not read file: {}", e))?;

    // Parse
    let mut parser = Parser::new(&source);
    let program = parser.parse_program()
        .map_err(|e| format!("parse error at {:?}: {}", e.span, e.message))?;
    let interner = parser.into_interner();

    // Type check
    let mut analyzer = Analyzer::new();
    analyzer.analyze(&program, &interner)
        .map_err(|errors| {
            let msgs: Vec<String> = errors.iter()
                .map(|e| format!("  {:?}: {}", e.span, e.message))
                .collect();
            format!("type errors:\n{}", msgs.join("\n"))
        })?;

    // Compile
    let mut jit = JitContext::new();
    let tests = {
        let mut compiler = Compiler::new(&mut jit, &interner);
        compiler.set_source_file(&path.to_string_lossy());
        compiler.compile_program(&program)
            .map_err(|e| format!("compilation error: {}", e))?;
        compiler.take_tests()
    };
    jit.finalize();

    // Execute tests
    let results = execute_tests(tests, &jit);

    Ok(results)
}

/// Execute compiled tests with setjmp/longjmp for assertion failure handling
fn execute_tests(tests: Vec<TestInfo>, jit: &JitContext) -> TestResults {
    let mut results = TestResults::new();
    let start = Instant::now();

    for test in tests {
        let func_ptr = match jit.get_function_ptr(&test.func_name) {
            Some(ptr) => ptr,
            None => {
                results.add(TestResult {
                    info: test,
                    status: TestStatus::Failed(None),
                    duration: Duration::ZERO,
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
        });
    }

    results.total_duration = start.elapsed();
    results
}

/// Print results for tests from a single file
fn print_file_results(path: &Path, results: &TestResults) {
    if results.results.is_empty() {
        return;
    }

    println!("\n{}", path.display());

    for result in &results.results {
        let duration_ms = result.duration.as_secs_f64() * 1000.0;

        match &result.status {
            TestStatus::Passed => {
                println!(
                    "  \x1b[32m\u{2713}\x1b[0m {} \x1b[90m({:.2}ms)\x1b[0m",
                    result.info.name,
                    duration_ms
                );
            }
            TestStatus::Failed(failure) => {
                print!(
                    "  \x1b[31m\u{2717}\x1b[0m {} \x1b[90m({:.2}ms)\x1b[0m",
                    result.info.name,
                    duration_ms
                );
                if let Some(info) = failure {
                    println!(" - assertion failed at {}:{}", info.file, info.line);
                } else {
                    println!();
                }
            }
        }
    }
}

/// Print overall test summary
fn print_summary(results: &TestResults) {
    let total = results.passed + results.failed;
    let duration_ms = results.total_duration.as_secs_f64() * 1000.0;

    println!();
    if results.failed == 0 {
        println!(
            "\x1b[32m{} test{} passed\x1b[0m \x1b[90m({:.2}ms)\x1b[0m",
            total,
            if total == 1 { "" } else { "s" },
            duration_ms
        );
    } else {
        println!(
            "\x1b[31m{} failed\x1b[0m, \x1b[32m{} passed\x1b[0m \x1b[90m({:.2}ms)\x1b[0m",
            results.failed,
            results.passed,
            duration_ms
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    fn create_test_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        let mut file = File::create(&path).unwrap();
        file.write_all(content.as_bytes()).unwrap();
        path
    }

    #[test]
    fn test_collect_single_file() {
        let dir = TempDir::new().unwrap();
        let file = create_test_file(dir.path(), "test.vole", "fn main() {}");

        let files = collect_test_files(&[file.to_string_lossy().to_string()]).unwrap();
        assert_eq!(files.len(), 1);
        assert_eq!(files[0], file);
    }

    #[test]
    fn test_collect_directory() {
        let dir = TempDir::new().unwrap();
        create_test_file(dir.path(), "a.vole", "fn main() {}");
        create_test_file(dir.path(), "b.vole", "fn main() {}");
        create_test_file(dir.path(), "c.txt", "not a vole file");

        let files = collect_test_files(&[dir.path().to_string_lossy().to_string()]).unwrap();
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_collect_rejects_non_vole() {
        let dir = TempDir::new().unwrap();
        let file = create_test_file(dir.path(), "test.txt", "not vole");

        let result = collect_test_files(&[file.to_string_lossy().to_string()]);
        assert!(result.is_err());
    }
}
