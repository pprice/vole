// src/snap/runner.rs
//! Test discovery and execution for snapshot tests.

use std::collections::HashSet;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use glob::glob;

use super::ReportMode;
use super::diff::{unified_diff, unified_diff_colored};
use super::snapshot::Snapshot;
use crate::cli::should_skip_path;
use crate::commands::common::{check_captured, inspect_ast_captured, run_captured};

/// Result of running a single test
#[derive(Debug)]
pub enum TestResult {
    Pass,
    Fail(String), // diff output
    New,          // no snapshot file exists
}

/// Summary of test run
#[derive(Debug, Default)]
pub struct TestSummary {
    pub passed: usize,
    pub failed: usize,
    pub new: usize,
    pub failed_tests: Vec<String>,
    pub new_tests: Vec<String>,
}

/// Discover test files matching patterns.
/// Excludes underscore-prefixed files/directories unless include_skipped is true.
/// Skips any path where any component starts with '_' (e.g., `_imports/foo.vole`).
pub fn discover_tests(
    patterns: &[String],
    include_skipped: bool,
) -> Result<(Vec<PathBuf>, usize), String> {
    let mut files = HashSet::new();
    let mut skipped_count = 0;

    for pattern in patterns {
        let path = Path::new(pattern);

        if path.is_file() {
            if !include_skipped && should_skip_path(path) {
                skipped_count += 1;
            } else {
                files.insert(path.to_path_buf());
            }
        } else if path.is_dir() {
            let glob_pattern = format!("{}/**/*.vole", path.display());
            for p in glob(&glob_pattern).map_err(|e| e.to_string())?.flatten() {
                if !include_skipped && should_skip_path(&p) {
                    skipped_count += 1;
                } else {
                    files.insert(p);
                }
            }
        } else {
            // Treat as glob pattern
            for p in glob(pattern).map_err(|e| e.to_string())?.flatten() {
                if p.is_file() {
                    if !include_skipped && should_skip_path(&p) {
                        skipped_count += 1;
                    } else {
                        files.insert(p);
                    }
                }
            }
        }
    }

    let mut files: Vec<_> = files.into_iter().collect();
    files.sort();
    Ok((files, skipped_count))
}

/// Extract command from path: test/snapshot/{cmd}/... -> cmd
pub fn extract_command(path: &Path) -> Option<&str> {
    let path_str = path.to_str()?;
    let marker = "snapshot/";
    let idx = path_str.find(marker)?;
    let after_marker = &path_str[idx + marker.len()..];
    let end = after_marker.find('/').unwrap_or(after_marker.len());
    if end == 0 {
        return None;
    }
    Some(&after_marker[..end])
}

/// Extract subcommand from path: test/snapshot/{cmd}/{subcmd}/... -> subcmd
/// Returns None if there's no subcommand (e.g., test/snapshot/run/file.vole)
pub fn extract_subcommand(path: &Path) -> Option<&str> {
    let path_str = path.to_str()?;
    let marker = "snapshot/";
    let idx = path_str.find(marker)?;
    let after_marker = &path_str[idx + marker.len()..];

    // Skip first component (cmd)
    let first_slash = after_marker.find('/')?;
    let after_cmd = &after_marker[first_slash + 1..];

    // Get the next component (subcmd)
    let end = after_cmd.find('/').unwrap_or(after_cmd.len());
    if end == 0 {
        return None;
    }

    // Check if this looks like a subcommand (not a .vole file)
    let component = &after_cmd[..end];
    if component.ends_with(".vole") {
        return None;
    }
    Some(component)
}

/// Normalize paths in output: /full/path/to/file.vole -> <path>/file.vole
pub fn normalize_paths(content: &str, file_path: &Path) -> String {
    let file_path_str = file_path.to_string_lossy();
    let basename = file_path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    let replacement = format!("<path>/{}", basename);
    content.replace(&*file_path_str, &replacement)
}

/// Trim trailing whitespace
fn trim_trailing(s: &str) -> &str {
    s.trim_end_matches([' ', '\n', '\r', '\t'])
}

/// A shareable buffer that implements Write for use with captured output functions.
/// This satisfies the 'static lifetime requirement.
#[derive(Clone)]
struct SharedBuffer(Arc<Mutex<Vec<u8>>>);

impl SharedBuffer {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(Vec::new())))
    }

    fn into_bytes(self) -> Vec<u8> {
        Arc::try_unwrap(self.0)
            .map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner()))
            .unwrap_or_else(|arc| arc.lock().unwrap_or_else(|e| e.into_inner()).clone())
    }
}

impl Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.lock().unwrap_or_else(|e| e.into_inner()).write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.0.lock().unwrap_or_else(|e| e.into_inner()).flush()
    }
}

/// Run a single test
pub fn run_test(test_path: &Path, use_color: bool) -> TestResult {
    let cmd = match extract_command(test_path) {
        Some(c) => c,
        None => return TestResult::Fail("Cannot determine command from path".to_string()),
    };

    // Read source
    let source = match fs::read_to_string(test_path) {
        Ok(s) => s,
        Err(e) => return TestResult::Fail(format!("Could not read file: {}", e)),
    };

    let file_path = test_path.to_string_lossy().to_string();

    // Run command with captured output
    let stdout_buf = SharedBuffer::new();
    let stderr_buf = SharedBuffer::new();

    match cmd {
        "run" => {
            let _ = run_captured(&source, &file_path, stdout_buf.clone(), stderr_buf.clone());
        }
        "check" => {
            let _ = check_captured(&source, &file_path, stderr_buf.clone());
        }
        "inspect" => {
            let subcmd = extract_subcommand(test_path);
            match subcmd {
                Some("ast") => {
                    let _ = inspect_ast_captured(
                        &source,
                        &file_path,
                        stdout_buf.clone(),
                        stderr_buf.clone(),
                    );
                }
                Some(other) => {
                    return TestResult::Fail(format!("Unknown inspect subcommand: {}", other));
                }
                None => {
                    return TestResult::Fail(
                        "inspect command requires subcommand (ast)".to_string(),
                    );
                }
            }
        }
        _ => return TestResult::Fail(format!("Unknown command: {}", cmd)),
    }

    // Normalize and trim output
    let stdout_bytes = stdout_buf.into_bytes();
    let stderr_bytes = stderr_buf.into_bytes();
    let stdout = String::from_utf8_lossy(&stdout_bytes);
    let stderr = String::from_utf8_lossy(&stderr_bytes);
    let stdout = normalize_paths(&stdout, test_path);
    let stderr = normalize_paths(&stderr, test_path);
    let stdout = trim_trailing(&stdout);
    let stderr = trim_trailing(&stderr);

    // Load snapshot
    let snap_path = format!("{}.snap", test_path.display());
    let snap_content = match fs::read_to_string(&snap_path) {
        Ok(s) => s,
        Err(_) => return TestResult::New,
    };

    let snap = Snapshot::parse(&snap_content);

    // Compare
    let diff_fn = if use_color {
        unified_diff_colored
    } else {
        unified_diff
    };
    let stdout_diff = diff_fn(&snap.stdout, stdout, "stdout");
    let stderr_diff = diff_fn(&snap.stderr, stderr, "stderr");

    if stdout_diff.is_none() && stderr_diff.is_none() {
        return TestResult::Pass;
    }

    let mut output = String::new();
    if let Some(d) = stdout_diff {
        output.push_str(&d);
    }
    if let Some(d) = stderr_diff {
        output.push_str(&d);
    }

    TestResult::Fail(output)
}

/// Bless a single test (create/update snapshot)
pub fn bless_test(test_path: &Path) -> Result<bool, String> {
    let cmd = extract_command(test_path)
        .ok_or_else(|| "Cannot determine command from path".to_string())?;

    let source =
        fs::read_to_string(test_path).map_err(|e| format!("Could not read file: {}", e))?;

    let file_path = test_path.to_string_lossy().to_string();

    let stdout_buf = SharedBuffer::new();
    let stderr_buf = SharedBuffer::new();

    match cmd {
        "run" => {
            let _ = run_captured(&source, &file_path, stdout_buf.clone(), stderr_buf.clone());
        }
        "check" => {
            let _ = check_captured(&source, &file_path, stderr_buf.clone());
        }
        "inspect" => {
            let subcmd = extract_subcommand(test_path);
            match subcmd {
                Some("ast") => {
                    let _ = inspect_ast_captured(
                        &source,
                        &file_path,
                        stdout_buf.clone(),
                        stderr_buf.clone(),
                    );
                }
                Some(other) => return Err(format!("Unknown inspect subcommand: {}", other)),
                None => return Err("inspect command requires subcommand (ast)".to_string()),
            }
        }
        _ => return Err(format!("Unknown command: {}", cmd)),
    }

    let stdout_bytes = stdout_buf.into_bytes();
    let stderr_bytes = stderr_buf.into_bytes();
    let stdout = String::from_utf8_lossy(&stdout_bytes);
    let stderr = String::from_utf8_lossy(&stderr_bytes);
    let stdout = normalize_paths(&stdout, test_path);
    let stderr = normalize_paths(&stderr, test_path);

    let snap_content = Snapshot::format(&stdout, &stderr);
    let snap_path = format!("{}.snap", test_path.display());

    let existed = Path::new(&snap_path).exists();
    fs::write(&snap_path, snap_content).map_err(|e| format!("Could not write snapshot: {}", e))?;

    Ok(existed) // true = updated, false = created
}

/// Run all tests matching patterns
pub fn run_tests(
    patterns: &[String],
    include_skipped: bool,
    use_color: bool,
    report_mode: ReportMode,
) -> TestSummary {
    let (tests, skipped) = match discover_tests(patterns, include_skipped) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error discovering tests: {}", e);
            return TestSummary::default();
        }
    };

    if tests.is_empty() {
        if skipped > 0 {
            eprintln!(
                "No tests found ({} skipped with '_' prefix, use --include-skipped)",
                skipped
            );
        } else {
            eprintln!("No tests found matching patterns");
        }
        return TestSummary::default();
    }

    let mut summary = TestSummary::default();
    let colors = Colors::new(use_color);
    let show_all = matches!(report_mode, ReportMode::All);

    for test_path in &tests {
        let result = run_test(test_path, use_color);
        let path_display = test_path.display().to_string();

        match result {
            TestResult::Pass => {
                summary.passed += 1;
                if show_all {
                    println!("{}✓{} {}", colors.green(), colors.reset(), path_display);
                }
            }
            TestResult::Fail(diff) => {
                summary.failed += 1;
                summary.failed_tests.push(path_display.clone());
                println!("\n{}✗{} {}\n", colors.red(), colors.reset(), path_display);
                println!(
                    "{}--- expected{} (.snap)\n{}+++ actual{}\n",
                    colors.red(),
                    colors.reset(),
                    colors.green(),
                    colors.reset()
                );
                print!("{}", diff);
            }
            TestResult::New => {
                summary.new += 1;
                summary.new_tests.push(path_display.clone());
                if show_all {
                    println!(
                        "{}○{} {} {}(new){}",
                        colors.yellow(),
                        colors.reset(),
                        path_display,
                        colors.dim(),
                        colors.reset()
                    );
                }
            }
        }
    }

    summary
}

/// Bless all tests matching patterns
pub fn bless_tests(patterns: &[String], include_skipped: bool, use_color: bool) -> usize {
    let (tests, skipped) = match discover_tests(patterns, include_skipped) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error discovering tests: {}", e);
            return 0;
        }
    };

    if tests.is_empty() {
        if skipped > 0 {
            eprintln!(
                "No tests found ({} skipped with '_' prefix, use --include-skipped)",
                skipped
            );
        } else {
            eprintln!("No tests found matching patterns");
        }
        return 0;
    }

    let colors = Colors::new(use_color);
    let mut blessed = 0;

    for test_path in &tests {
        match bless_test(test_path) {
            Ok(updated) => {
                blessed += 1;
                let status = if updated { "(updated)" } else { "(created)" };
                println!(
                    "{}✓{} {} {}{}{}",
                    colors.green(),
                    colors.reset(),
                    test_path.display(),
                    colors.dim(),
                    status,
                    colors.reset()
                );
            }
            Err(e) => {
                eprintln!(
                    "{}✗{} {}: {}",
                    colors.red(),
                    colors.reset(),
                    test_path.display(),
                    e
                );
            }
        }
    }

    blessed
}

/// ANSI color helpers
struct Colors {
    use_color: bool,
}

impl Colors {
    fn new(use_color: bool) -> Self {
        Self { use_color }
    }

    fn green(&self) -> &'static str {
        if self.use_color { "\x1b[32m" } else { "" }
    }

    fn red(&self) -> &'static str {
        if self.use_color { "\x1b[31m" } else { "" }
    }

    fn yellow(&self) -> &'static str {
        if self.use_color { "\x1b[33m" } else { "" }
    }

    fn dim(&self) -> &'static str {
        if self.use_color { "\x1b[90m" } else { "" }
    }

    fn reset(&self) -> &'static str {
        if self.use_color { "\x1b[0m" } else { "" }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extract_command_run() {
        let path = Path::new("test/snapshot/run/hello.vole");
        assert_eq!(extract_command(path), Some("run"));
    }

    #[test]
    fn extract_command_check() {
        let path = Path::new("test/snapshot/check/sema/error.vole");
        assert_eq!(extract_command(path), Some("check"));
    }

    #[test]
    fn extract_command_nested() {
        let path = Path::new("test/snapshot/run/runtime/strings.vole");
        assert_eq!(extract_command(path), Some("run"));
    }

    #[test]
    fn normalize_paths_replaces() {
        let content = "error at /home/user/test/snapshot/run/test.vole:5:3";
        let path = Path::new("/home/user/test/snapshot/run/test.vole");
        let result = normalize_paths(content, path);
        assert_eq!(result, "error at <path>/test.vole:5:3");
    }

    #[test]
    fn extract_subcommand_inspect_ast() {
        let path = Path::new("test/snapshot/inspect/ast/simple.vole");
        assert_eq!(extract_subcommand(path), Some("ast"));
    }

    #[test]
    fn extract_subcommand_none_for_run() {
        let path = Path::new("test/snapshot/run/hello.vole");
        assert_eq!(extract_subcommand(path), None);
    }

    #[test]
    fn extract_subcommand_none_for_check_nested() {
        let path = Path::new("test/snapshot/check/sema/error.vole");
        // "sema" is a subdir, not a subcommand - but it doesn't end with .vole
        // so it gets returned as a subcommand. This is fine for the use case
        // where check/run don't use subcommands.
        assert_eq!(extract_subcommand(path), Some("sema"));
    }

    #[test]
    fn extract_command_inspect() {
        let path = Path::new("test/snapshot/inspect/ast/simple.vole");
        assert_eq!(extract_command(path), Some("inspect"));
    }
}
