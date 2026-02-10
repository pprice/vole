// tests/integration.rs
//! Integration tests for vole-reduce binary.
//!
//! These tests shell out to the compiled binary and verify end-to-end behavior.

use std::fs;
use std::process::Command;

/// Path to the vole-reduce binary (built by cargo test).
fn vole_reduce_bin() -> String {
    // cargo test puts test binaries in target/debug/deps, but the actual binary
    // is at target/debug/vole-reduce.
    let mut path = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    path.push("vole-reduce");
    path.display().to_string()
}

/// Create a temporary directory with a simple Vole project that has a bug.
fn make_buggy_project() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    fs::write(
        dir.path().join("main.vole"),
        "func main() {\n    let x = undefined_var\n}\n",
    )
    .unwrap();
    dir
}

#[test]
fn binary_rejects_no_oracle_args() {
    let dir = make_buggy_project();
    let output = Command::new(vole_reduce_bin())
        .arg(dir.path())
        .output()
        .expect("failed to run vole-reduce");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("oracle"),
        "Expected error about missing oracle, got: {stderr}",
    );
}

#[test]
fn binary_rejects_nonexistent_input() {
    let output = Command::new(vole_reduce_bin())
        .args(["--exit-code", "1"])
        .arg("/nonexistent/path/to/vole/project")
        .output()
        .expect("failed to run vole-reduce");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("does not exist"),
        "Expected 'does not exist' error, got: {stderr}",
    );
}

#[test]
fn binary_force_overwrites_output() {
    let dir = make_buggy_project();
    let output_dir = tempfile::tempdir().unwrap();
    let output_path = output_dir.path().join("out");

    // Create output directory manually to simulate pre-existing output.
    fs::create_dir_all(&output_path).unwrap();

    // Without --force, should fail.
    let output = Command::new(vole_reduce_bin())
        .arg(dir.path())
        .args(["--exit-code", "1"])
        .args(["--output", &output_path.display().to_string()])
        .args(["--command", "false"])
        .output()
        .expect("failed to run vole-reduce");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("already exists"),
        "Expected 'already exists' error, got: {stderr}",
    );
}

#[test]
fn binary_runs_with_custom_oracle_command() {
    let dir = make_buggy_project();
    let output_dir = tempfile::tempdir().unwrap();
    let output_path = output_dir.path().join("out");

    // Use a custom command that always "reproduces" the bug (exit 1).
    let output = Command::new(vole_reduce_bin())
        .arg(dir.path())
        .args(["--exit-code", "1"])
        .args(["--output", &output_path.display().to_string()])
        .args(["--command", "exit 1"])
        .args(["--max-iterations", "20"])
        .output()
        .expect("failed to run vole-reduce");

    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "vole-reduce should succeed, stderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );

    // Verify the summary was printed.
    assert!(
        stdout.contains("Reduction Summary"),
        "Expected summary in output, got: {stdout}",
    );
    assert!(
        stdout.contains("Lines:"),
        "Expected Lines: in summary, got: {stdout}",
    );
    assert!(
        stdout.contains("Files:"),
        "Expected Files: in summary, got: {stdout}",
    );

    // Verify the result directory exists.
    assert!(output_path.join("result").exists());

    // Verify the log file was written.
    let log_content = fs::read_to_string(output_path.join("log.txt")).unwrap();
    assert!(
        log_content.contains("Reduction Summary"),
        "Log should contain summary, got: {log_content}",
    );
}

#[test]
fn binary_shows_help() {
    let output = Command::new(vole_reduce_bin())
        .arg("--help")
        .output()
        .expect("failed to run vole-reduce");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Test case minimizer"),
        "Help should mention test case minimizer, got: {stdout}",
    );
}

#[test]
fn binary_baseline_fails_when_bug_not_reproduced() {
    let dir = make_buggy_project();
    let output_dir = tempfile::tempdir().unwrap();
    let output_path = output_dir.path().join("out");

    // Use a command that always succeeds (exit 0) — the bug won't reproduce.
    let output = Command::new(vole_reduce_bin())
        .arg(dir.path())
        .args(["--exit-code", "1"])
        .args(["--output", &output_path.display().to_string()])
        .args(["--command", "exit 0"])
        .output()
        .expect("failed to run vole-reduce");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("does not reproduce"),
        "Expected 'does not reproduce' error, got: {stderr}",
    );
}
