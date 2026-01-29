// Integration tests for CLI implicit run and shebang support.
//
// Tests that `vole file.vole` works without the `run` subcommand,
// which is required for shebang scripts (`#!/usr/bin/env vole`).

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;

/// Returns the path to the cargo-built `vole` binary.
fn vole_binary() -> PathBuf {
    // `cargo test` sets this env var to the path of the built binary
    let path = PathBuf::from(env!("CARGO_BIN_EXE_vole"));
    assert!(path.exists(), "vole binary not found at {}", path.display());
    path
}

/// Helper to create a temp .vole file and return its path.
/// The file is created in a temp directory that is cleaned up when the returned
/// `TempDir` is dropped.
struct TempVoleFile {
    // Held to prevent cleanup until the struct is dropped.
    _dir: tempfile::TempDir,
    path: PathBuf,
}

impl TempVoleFile {
    fn new(filename: &str, content: &str) -> Self {
        let dir = tempfile::tempdir().expect("failed to create temp dir");
        let path = dir.path().join(filename);
        fs::write(&path, content).expect("failed to write temp file");
        Self { _dir: dir, path }
    }

    fn make_executable(&self) {
        let mut perms = fs::metadata(&self.path)
            .expect("failed to read metadata")
            .permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&self.path, perms).expect("failed to set permissions");
    }
}

#[test]
fn implicit_run_executes_vole_file() {
    // `vole file.vole` should work the same as `vole run file.vole`
    let tmp = TempVoleFile::new(
        "hello.vole",
        r#"func main() {
    println("implicit-run-ok")
}
"#,
    );

    let output = Command::new(vole_binary())
        .arg(&tmp.path)
        .output()
        .expect("failed to execute vole");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "vole exited with failure.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(stdout.trim(), "implicit-run-ok");
}

#[test]
fn explicit_run_still_works() {
    // `vole run file.vole` must continue to work
    let tmp = TempVoleFile::new(
        "hello.vole",
        r#"func main() {
    println("explicit-run-ok")
}
"#,
    );

    let output = Command::new(vole_binary())
        .args(["run", &tmp.path.to_string_lossy()])
        .output()
        .expect("failed to execute vole");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "vole run exited with failure.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(stdout.trim(), "explicit-run-ok");
}

#[test]
fn shebang_end_to_end() {
    // Full shebang pipeline: create a .vole file with a shebang line pointing
    // to a copy of the cargo-built binary, chmod +x, execute directly, and
    // verify output.
    //
    // We copy the binary to a temp location to avoid "Text file busy" errors
    // that occur when the kernel tries to exec a binary that cargo's test
    // harness may still have open.
    let original_binary = vole_binary();
    let bin_dir = tempfile::tempdir().expect("failed to create temp dir for binary");
    let binary_copy = bin_dir.path().join("vole");
    fs::copy(&original_binary, &binary_copy).expect("failed to copy vole binary");
    let mut perms = fs::metadata(&binary_copy)
        .expect("failed to read binary metadata")
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&binary_copy, perms).expect("failed to set binary permissions");

    let shebang_line = format!("#!{}\n", binary_copy.display());
    let source = format!(
        r#"{shebang_line}func main() {{
    println("shebang-works")
}}
"#
    );

    let tmp = TempVoleFile::new("shebang_test.vole", &source);
    tmp.make_executable();

    let output = Command::new(&tmp.path)
        .output()
        .expect("failed to execute shebang script");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "shebang script exited with failure.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(stdout.trim(), "shebang-works");
}

#[test]
fn unrecognized_command_gives_error() {
    // A non-.vole argument that isn't a known subcommand should fail gracefully
    let output = Command::new(vole_binary())
        .arg("notacommand")
        .output()
        .expect("failed to execute vole");

    assert!(
        !output.status.success(),
        "expected failure for unrecognized command"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unrecognized command"),
        "expected 'unrecognized command' in stderr, got: {stderr}"
    );
}

#[test]
fn other_subcommands_unaffected() {
    // `vole check` should still work (testing with an invalid path to confirm
    // the subcommand is recognized, even if it errors on missing files)
    let output = Command::new(vole_binary())
        .args(["check", "nonexistent.vole"])
        .output()
        .expect("failed to execute vole");

    // It will fail because the file doesn't exist, but it should NOT say
    // "unrecognized command" — the subcommand should be properly dispatched.
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("unrecognized command"),
        "check subcommand was not recognized: {stderr}"
    );
}
