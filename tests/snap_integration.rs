// tests/snap_integration.rs
//! Integration tests for vole-snap functionality.

use std::process::Command;

#[test]
fn vole_snap_test_passes() {
    let output = Command::new("cargo")
        .args(["run", "--bin", "vole-snap", "--", "test", "test/snapshot/"])
        .output()
        .expect("Failed to run vole-snap");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("passed"),
        "Expected 'passed' in output: {}",
        stdout
    );
    assert!(
        output.status.success(),
        "Expected success exit code, got: {:?}",
        output.status
    );
}

#[test]
fn vole_snap_help_works() {
    let output = Command::new("cargo")
        .args(["run", "--bin", "vole-snap", "--", "--help"])
        .output()
        .expect("Failed to run vole-snap");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Snapshot testing"));
    assert!(stdout.contains("test"));
    assert!(stdout.contains("bless"));
}

#[test]
fn vole_check_command_works() {
    // Test check on a valid file
    let output = Command::new("cargo")
        .args(["run", "--bin", "vole", "--", "check", "test/snapshot/run/hello.vole"])
        .output()
        .expect("Failed to run vole check");

    assert!(
        output.status.success(),
        "Expected success for valid file"
    );

    // Test check on an error file
    let output = Command::new("cargo")
        .args(["run", "--bin", "vole", "--", "check", "test/snapshot/check/sema/undefined_variable.vole"])
        .output()
        .expect("Failed to run vole check");

    assert!(
        !output.status.success(),
        "Expected failure for error file"
    );
}
