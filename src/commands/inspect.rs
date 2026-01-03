// src/commands/inspect.rs

use std::process::ExitCode;

use crate::cli::InspectType;

/// Inspect compilation output for the given files
pub fn inspect_files(
    files: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    _imports: Option<&str>,
) -> ExitCode {
    eprintln!(
        "inspect {:?} files={:?} no_tests={}",
        inspect_type, files, no_tests
    );
    ExitCode::SUCCESS
}
