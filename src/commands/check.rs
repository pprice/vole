// src/commands/check.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::common::parse_and_analyze;

/// Check a Vole source file (parse + type check, no execution)
pub fn check_file(path: &Path) -> ExitCode {
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read '{}': {}", path.display(), e);
            return ExitCode::FAILURE;
        }
    };

    let file_path = path.to_string_lossy();
    match parse_and_analyze(&source, &file_path) {
        Ok(_) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE, // diagnostics already rendered
    }
}
