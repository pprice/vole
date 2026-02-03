// src/commands/check.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::common::{PipelineError, PipelineOptions, compile_source, read_stdin};
use crate::cli::expand_paths_flat;
use crate::runtime::push_context;

/// Check Vole source files (parse + type check, no execution)
/// Use "-" to read from stdin.
pub fn check_files(patterns: &[String]) -> ExitCode {
    // Handle stdin specially
    if patterns.len() == 1 && patterns[0] == "-" {
        return check_stdin();
    }

    let files = match expand_paths_flat(patterns) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::FAILURE;
        }
    };

    if files.is_empty() {
        eprintln!("error: no .vole files found");
        return ExitCode::FAILURE;
    }

    let mut had_error = false;

    for path in &files {
        if check_single_file(path).is_err() {
            had_error = true;
        }
    }

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Check source from stdin
fn check_stdin() -> ExitCode {
    let source = match read_stdin() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read stdin: {}", e);
            return ExitCode::FAILURE;
        }
    };

    match compile_source(
        PipelineOptions {
            source: &source,
            file_path: "<stdin>",
            skip_tests: false,
            project_root: None,
            module_cache: None,
        },
        &mut std::io::stderr(),
    ) {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}

/// Check a single file, returns Ok(()) on success
fn check_single_file(path: &Path) -> Result<(), PipelineError> {
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read '{}': {}", path.display(), e);
            return Err(PipelineError::Io);
        }
    };

    let file_path = path.to_string_lossy();
    push_context(&format!("checking {}", file_path));
    compile_source(
        PipelineOptions {
            source: &source,
            file_path: &file_path,
            skip_tests: false,
            project_root: None,
            module_cache: None,
        },
        &mut std::io::stderr(),
    )?;
    Ok(())
}
