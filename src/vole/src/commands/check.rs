// src/commands/check.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::common::{
    PipelineError, PipelineOptions, compile_source, read_stdin, render_pipeline_error,
};
use crate::cli::{ColorMode, expand_paths_flat};
use crate::runtime::push_context;

/// Check Vole source files (parse + type check, no execution)
/// Use "-" to read from stdin.
pub fn check_files(patterns: &[String], color_mode: ColorMode) -> ExitCode {
    // Handle stdin specially
    if patterns.len() == 1 && patterns[0] == "-" {
        return check_stdin(color_mode);
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
        if check_single_file(path, color_mode).is_err() {
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
fn check_stdin(color_mode: ColorMode) -> ExitCode {
    let source = match read_stdin() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read stdin: {}", e);
            return ExitCode::FAILURE;
        }
    };

    let result = compile_source(
        PipelineOptions {
            source: &source,
            file_path: "<stdin>",
            skip_tests: false,
            project_root: None,
            module_cache: None,
            color_mode,
        },
        &mut std::io::stderr(),
    );
    if let Err(ref e) = result {
        render_pipeline_error(
            e,
            "<stdin>",
            &source,
            &mut std::io::stderr(),
            color_mode,
            false,
        );
    }
    match result {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}

/// Check a single file, returns Ok(()) on success
fn check_single_file(path: &Path, color_mode: ColorMode) -> Result<(), PipelineError> {
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read '{}': {}", path.display(), e);
            return Err(PipelineError::Io {
                path: path.to_path_buf(),
                source: e,
            });
        }
    };

    let file_path = path.to_string_lossy();
    push_context(&format!("checking {}", file_path));
    let result = compile_source(
        PipelineOptions {
            source: &source,
            file_path: &file_path,
            skip_tests: false,
            project_root: None,
            module_cache: None,
            color_mode,
        },
        &mut std::io::stderr(),
    );
    if let Err(ref e) = result {
        render_pipeline_error(
            e,
            &file_path,
            &source,
            &mut std::io::stderr(),
            color_mode,
            false,
        );
    }
    result?;
    Ok(())
}
