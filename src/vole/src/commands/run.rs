// src/commands/run.rs

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use super::common::{
    PipelineError, PipelineOptions, RunOptions, compile_and_run, compile_source, read_stdin,
    render_pipeline_error,
};
use crate::cli::ColorMode;
use crate::codegen::JitOptions;
use crate::runtime::{push_context, replace_context};

/// Run a Vole source file (or stdin if path is "-")
pub fn run_file(
    path: &Path,
    project_root: Option<&Path>,
    release: bool,
    color_mode: ColorMode,
) -> ExitCode {
    // Validate project root if provided
    if let Some(root) = project_root {
        if !root.exists() {
            eprintln!("error: --root path does not exist: {}", root.display());
            return ExitCode::FAILURE;
        }
        if !root.is_dir() {
            eprintln!("error: --root path is not a directory: {}", root.display());
            return ExitCode::FAILURE;
        }
    }

    match execute(path, project_root, release, color_mode) {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}

fn execute(
    path: &Path,
    project_root: Option<&Path>,
    release: bool,
    color_mode: ColorMode,
) -> Result<(), PipelineError> {
    // Read source from file or stdin
    let (source, file_path) = if path.as_os_str() == "-" {
        let source = read_stdin().map_err(|e| PipelineError::Io {
            path: PathBuf::from("<stdin>"),
            source: e,
        })?;
        (source, "<stdin>".to_string())
    } else {
        let source = fs::read_to_string(path).map_err(|e| PipelineError::Io {
            path: path.to_path_buf(),
            source: e,
        })?;
        (source, path.to_string_lossy().to_string())
    };

    // Set context for signal handler
    push_context(&file_path);

    // Parse and type check (skip tests blocks in run mode)
    replace_context(&format!("{} (parsing)", file_path));
    let compile_result = compile_source(
        PipelineOptions {
            source: &source,
            file_path: &file_path,
            skip_tests: true,
            project_root,
            module_cache: None,
            color_mode,
        },
        &mut std::io::stderr(),
    );
    if let Err(ref e) = compile_result {
        render_pipeline_error(
            e,
            &file_path,
            &source,
            &mut std::io::stderr(),
            color_mode,
            true,
        );
    }
    let analyzed = compile_result?;

    // Codegen + execute phase
    replace_context(&format!("{} (compiling)", file_path));
    let jit_options = if release {
        JitOptions::release()
    } else {
        JitOptions::debug()
    };

    let run_opts = RunOptions {
        file_path: &file_path,
        jit_options,
        skip_tests: true,
    };

    replace_context(&format!("{} (executing main)", file_path));
    let result = compile_and_run(&analyzed, &run_opts);
    if let Err(ref e) = result {
        render_pipeline_error(
            e,
            &file_path,
            &source,
            &mut std::io::stderr(),
            color_mode,
            true,
        );
    }
    result
}
