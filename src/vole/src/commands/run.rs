// src/commands/run.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::common::{PipelineOptions, compile_source, read_stdin};
use crate::codegen::{Compiler, JitContext, JitOptions};
use crate::runtime::{push_context, replace_context};

/// Run a Vole source file (or stdin if path is "-")
pub fn run_file(path: &Path, project_root: Option<&Path>, release: bool) -> ExitCode {
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

    match execute(path, project_root, release) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            // Empty error means diagnostics were already rendered
            if !e.is_empty() {
                eprintln!("error: {}", e);
            }
            ExitCode::FAILURE
        }
    }
}

fn execute(path: &Path, project_root: Option<&Path>, release: bool) -> Result<(), String> {
    // Read source from file or stdin
    let (source, file_path) = if path.as_os_str() == "-" {
        let source = read_stdin().map_err(|e| format!("could not read stdin: {}", e))?;
        (source, "<stdin>".to_string())
    } else {
        let source = fs::read_to_string(path)
            .map_err(|e| format!("could not read '{}': {}", path.display(), e))?;
        (source, path.to_string_lossy().to_string())
    };

    // Set context for signal handler
    push_context(&file_path);

    // Parse and type check (skip tests blocks in run mode)
    replace_context(&format!("{} (parsing)", file_path));
    let analyzed = compile_source(
        PipelineOptions {
            source: &source,
            file_path: &file_path,
            skip_tests: true,
            project_root,
            module_cache: None,
        },
        &mut std::io::stderr(),
    )
    .map_err(|()| String::new())?;

    // Codegen phase
    replace_context(&format!("{} (compiling)", file_path));
    let options = if release {
        JitOptions::release()
    } else {
        JitOptions::debug()
    };
    let jit = {
        let _span = tracing::info_span!("codegen").entered();
        let mut jit = JitContext::with_options(options);
        {
            let mut compiler = Compiler::new(&mut jit, &analyzed);
            compiler.set_source_file(&file_path);
            compiler.set_skip_tests(true);
            compiler
                .compile_program(&analyzed.program)
                .map_err(|e| format!("compilation error: {}", e))?;
        }
        jit.finalize()?;
        tracing::debug!("compilation complete");
        jit
    };

    // Execute phase
    replace_context(&format!("{} (executing main)", file_path));
    {
        let _span = tracing::info_span!("execute").entered();
        let fn_ptr = jit
            .get_function_ptr("main")
            .ok_or_else(|| "no 'main' function found".to_string())?;

        // Call main - it may or may not return a value
        // We use extern "C" fn() since main() in Vole can be void
        let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };
        main();
    }

    Ok(())
}
