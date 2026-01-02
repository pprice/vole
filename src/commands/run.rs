// src/commands/run.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::common::parse_and_analyze;
use crate::codegen::{Compiler, JitContext};

/// Run a Vole source file
pub fn run_file(path: &Path) -> ExitCode {
    match execute_file(path) {
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

fn execute_file(path: &Path) -> Result<(), String> {
    // Read source file
    let source = fs::read_to_string(path)
        .map_err(|e| format!("could not read '{}': {}", path.display(), e))?;
    let file_path = path.to_string_lossy();

    // Parse and type check
    let analyzed = parse_and_analyze(&source, &file_path).map_err(|()| String::new())?;

    // Compile
    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(&mut jit, &analyzed.interner);
        compiler
            .compile_program(&analyzed.program)
            .map_err(|e| format!("compilation error: {}", e))?;
    }
    jit.finalize();

    // Execute main
    let fn_ptr = jit
        .get_function_ptr("main")
        .ok_or_else(|| "no 'main' function found".to_string())?;

    // Call main - it may or may not return a value
    // We use extern "C" fn() since main() in Vole can be void
    let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };
    main();

    Ok(())
}
