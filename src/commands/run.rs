// src/commands/run.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::common::{parse_and_analyze, read_stdin};
use crate::codegen::{Compiler, JitContext};

/// Run a Vole source file (or stdin if path is "-")
pub fn run_file(path: &Path) -> ExitCode {
    match execute(path) {
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

fn execute(path: &Path) -> Result<(), String> {
    // Read source from file or stdin
    let (source, file_path) = if path.as_os_str() == "-" {
        let source = read_stdin().map_err(|e| format!("could not read stdin: {}", e))?;
        (source, "<stdin>".to_string())
    } else {
        let source = fs::read_to_string(path)
            .map_err(|e| format!("could not read '{}': {}", path.display(), e))?;
        (source, path.to_string_lossy().to_string())
    };

    // Parse and type check
    let analyzed = parse_and_analyze(&source, &file_path).map_err(|()| String::new())?;

    // Compile
    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(
            &mut jit,
            &analyzed.interner,
            analyzed.type_aliases.clone(),
            analyzed.expr_types.clone(),
            analyzed.method_resolutions.clone(),
            analyzed.interface_registry.clone(),
            analyzed.type_implements.clone(),
            analyzed.error_types.clone(),
            analyzed.module_programs.clone(),
        );
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
