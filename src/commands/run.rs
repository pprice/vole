// src/commands/run.rs

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use crate::frontend::Parser;
use crate::sema::Analyzer;
use crate::codegen::{JitContext, Compiler};

/// Run a Vole source file
pub fn run_file(path: &Path) -> ExitCode {
    match execute_file(path) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {}", e);
            ExitCode::FAILURE
        }
    }
}

fn execute_file(path: &Path) -> Result<(), String> {
    // Read source file
    let source = fs::read_to_string(path)
        .map_err(|e| format!("could not read '{}': {}", path.display(), e))?;

    // Parse
    let mut parser = Parser::new(&source);
    let program = parser.parse_program()
        .map_err(|e| format!("parse error at {:?}: {}", e.span, e.message))?;
    let interner = parser.into_interner();

    // Type check
    let file_path = path.to_string_lossy();
    let mut analyzer = Analyzer::new(&file_path, &source);
    analyzer.analyze(&program, &interner)
        .map_err(|errors| {
            let msgs: Vec<String> = errors.iter()
                .map(|e| format!("  {:?}: {}", e.span(), e.message()))
                .collect();
            format!("type errors:\n{}", msgs.join("\n"))
        })?;

    // Compile
    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(&mut jit, &interner);
        compiler.compile_program(&program)
            .map_err(|e| format!("compilation error: {}", e))?;
    }
    jit.finalize();

    // Execute main
    let fn_ptr = jit.get_function_ptr("main")
        .ok_or_else(|| "no 'main' function found".to_string())?;

    // Call main - it may or may not return a value
    // We use extern "C" fn() since main() in Vole can be void
    let main: extern "C" fn() = unsafe { std::mem::transmute(fn_ptr) };
    main();

    Ok(())
}
