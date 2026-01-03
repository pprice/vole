// src/commands/inspect.rs

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use glob::glob;
use miette::NamedSource;

use crate::cli::InspectType;
use crate::errors::render_to_stderr;
use crate::frontend::{AstPrinter, Parser};

/// Inspect compilation output for the given files
pub fn inspect_files(
    patterns: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    _imports: Option<&str>,
) -> ExitCode {
    // Expand globs and collect unique files
    let mut files: Vec<PathBuf> = Vec::new();
    let mut seen: HashSet<PathBuf> = HashSet::new();

    for pattern in patterns {
        match glob(pattern) {
            Ok(paths) => {
                for entry in paths.flatten() {
                    if let Ok(canonical) = entry.canonicalize() {
                        if seen.insert(canonical.clone()) {
                            files.push(entry);
                        }
                    } else if seen.insert(entry.clone()) {
                        files.push(entry);
                    }
                }
            }
            Err(e) => {
                eprintln!("error: invalid glob pattern '{}': {}", pattern, e);
            }
        }
    }

    if files.is_empty() {
        eprintln!("error: no matching files found");
        return ExitCode::FAILURE;
    }

    let mut had_error = false;

    for (i, path) in files.iter().enumerate() {
        // Print separator between files
        if i > 0 {
            println!();
        }

        // Print file header to stderr
        eprintln!("// {}", path.display());

        // Read source
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: could not read '{}': {}", path.display(), e);
                had_error = true;
                continue;
            }
        };

        let file_path = path.to_string_lossy();

        match inspect_type {
            InspectType::Ast => {
                // Parse
                let mut parser = Parser::with_file(&source, &file_path);
                let program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        let report = miette::Report::new(e.error.clone())
                            .with_source_code(NamedSource::new(
                                &file_path,
                                source.clone(),
                            ));
                        render_to_stderr(report.as_ref());
                        had_error = true;
                        continue;
                    }
                };

                let interner = parser.into_interner();
                let printer = AstPrinter::new(&interner, no_tests);
                print!("{}", printer.print_program(&program));
            }
            InspectType::Ir => {
                println!("TODO: IR for {} (no_tests={})", file_path, no_tests);
            }
        }
    }

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
