// src/commands/inspect.rs

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use glob::glob;

use crate::cli::InspectType;

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
        let _source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: could not read '{}': {}", path.display(), e);
                had_error = true;
                continue;
            }
        };

        let file_path = path.to_string_lossy();

        // TODO: Process based on inspect_type
        match inspect_type {
            InspectType::Ast => {
                println!("TODO: AST for {} (no_tests={})", file_path, no_tests);
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
