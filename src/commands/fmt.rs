// src/commands/fmt.rs
//! Format Vole source files with canonical style.

use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::ExitCode;

use crate::cli::expand_paths;
use crate::fmt::{self, CANONICAL};

/// Options for formatting
pub struct FmtOptions {
    /// Check only - don't modify files, exit 1 if any need formatting
    pub check: bool,
    /// Write to stdout instead of modifying files
    pub stdout: bool,
}

/// Format Vole source files.
///
/// - With no options: format files in-place
/// - With --check: report which files need formatting, exit 1 if any
/// - With --stdout: write formatted output to stdout
/// - Use "-" to read from stdin and write to stdout
pub fn format_files(patterns: &[String], options: FmtOptions) -> ExitCode {
    // Handle stdin specially
    if patterns.len() == 1 && patterns[0] == "-" {
        return format_stdin(options.check);
    }

    let files = match expand_paths(patterns) {
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

    let mut needs_formatting: u32 = 0;
    let mut had_errors = false;

    for path in &files {
        match format_single_file(path, &options) {
            Ok(changed) => {
                if changed && options.check {
                    // In check mode, print files that need formatting
                    println!("{}", path.display());
                    needs_formatting += 1;
                }
            }
            Err(e) => {
                eprintln!("{}: {}", path.display(), e);
                had_errors = true;
            }
        }
    }

    if had_errors {
        return ExitCode::from(2);
    }

    if options.check && needs_formatting > 0 {
        eprintln!("{} file(s) need formatting", needs_formatting);
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}

/// Format a single file. Returns whether the file was changed.
fn format_single_file(path: &Path, options: &FmtOptions) -> Result<bool, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("could not read: {}", e))?;

    let result = fmt::format(&source, CANONICAL).map_err(|e| e.to_string())?;

    if options.stdout {
        // Write to stdout
        print!("{}", result.output);
        Ok(result.changed)
    } else if options.check {
        // Check mode - just report whether it changed
        Ok(result.changed)
    } else if result.changed {
        // In-place mode - write back to file
        fs::write(path, &result.output).map_err(|e| format!("could not write: {}", e))?;
        Ok(true)
    } else {
        Ok(false)
    }
}

/// Format source from stdin, write to stdout.
fn format_stdin(check_mode: bool) -> ExitCode {
    let mut source = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut source) {
        eprintln!("error: could not read stdin: {}", e);
        return ExitCode::from(2);
    }

    let result = match fmt::format(&source, CANONICAL) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("stdin: {}", e);
            return ExitCode::from(2);
        }
    };

    if check_mode {
        if result.changed {
            eprintln!("stdin: not formatted");
            return ExitCode::FAILURE;
        }
    } else {
        print!("{}", result.output);
        let _ = io::stdout().flush();
    }

    ExitCode::SUCCESS
}
