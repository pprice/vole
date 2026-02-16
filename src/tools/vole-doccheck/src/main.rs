use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use glob::glob;

/// A code block extracted from a markdown file.
struct CodeBlock {
    /// The source markdown file.
    file: PathBuf,
    /// 1-based line number where the opening fence is.
    line: usize,
    /// The raw source code inside the fence.
    code: String,
}

/// Extract all ```vole code blocks from a markdown file.
/// Skips blocks tagged ```vole,ignore.
fn extract_blocks(path: &Path) -> Vec<CodeBlock> {
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("  warning: cannot read {}: {e}", path.display());
            return vec![];
        }
    };

    let mut blocks = Vec::new();
    let mut in_vole_block = false;
    let mut in_ignore_block = false;
    let mut in_other_block = false;
    let mut current_code = String::new();
    let mut block_start = 0;

    for (i, line) in content.lines().enumerate() {
        let lineno = i + 1;
        let trimmed = line.trim();

        if in_vole_block {
            if trimmed == "```" {
                blocks.push(CodeBlock {
                    file: path.to_path_buf(),
                    line: block_start,
                    code: current_code.clone(),
                });
                current_code.clear();
                in_vole_block = false;
            } else {
                current_code.push_str(line);
                current_code.push('\n');
            }
        } else if in_ignore_block || in_other_block {
            if trimmed == "```" {
                in_ignore_block = false;
                in_other_block = false;
            }
        } else if trimmed.starts_with("```") {
            let after_backticks = &trimmed[3..];
            if after_backticks.starts_with("vole") {
                let rest = &after_backticks[4..];
                if rest.contains("ignore") {
                    in_ignore_block = true;
                } else if rest.is_empty() || rest.starts_with(' ') {
                    in_vole_block = true;
                    block_start = lineno;
                    current_code.clear();
                } else {
                    // Something like ```volexyz - not a vole block
                    in_other_block = true;
                }
            } else {
                in_other_block = true;
            }
        }
    }

    blocks
}

/// Check a single code block by writing it to a temp file and running `vole check`.
fn check_block(block: &CodeBlock, vole_bin: &Path, temp_dir: &Path) -> bool {
    let temp_file = temp_dir.join("doccheck.vole");
    if let Err(e) = fs::write(&temp_file, &block.code) {
        eprintln!("  error: cannot write temp file: {e}");
        return false;
    }

    let output = Command::new(vole_bin).arg("check").arg(&temp_file).output();

    match output {
        Ok(out) => {
            if out.status.success() {
                true
            } else {
                let stderr = String::from_utf8_lossy(&out.stderr);
                eprintln!(
                    "  FAIL {}:{}\n{}",
                    block.file.display(),
                    block.line,
                    indent_stderr(&stderr, &temp_file, &block.file, block.line),
                );
                false
            }
        }
        Err(e) => {
            eprintln!("  error: cannot run vole: {e}");
            false
        }
    }
}

/// Rewrite temp file paths in error output to show the original markdown location.
fn indent_stderr(stderr: &str, temp_path: &Path, md_file: &Path, _block_line: usize) -> String {
    let temp_str = temp_path.display().to_string();
    let md_str = md_file.display().to_string();
    stderr
        .lines()
        .map(|l| format!("    {}", l.replace(&temp_str, &md_str)))
        .collect::<Vec<_>>()
        .join("\n")
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: vole-doccheck <markdown-files-or-globs...>");
        eprintln!("  Validates ```vole code blocks in markdown files.");
        eprintln!("  Use ```vole,ignore to skip blocks with intentional errors.");
        return ExitCode::from(2);
    }

    // Find the vole binary
    let vole_bin = find_vole_binary();

    // Collect all markdown files from arguments
    let mut md_files: Vec<PathBuf> = Vec::new();
    for pattern in &args[1..] {
        match glob(pattern) {
            Ok(paths) => {
                for entry in paths {
                    match entry {
                        Ok(p) if p.extension().is_some_and(|e| e == "md") => {
                            md_files.push(p);
                        }
                        Ok(p) => {
                            // If it's a directory, glob for *.md inside it
                            if p.is_dir() {
                                let dir_pattern = format!("{}/**/*.md", p.display());
                                if let Ok(inner) = glob(&dir_pattern) {
                                    for entry in inner.flatten() {
                                        md_files.push(entry);
                                    }
                                }
                            }
                        }
                        Err(e) => eprintln!("warning: glob error: {e}"),
                    }
                }
            }
            Err(e) => {
                eprintln!("error: bad pattern '{}': {e}", pattern);
                return ExitCode::from(2);
            }
        }
    }

    if md_files.is_empty() {
        eprintln!("No markdown files found.");
        return ExitCode::from(2);
    }

    md_files.sort();

    // Create temp directory
    let temp_dir = env::temp_dir().join("vole-doccheck");
    let _ = fs::create_dir_all(&temp_dir);

    let mut total_blocks = 0;
    let mut passed = 0;
    let mut failed = 0;
    let mut failed_locations: Vec<String> = Vec::new();

    for md_file in &md_files {
        let blocks = extract_blocks(md_file);
        if blocks.is_empty() {
            continue;
        }

        let file_name = md_file.file_name().unwrap_or_default().to_string_lossy();
        let block_count = blocks.len();
        total_blocks += block_count;

        let mut file_passed = 0;
        let mut file_failed = 0;

        for block in &blocks {
            if check_block(block, &vole_bin, &temp_dir) {
                file_passed += 1;
                passed += 1;
            } else {
                file_failed += 1;
                failed += 1;
                failed_locations.push(format!("{}:{}", md_file.display(), block.line));
            }
        }

        let status = if file_failed == 0 { "PASS" } else { "FAIL" };
        println!("{status} {file_name} ({file_passed}/{block_count} blocks)");
    }

    // Clean up
    let _ = fs::remove_dir_all(&temp_dir);

    // Summary
    println!();
    if failed == 0 {
        println!("All {total_blocks} code blocks passed.");
        ExitCode::SUCCESS
    } else {
        println!("{passed} passed, {failed} failed out of {total_blocks} blocks.");
        println!();
        println!("Failed blocks:");
        for loc in &failed_locations {
            println!("  {loc}");
        }
        ExitCode::FAILURE
    }
}

/// Find the vole binary, preferring the cargo target directory.
fn find_vole_binary() -> PathBuf {
    // Check if VOLE_BIN is set
    if let Ok(bin) = env::var("VOLE_BIN") {
        return PathBuf::from(bin);
    }

    // Try to find it relative to the current exe
    if let Ok(exe) = env::current_exe() {
        let dir = exe.parent().unwrap_or(Path::new("."));
        let candidate = dir.join("vole");
        if candidate.exists() {
            return candidate;
        }
    }

    // Fall back to PATH
    PathBuf::from("vole")
}
