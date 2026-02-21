use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use glob::glob;

use vole::cli::ColorMode;
use vole::commands::common::{
    PipelineOptions, RunOptions, compile_and_run, compile_source, render_pipeline_error,
};

/// A code block extracted from a markdown file.
struct CodeBlock {
    /// The source markdown file.
    file: PathBuf,
    /// 1-based line number where the opening fence is.
    line: usize,
    /// The raw source code inside the fence.
    code: String,
    /// How to validate this block.
    mode: BlockMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockMode {
    Check,
    Test,
    Run,
}

/// Determine how to validate a code block based on its content.
fn block_mode(code: &str) -> BlockMode {
    if code.contains("tests ") || code.contains("tests{") {
        BlockMode::Test
    } else if code.contains("func main(") || code.contains("func main()") {
        BlockMode::Run
    } else {
        BlockMode::Check
    }
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
                let mode = block_mode(&current_code);
                blocks.push(CodeBlock {
                    file: path.to_path_buf(),
                    line: block_start,
                    code: current_code.clone(),
                    mode,
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
                    in_other_block = true;
                }
            } else {
                in_other_block = true;
            }
        }
    }

    blocks
}

/// Check a code block using the in-process compiler.
fn check_block(block: &CodeBlock) -> bool {
    let file_label = format!("{}:{}", block.file.display(), block.line);

    match block.mode {
        BlockMode::Check => check_block_compile(&block.code, &file_label, "check", false),
        BlockMode::Test => check_block_compile(&block.code, &file_label, "test", false),
        BlockMode::Run => check_block_run(&block.code, &file_label),
    }
}

/// Validate a block with `compile_source` (parse + type check only).
fn check_block_compile(code: &str, file_label: &str, mode: &str, skip_tests: bool) -> bool {
    let mut warnings = Vec::new();
    let result = compile_source(
        PipelineOptions {
            source: code,
            file_path: file_label,
            skip_tests,
            project_root: None,
            module_cache: None,
            color_mode: ColorMode::Never,
        },
        &mut warnings,
    );
    if let Err(ref e) = result {
        let mut buf = Vec::new();
        render_pipeline_error(e, file_label, code, &mut buf, ColorMode::Never, false);
        let msg = String::from_utf8_lossy(&buf);
        eprintln!("  FAIL {file_label} (mode: {mode})\n{}", indent(&msg));
        return false;
    }
    true
}

/// Validate a block by compiling and running `main`.
fn check_block_run(code: &str, file_label: &str) -> bool {
    let mut warnings = Vec::new();
    let analyzed = match compile_source(
        PipelineOptions {
            source: code,
            file_path: file_label,
            skip_tests: true,
            project_root: None,
            module_cache: None,
            color_mode: ColorMode::Never,
        },
        &mut warnings,
    ) {
        Ok(a) => a,
        Err(ref e) => {
            let mut buf = Vec::new();
            render_pipeline_error(e, file_label, code, &mut buf, ColorMode::Never, true);
            let msg = String::from_utf8_lossy(&buf);
            eprintln!("  FAIL {file_label} (mode: run)\n{}", indent(&msg));
            return false;
        }
    };

    let opts = RunOptions {
        file_path: file_label,
        jit_options: Default::default(),
        skip_tests: true,
    };

    if let Err(ref e) = compile_and_run(&analyzed, &opts) {
        let mut buf = Vec::new();
        render_pipeline_error(e, file_label, code, &mut buf, ColorMode::Never, true);
        let msg = String::from_utf8_lossy(&buf);
        eprintln!("  FAIL {file_label} (mode: run)\n{}", indent(&msg));
        return false;
    }
    true
}

/// Indent each line of a string for display.
fn indent(text: &str) -> String {
    text.lines()
        .map(|l| format!("    {l}"))
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

    // Install signal handler for JIT code
    vole::install_segfault_handler();

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

    let start = Instant::now();
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
            if check_block(block) {
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

    // Summary
    let elapsed = start.elapsed();
    println!();
    if failed == 0 {
        println!("All {total_blocks} code blocks passed in {elapsed:.2?}.");
        ExitCode::SUCCESS
    } else {
        println!("{passed} passed, {failed} failed out of {total_blocks} blocks in {elapsed:.2?}.");
        println!();
        println!("Failed blocks:");
        for loc in &failed_locations {
            println!("  {loc}");
        }
        ExitCode::FAILURE
    }
}
