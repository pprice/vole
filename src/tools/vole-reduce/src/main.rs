// main.rs
//! vole-reduce: Test case minimizer for Vole compiler bugs.

mod cli;
mod oracle;
mod passes;
mod reducer;
mod workspace;

use std::path::Path;
use std::process::ExitCode;

use clap::Parser;

use cli::{Cli, OracleMode};
use oracle::Oracle;
use reducer::{Reducer, ReducerConfig};

fn print_summary(cli: &Cli, ws: &workspace::Workspace, oracle: &Oracle) {
    println!("vole-reduce: Test case minimizer");
    println!();
    println!("  input:          {}", cli.path.display());
    println!("  output:         {}", ws.root.display());
    println!("  max iterations: {}", cli.max_iterations);
    println!(
        "  oracle mode:    {}",
        match cli.oracle_mode {
            OracleMode::Strict => "strict",
            OracleMode::Loose => "loose",
        }
    );
    println!();

    // Oracle summary
    println!("  oracles:");
    if let Some(ref pattern) = cli.stderr {
        println!("    stderr regex: {}", pattern);
    }
    if let Some(signal) = cli.signal {
        println!("    signal:       {}", signal);
    }
    if let Some(code) = cli.exit_code {
        println!("    exit code:    {}", code);
    }
    if let Some(secs) = cli.timeout {
        println!("    timeout:      {}s", secs);
    }
    if let Some(ref cmd) = cli.predicate {
        println!("    predicate:    {}", cmd);
    }
    println!();

    // Command
    println!("  command:        {}", oracle.command_template());
    if let Some(ref name) = cli.test {
        println!("  test filter:    {}", name);
    }
    println!();

    // Workspace summary
    println!("  workspace:");
    println!("    original:     {}", ws.original.display());
    println!("    result:       {}", ws.result.display());
    println!("    divergent:    {}", ws.divergent.display());
    println!("    log:          {}", ws.log.display());
    println!();
}

/// Resolve the `{file}` placeholder value.
///
/// If the input was a single file, returns the corresponding path inside the
/// workspace result directory. If it was a directory, returns the result dir
/// itself.
fn resolve_file_placeholder(input: &Path, result_dir: &Path) -> String {
    if input.is_file()
        && let Some(name) = input.file_name()
    {
        return result_dir.join(name).display().to_string();
    }
    result_dir.display().to_string()
}

/// Resolve the entrypoint file inside the workspace result directory.
///
/// If the user pointed at a specific `.vole` file, the entrypoint is that
/// file's copy inside `result/`. If the user pointed at a directory, we look
/// for a `main.vole` inside the result directory.
fn resolve_entrypoint(input: &Path, result_dir: &Path) -> Result<std::path::PathBuf, String> {
    if input.is_file()
        && let Some(name) = input.file_name()
    {
        let entry = result_dir.join(name);
        if entry.exists() {
            return Ok(entry);
        }
        return Err(format!(
            "entrypoint file not found in workspace: {}",
            entry.display()
        ));
    }

    // Directory input — look for main.vole.
    let main_vole = result_dir.join("main.vole");
    if main_vole.exists() {
        return Ok(main_vole);
    }

    // Fall back to any single .vole file if there's only one.
    let vole_files: Vec<_> = std::fs::read_dir(result_dir)
        .map_err(|e| format!("failed to read '{}': {e}", result_dir.display()))?
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "vole"))
        .collect();

    if vole_files.len() == 1 {
        return Ok(vole_files[0].path());
    }

    Err(format!(
        "cannot determine entrypoint: no main.vole found in '{}' \
         and there are {} .vole files. Use a file path instead of a directory.",
        result_dir.display(),
        vole_files.len()
    ))
}

fn run() -> Result<(), String> {
    let cli = Cli::parse();
    cli::validate(&cli)?;

    let ws = workspace::setup(&cli.path, cli.output.as_deref(), cli.force)?;
    let oracle = Oracle::from_cli(&cli)?;

    print_summary(&cli, &ws, &oracle);

    // Resolve placeholder values for the command template.
    let file_path = resolve_file_placeholder(&cli.path, &ws.result);
    let dir_path = ws.result.display().to_string();

    // Establish baseline against the original (unmodified) working copy.
    let baseline = oracle.establish_baseline(&ws.result, &file_path, &dir_path)?;

    // Resolve entrypoint: the specific file inside result/ that the user targeted.
    let entrypoint = resolve_entrypoint(&cli.path, &ws.result)?;

    let config = ReducerConfig {
        oracle: &oracle,
        workspace: &ws,
        file_path,
        dir_path,
        baseline: &baseline,
        entrypoint,
        verbose: cli.verbose,
    };
    let mut reducer = Reducer::new(config);
    reducer.run()?;
    reducer.print_stats();

    println!("Result: {}", ws.result.display());
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("error: {}", msg);
            ExitCode::FAILURE
        }
    }
}
