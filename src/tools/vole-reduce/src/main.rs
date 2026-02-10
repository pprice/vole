// main.rs
//! vole-reduce: Test case minimizer for Vole compiler bugs.

mod cli;
mod oracle;
mod workspace;

use std::path::Path;
use std::process::ExitCode;

use clap::Parser;

use cli::{Cli, OracleMode};
use oracle::Oracle;

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
    let _baseline = oracle.establish_baseline(&ws.result, &file_path, &dir_path)?;

    println!("Ready to reduce. (Reduction passes not yet implemented.)");
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
