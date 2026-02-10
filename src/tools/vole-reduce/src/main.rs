// main.rs
//! vole-reduce: Test case minimizer for Vole compiler bugs.

mod cli;
mod workspace;

use std::process::ExitCode;

use clap::Parser;

use cli::{Cli, OracleMode};

fn print_summary(cli: &Cli, ws: &workspace::Workspace) {
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

    // Command summary
    if let Some(ref cmd) = cli.command {
        println!("  command:        {}", cmd);
    } else {
        let filter = cli.test.as_deref().unwrap_or("*");
        println!(
            "  command:        cargo run -- test <path> --filter {} --max-failures 1",
            filter
        );
    }
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
}

fn run() -> Result<(), String> {
    let cli = Cli::parse();
    cli::validate(&cli)?;

    let ws = workspace::setup(&cli.path, cli.output.as_deref(), cli.force)?;

    print_summary(&cli, &ws);
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
