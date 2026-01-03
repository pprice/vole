// src/bin/vole.rs

use clap::Parser;
use std::process::ExitCode;

use vole::cli::Cli;
use vole::cli::Commands;
use vole::commands::check::check_file;
use vole::commands::run::run_file;
use vole::commands::test::run_tests;

fn main() -> ExitCode {
    let cli = Cli::parse();

    match cli.command {
        Commands::Run { file } => run_file(&file),
        Commands::Check { file } => check_file(&file),
        Commands::Test { paths } => run_tests(&paths),
        Commands::Inspect { .. } => todo!("inspect command not yet implemented"),
    }
}
