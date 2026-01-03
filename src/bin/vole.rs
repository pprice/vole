// src/bin/vole.rs

use clap::Parser;
use std::process::ExitCode;

use vole::cli::{Cli, Commands};
use vole::commands::check::check_files;
use vole::commands::inspect::inspect_files;
use vole::commands::run::run_file;
use vole::commands::test::run_tests;
use vole::commands::version::print_version;
use vole::errors::set_color_mode;

fn main() -> ExitCode {
    let cli = Cli::parse();

    // Set global color mode before any output
    set_color_mode(cli.color);

    match cli.command {
        Commands::Run { file } => run_file(&file),
        Commands::Check { paths } => check_files(&paths),
        Commands::Test {
            paths,
            filter,
            report,
            max_failures,
        } => run_tests(&paths, filter.as_deref(), report, max_failures, cli.color),
        Commands::Inspect {
            inspect_type,
            files,
            no_tests,
            imports,
        } => inspect_files(&files, inspect_type, no_tests, imports.as_deref()),
        Commands::Version => print_version(),
    }
}
