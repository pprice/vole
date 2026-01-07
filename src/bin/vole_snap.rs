// src/bin/vole_snap.rs
//! Snapshot testing CLI for Vole.

use std::io::IsTerminal;
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use vole::snap::{bless_tests, run_tests};

#[derive(Parser)]
#[command(name = "vole-snap")]
#[command(version = "0.1.0")]
#[command(about = "Snapshot testing for Vole")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run tests and compare against snapshots
    Test {
        /// Paths to test (files, directories, or glob patterns)
        #[arg(value_name = "PATTERNS", required = true)]
        patterns: Vec<String>,

        /// Include underscore-prefixed files (normally skipped)
        #[arg(long)]
        include_skipped: bool,
    },
    /// Create or update snapshot files
    Bless {
        /// Paths to bless (files, directories, or glob patterns)
        #[arg(value_name = "PATTERNS", required = true)]
        patterns: Vec<String>,

        /// Include underscore-prefixed files (normally skipped)
        #[arg(long)]
        include_skipped: bool,
    },
}

fn main() -> ExitCode {
    unsafe {
        std::env::set_var("RUST_BACKTRACE", "1");
    }
    let cli = Cli::parse();
    let use_color = std::io::stdout().is_terminal();

    match cli.command {
        Commands::Test {
            patterns,
            include_skipped,
        } => {
            let summary = run_tests(&patterns, include_skipped, use_color);

            // Print summary
            println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

            if use_color {
                print!("\x1b[32m{} passed\x1b[0m", summary.passed);
                if summary.failed > 0 {
                    print!("  \x1b[31m{} failed\x1b[0m", summary.failed);
                }
                if summary.new > 0 {
                    print!("  \x1b[33m{} new\x1b[0m", summary.new);
                }
            } else {
                print!("{} passed", summary.passed);
                if summary.failed > 0 {
                    print!("  {} failed", summary.failed);
                }
                if summary.new > 0 {
                    print!("  {} new", summary.new);
                }
            }
            println!();

            if !summary.failed_tests.is_empty() {
                println!("\nFailed:");
                for path in &summary.failed_tests {
                    println!("  {}", path);
                }
            }

            if !summary.new_tests.is_empty() {
                println!("\nNew (run 'vole-snap bless' to create snapshots):");
                for path in &summary.new_tests {
                    println!("  {}", path);
                }
            }

            // Exit codes: 0 = pass, 1 = fail, 2 = new
            if summary.failed > 0 {
                ExitCode::FAILURE
            } else if summary.new > 0 {
                ExitCode::from(2)
            } else {
                ExitCode::SUCCESS
            }
        }
        Commands::Bless {
            patterns,
            include_skipped,
        } => {
            let blessed = bless_tests(&patterns, include_skipped, use_color);

            println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
            if use_color {
                println!("\x1b[32m{} blessed\x1b[0m", blessed);
            } else {
                println!("{} blessed", blessed);
            }

            ExitCode::SUCCESS
        }
    }
}
