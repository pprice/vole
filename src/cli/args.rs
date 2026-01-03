// src/cli/args.rs

use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

/// Vole programming language compiler and runtime
#[derive(Parser)]
#[command(name = "vole")]
#[command(version = "0.1.0")]
#[command(about = "Vole programming language", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Run a Vole source file
    Run {
        /// Path to the .vole file to execute
        #[arg(value_name = "FILE")]
        file: PathBuf,
    },
    /// Check a Vole source file for errors without running it
    Check {
        /// Path to the .vole file to check
        #[arg(value_name = "FILE")]
        file: PathBuf,
    },
    /// Run tests in Vole source files
    Test {
        /// Paths to test (files, directories, or glob patterns)
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,
    },
    /// Inspect compilation output (AST, IR)
    Inspect {
        /// What to inspect: ast, ir
        #[arg(value_name = "TYPE")]
        inspect_type: InspectType,

        /// Paths to inspect (files or glob patterns)
        #[arg(value_name = "FILES", required = true)]
        files: Vec<String>,

        /// Exclude test blocks from output
        #[arg(long)]
        no_tests: bool,

        /// Include imports: "project" or "all" (not yet implemented)
        #[arg(long)]
        imports: Option<String>,
    },
}

#[derive(Clone, Debug, ValueEnum)]
pub enum InspectType {
    Ast,
    Ir,
}
