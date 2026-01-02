// src/cli/args.rs

use clap::{Parser, Subcommand};
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
    /// Run tests in Vole source files
    Test {
        /// Paths to test (files, directories, or glob patterns)
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,
    },
}
