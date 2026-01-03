// src/cli/args.rs

use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

/// Color output mode
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum ColorMode {
    /// Auto-detect based on terminal
    #[default]
    Auto,
    /// Always use colors
    Always,
    /// Never use colors
    Never,
}

/// Test output report mode
#[derive(Clone, Debug, Default, ValueEnum)]
pub enum ReportMode {
    /// Show all tests, reprint failures at end
    #[default]
    All,
    /// Show only failed tests
    Failures,
    /// Show only final summary
    Results,
}

/// Vole programming language compiler and runtime
#[derive(Parser)]
#[command(name = "vole")]
#[command(version = "0.1.0")]
#[command(about = "Vole programming language", long_about = None)]
pub struct Cli {
    /// Color output: auto, always, never
    #[arg(long, global = true, value_enum, default_value_t = ColorMode::Auto)]
    pub color: ColorMode,

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
    /// Check Vole source files for errors without running them
    Check {
        /// Paths to check (files, directories, or glob patterns)
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,
    },
    /// Run tests in Vole source files
    Test {
        /// Paths to test (files, directories, or glob patterns)
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,

        /// Filter tests by name (substring match)
        #[arg(short, long)]
        filter: Option<String>,

        /// Report mode: all (default), failures, results
        #[arg(short, long, value_enum, default_value_t = ReportMode::All)]
        report: ReportMode,

        /// Stop after N test failures (default: 100, 0 = no limit)
        #[arg(short = 'x', long, default_value_t = 100)]
        max_failures: u32,
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
