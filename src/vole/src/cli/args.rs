// src/cli/args.rs

use clap::{Args, Parser, Subcommand, ValueEnum};
use std::ffi::OsString;
use std::path::PathBuf;

use crate::commands::version::version_string;

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
#[command(version = version_string())]
#[command(about = "Vole programming language", long_about = None)]
pub struct Cli {
    /// Color output: auto, always, never
    #[arg(long, global = true, hide = true, value_enum, default_value_t = ColorMode::Auto)]
    pub color: ColorMode,

    /// Optimize for faster execution (disables verification, enables optimizations)
    #[arg(long, global = true, hide = true)]
    pub release: bool,

    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Run a Vole source file
    #[command(visible_alias = "r")]
    Run {
        /// Path to the .vole file to execute
        #[arg(value_name = "FILE")]
        file: PathBuf,

        /// Project root directory (overrides auto-detection)
        #[arg(long, value_name = "PATH")]
        root: Option<PathBuf>,
    },
    /// Check Vole source files for errors without running them
    #[command(visible_alias = "c")]
    Check {
        /// Paths to check (files, directories, or glob patterns)
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,
    },
    /// Run tests in Vole source files
    #[command(visible_alias = "t")]
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

        /// Include underscore-prefixed files (normally skipped)
        #[arg(long)]
        include_skipped: bool,

        /// Project root directory (overrides auto-detection)
        #[arg(long, value_name = "PATH")]
        root: Option<PathBuf>,
    },
    /// Inspect compilation output (AST, IR)
    #[command(visible_alias = "i")]
    Inspect {
        /// What to inspect: ast, ir, mir
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

        /// Show all functions including prelude (for mir)
        #[arg(long)]
        all: bool,
    },
    /// Show version information
    Version,
    /// Benchmark commands
    Bench(BenchArgs),
    /// Format Vole source files
    #[command(visible_alias = "f")]
    Fmt {
        /// Paths to format (files, directories, or glob patterns). Use "-" for stdin.
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,

        /// Check if files are formatted (exit 1 if not, don't modify)
        #[arg(long)]
        check: bool,

        /// Write to stdout instead of modifying files in-place
        #[arg(long)]
        stdout: bool,
    },

    /// Run a .vole file directly (e.g. `vole file.vole` or via shebang)
    #[command(external_subcommand)]
    External(Vec<OsString>),
}

#[derive(Args)]
pub struct BenchArgs {
    /// Run even on debug builds
    #[arg(long)]
    pub force: bool,

    #[command(subcommand)]
    pub command: BenchCommands,
}

#[derive(Subcommand)]
pub enum BenchCommands {
    /// Run benchmarks with timing statistics
    Run {
        /// Paths to benchmark (files, directories, or glob patterns)
        #[arg(value_name = "PATHS", required = true)]
        paths: Vec<String>,

        /// Number of runtime iterations (default: 5)
        #[arg(short = 'n', long, default_value_t = 5)]
        iterations: u32,

        /// Warmup iterations before measuring (default: 1)
        #[arg(short, long, default_value_t = 1)]
        warmup: u32,

        /// Save JSON results to file
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,

        /// Show per-phase compile timing
        #[arg(long)]
        detailed: bool,
    },
    /// Compare benchmark results against a baseline
    Compare {
        /// Baseline JSON file to compare against
        #[arg(value_name = "BASELINE")]
        baseline: PathBuf,

        /// Save new results as baseline
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
    },
}

#[derive(Clone, Debug, ValueEnum)]
pub enum InspectType {
    Ast,
    Ir,
    Mir,
}
