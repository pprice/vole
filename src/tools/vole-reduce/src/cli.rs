// cli.rs
//! CLI argument parsing for vole-reduce.

use std::path::PathBuf;

use clap::{Parser, ValueEnum};

/// Test case minimizer for Vole compiler bugs.
///
/// Reduces a Vole test case to the smallest version that still reproduces
/// a specified bug. At least one oracle option (--stderr, --signal,
/// --exit-code, --timeout, or --predicate) must be provided.
#[derive(Parser, Debug)]
#[command(name = "vole-reduce")]
#[command(version = "0.1.0")]
#[command(about = "Test case minimizer for Vole compiler bugs")]
pub struct Cli {
    /// Path to the Vole file or directory to reduce
    #[arg(value_name = "PATH")]
    pub path: PathBuf,

    // -- Oracle options (at least one required) --
    /// Bug reproduces if stderr matches this regex
    #[arg(long, value_name = "REGEX")]
    pub stderr: Option<String>,

    /// Bug reproduces if process killed by this signal (e.g. 11 for segfault)
    #[arg(long, value_name = "NUM")]
    pub signal: Option<i32>,

    /// Bug reproduces if exit code matches
    #[arg(long, value_name = "CODE")]
    pub exit_code: Option<i32>,

    /// Bug reproduces if process hangs beyond N seconds
    #[arg(long, value_name = "SECS")]
    pub timeout: Option<f64>,

    /// Custom shell command oracle (exit 0 = bug reproduced)
    #[arg(long, value_name = "CMD")]
    pub predicate: Option<String>,

    // -- General options --
    /// Filter to a specific test (maps to `vole test --filter`)
    #[arg(long, value_name = "NAME")]
    pub test: Option<String>,

    /// Override the run command (default: cargo run -- test <path> --filter <test> --max-failures 1)
    #[arg(long, value_name = "CMD")]
    pub command: Option<String>,

    /// Output directory (default: <input>_reduced/)
    #[arg(long, value_name = "DIR")]
    pub output: Option<PathBuf>,

    /// Overwrite existing output directory
    #[arg(long)]
    pub force: bool,

    /// Safety limit on number of reduction iterations
    #[arg(long, default_value_t = 500)]
    pub max_iterations: u32,

    /// Log each reduction attempt
    #[arg(long)]
    pub verbose: bool,

    /// Oracle mode: 'strict' checks all specified oracles, 'loose' checks any
    #[arg(long, value_enum, default_value_t = OracleMode::Strict)]
    pub oracle_mode: OracleMode,
}

/// Oracle matching mode.
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum OracleMode {
    /// All specified oracle checks must pass (composite check)
    #[default]
    Strict,
    /// Any specified oracle check passing is sufficient
    Loose,
}

/// Returns true if at least one oracle option was specified.
pub fn has_oracle(cli: &Cli) -> bool {
    cli.stderr.is_some()
        || cli.signal.is_some()
        || cli.exit_code.is_some()
        || cli.timeout.is_some()
        || cli.predicate.is_some()
}

/// Validate the CLI arguments. Returns an error message if invalid.
pub fn validate(cli: &Cli) -> Result<(), String> {
    if !has_oracle(cli) {
        return Err("at least one oracle option is required\n\n\
             Specify how to detect the bug:\n  \
               --stderr <regex>     stderr matches a regex\n  \
               --signal <num>       process killed by signal (e.g. 11 for segfault)\n  \
               --exit-code <code>   process exits with specific code\n  \
               --timeout <secs>     process hangs beyond N seconds\n  \
               --predicate <cmd>    custom shell command (exit 0 = reproduced)"
            .to_string());
    }

    // Validate the stderr regex compiles
    if let Some(ref pattern) = cli.stderr {
        regex::Regex::new(pattern)
            .map_err(|e| format!("invalid --stderr regex '{}': {}", pattern, e))?;
    }

    // Validate timeout is positive
    if let Some(secs) = cli.timeout {
        if secs <= 0.0 {
            return Err(format!("--timeout must be positive, got {}", secs));
        }
    }

    // Validate input path exists
    if !cli.path.exists() {
        return Err(format!("input path does not exist: {}", cli.path.display()));
    }

    Ok(())
}
