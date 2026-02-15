// reducer.rs
//! Reducer: orchestrates reduction passes over a workspace.
//!
//! The reducer owns the oracle, workspace paths, and reduction statistics.
//! Individual passes are implemented in the [`passes`](crate::passes) module
//! and invoked from here.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use crate::oracle::{Baseline, Oracle};
use crate::passes;
use crate::workspace::Workspace;

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Aggregate statistics collected across all reduction passes.
#[derive(Debug, Default)]
pub(crate) struct ReductionStats {
    /// Total number of oracle invocations.
    pub(crate) oracle_invocations: u32,
    /// Number of reductions that the oracle confirmed as Same.
    pub(crate) successful_reductions: u32,
    /// Total line count of all `.vole` files before reduction.
    pub(crate) total_lines_before: u64,
    /// Total line count of all `.vole` files after reduction.
    pub(crate) total_lines_after: u64,
    /// Total number of `.vole` files before reduction.
    pub(crate) files_before: u32,
    /// Total number of `.vole` files after reduction.
    pub(crate) files_after: u32,
    /// Number of divergent failure snapshots saved.
    pub(crate) divergent_failures: u32,
    /// Total wall-clock time spent in oracle invocations.
    pub(crate) total_oracle_time: Duration,
}

// ---------------------------------------------------------------------------
// Reducer
// ---------------------------------------------------------------------------

/// Top-level reducer that drives all passes.
pub(crate) struct Reducer<'a> {
    pub(crate) oracle: &'a Oracle,
    pub(crate) workspace: &'a Workspace,
    pub(crate) file_path: String,
    pub(crate) dir_path: String,
    pub(crate) baseline: &'a Baseline,
    pub(crate) entrypoint: PathBuf,
    pub(crate) test_filter: Option<String>,
    pub(crate) verbose: bool,
    pub(crate) max_iterations: u32,
    pub(crate) stats: ReductionStats,
}

/// Arguments for constructing a [`Reducer`].
///
/// Bundled into a struct to keep the argument count manageable.
pub(crate) struct ReducerConfig<'a> {
    pub(crate) oracle: &'a Oracle,
    pub(crate) workspace: &'a Workspace,
    pub(crate) file_path: String,
    pub(crate) dir_path: String,
    pub(crate) baseline: &'a Baseline,
    pub(crate) entrypoint: PathBuf,
    pub(crate) test_filter: Option<String>,
    pub(crate) verbose: bool,
    pub(crate) max_iterations: u32,
}

impl<'a> Reducer<'a> {
    /// Create a new reducer from the given configuration.
    pub(crate) fn new(config: ReducerConfig<'a>) -> Self {
        Self {
            oracle: config.oracle,
            workspace: config.workspace,
            file_path: config.file_path,
            dir_path: config.dir_path,
            baseline: config.baseline,
            entrypoint: config.entrypoint,
            test_filter: config.test_filter,
            verbose: config.verbose,
            max_iterations: config.max_iterations,
            stats: ReductionStats::default(),
        }
    }

    /// Run all reduction passes in order.
    pub(crate) fn run(&mut self) -> Result<(), String> {
        self.stats.total_lines_before = count_vole_lines(&self.workspace.result)?;
        self.stats.files_before = count_vole_files(&self.workspace.result)?;

        let start = Instant::now();

        passes::module_elimination::run(self)?;
        passes::import_trimming::run(self)?;
        passes::decl_elimination::run(self)?;
        passes::body_reduction::run(self)?;
        passes::single_file_collapse::run(self)?;
        passes::line_delta::run(self)?;

        self.stats.total_oracle_time = start.elapsed();
        self.stats.total_lines_after = count_vole_lines(&self.workspace.result)?;
        self.stats.files_after = count_vole_files(&self.workspace.result)?;
        self.stats.divergent_failures = count_divergent_snapshots(&self.workspace.divergent)?;
        Ok(())
    }

    /// Print a summary of the reduction statistics.
    pub(crate) fn print_stats(&self) {
        let s = &self.stats;
        println!("--- Reduction Summary ---");
        println!();

        // Lines
        print!(
            "  Lines:               {} -> {}",
            s.total_lines_before, s.total_lines_after
        );
        if s.total_lines_before > 0 {
            let pct = 100.0 - (s.total_lines_after as f64 / s.total_lines_before as f64) * 100.0;
            println!(" ({pct:.1}% reduction)");
        } else {
            println!();
        }

        // Files
        println!(
            "  Files:               {} -> {}",
            s.files_before, s.files_after
        );

        // Oracle
        println!(
            "  Oracle invocations:  {} ({:.1}s total)",
            s.oracle_invocations,
            s.total_oracle_time.as_secs_f64(),
        );
        println!("  Successful removals: {}", s.successful_reductions);

        // Divergent failures
        if s.divergent_failures > 0 {
            println!("  Divergent failures:  {}", s.divergent_failures);
        }

        // Result path
        println!("  Result:              {}", self.workspace.result.display());
        println!();
    }

    /// Format a summary string suitable for writing to the log file.
    pub(crate) fn format_log_summary(&self) -> String {
        let s = &self.stats;
        let mut out = String::new();
        out.push_str("--- Reduction Summary ---\n\n");

        out.push_str(&format!(
            "  Lines:               {} -> {}",
            s.total_lines_before, s.total_lines_after,
        ));
        if s.total_lines_before > 0 {
            let pct = 100.0 - (s.total_lines_after as f64 / s.total_lines_before as f64) * 100.0;
            out.push_str(&format!(" ({pct:.1}% reduction)"));
        }
        out.push('\n');
        out.push_str(&format!(
            "  Files:               {} -> {}\n",
            s.files_before, s.files_after,
        ));
        out.push_str(&format!(
            "  Oracle invocations:  {} ({:.1}s total)\n",
            s.oracle_invocations,
            s.total_oracle_time.as_secs_f64(),
        ));
        out.push_str(&format!(
            "  Successful removals: {}\n",
            s.successful_reductions,
        ));
        if s.divergent_failures > 0 {
            out.push_str(&format!(
                "  Divergent failures:  {}\n",
                s.divergent_failures,
            ));
        }
        out.push_str(&format!(
            "  Result:              {}\n",
            self.workspace.result.display(),
        ));
        out
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Count total lines across all `.vole` files in a directory tree.
fn count_vole_lines(dir: &Path) -> Result<u64, String> {
    let mut total: u64 = 0;
    for entry in walkdir(dir)? {
        if entry.extension().is_some_and(|ext| ext == "vole") {
            let content = std::fs::read_to_string(&entry)
                .map_err(|e| format!("failed to read '{}': {e}", entry.display()))?;
            total += content.lines().count() as u64;
        }
    }
    Ok(total)
}

/// Count `.vole` files in a directory tree.
fn count_vole_files(dir: &Path) -> Result<u32, String> {
    let mut count: u32 = 0;
    for entry in walkdir(dir)? {
        if entry.extension().is_some_and(|ext| ext == "vole") {
            count += 1;
        }
    }
    Ok(count)
}

/// Count divergent snapshot directories.
fn count_divergent_snapshots(divergent_dir: &Path) -> Result<u32, String> {
    if !divergent_dir.exists() {
        return Ok(0);
    }
    let entries = std::fs::read_dir(divergent_dir)
        .map_err(|e| format!("failed to read '{}': {e}", divergent_dir.display()))?;
    let mut count: u32 = 0;
    for entry in entries {
        let entry = entry
            .map_err(|e| format!("failed to read entry in '{}': {e}", divergent_dir.display()))?;
        if entry.path().is_dir() {
            count += 1;
        }
    }
    Ok(count)
}

/// Recursively collect all file paths under `dir`.
fn walkdir(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    walk_recursive(dir, &mut files)?;
    Ok(files)
}

fn walk_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir)
        .map_err(|e| format!("failed to read directory '{}': {e}", dir.display()))?;

    for entry in entries {
        let entry =
            entry.map_err(|e| format!("failed to read entry in '{}': {e}", dir.display()))?;
        let path = entry.path();
        if path.is_dir() {
            walk_recursive(&path, out)?;
        } else {
            out.push(path);
        }
    }
    Ok(())
}
