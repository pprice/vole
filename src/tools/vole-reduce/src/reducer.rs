// reducer.rs
//! Reducer: orchestrates reduction passes over a workspace.
//!
//! The reducer owns the oracle, workspace paths, and reduction statistics.
//! Individual passes are implemented in the [`passes`](crate::passes) module
//! and invoked from here.

use std::path::{Path, PathBuf};

use crate::oracle::{Baseline, Oracle};
use crate::passes;
use crate::workspace::Workspace;

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Aggregate statistics collected across all reduction passes.
#[derive(Debug, Default)]
pub struct ReductionStats {
    /// Total number of oracle invocations.
    pub oracle_invocations: u32,
    /// Number of reductions that the oracle confirmed as Same.
    pub successful_reductions: u32,
    /// Total line count of all `.vole` files before reduction.
    pub total_lines_before: u64,
    /// Total line count of all `.vole` files after reduction.
    pub total_lines_after: u64,
}

// ---------------------------------------------------------------------------
// Reducer
// ---------------------------------------------------------------------------

/// Top-level reducer that drives all passes.
pub struct Reducer<'a> {
    pub oracle: &'a Oracle,
    pub workspace: &'a Workspace,
    pub file_path: String,
    pub dir_path: String,
    pub baseline: &'a Baseline,
    pub entrypoint: PathBuf,
    pub verbose: bool,
    pub stats: ReductionStats,
}

/// Arguments for constructing a [`Reducer`].
///
/// Bundled into a struct to keep the argument count manageable.
pub struct ReducerConfig<'a> {
    pub oracle: &'a Oracle,
    pub workspace: &'a Workspace,
    pub file_path: String,
    pub dir_path: String,
    pub baseline: &'a Baseline,
    pub entrypoint: PathBuf,
    pub verbose: bool,
}

impl<'a> Reducer<'a> {
    /// Create a new reducer from the given configuration.
    pub fn new(config: ReducerConfig<'a>) -> Self {
        Self {
            oracle: config.oracle,
            workspace: config.workspace,
            file_path: config.file_path,
            dir_path: config.dir_path,
            baseline: config.baseline,
            entrypoint: config.entrypoint,
            verbose: config.verbose,
            stats: ReductionStats::default(),
        }
    }

    /// Run all reduction passes in order.
    ///
    /// Currently only module elimination is implemented. Future passes
    /// (import trimming, statement elimination, etc.) will be added here.
    pub fn run(&mut self) -> Result<(), String> {
        self.stats.total_lines_before = count_vole_lines(&self.workspace.result)?;

        passes::module_elimination::run(self)?;

        self.stats.total_lines_after = count_vole_lines(&self.workspace.result)?;
        Ok(())
    }

    /// Print a summary of the reduction statistics.
    pub fn print_stats(&self) {
        println!("Reduction complete.");
        println!("  oracle invocations:    {}", self.stats.oracle_invocations);
        println!(
            "  successful reductions: {}",
            self.stats.successful_reductions
        );
        println!("  lines before:          {}", self.stats.total_lines_before);
        println!("  lines after:           {}", self.stats.total_lines_after);

        if self.stats.total_lines_before > 0 {
            let pct = 100.0
                - (self.stats.total_lines_after as f64 / self.stats.total_lines_before as f64)
                    * 100.0;
            println!("  reduction:             {pct:.1}%");
        }
        println!();
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
