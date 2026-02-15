// passes/module_elimination.rs
//! Pass 1: Module elimination.
//!
//! Tries to remove entire `.vole` files from the workspace while preserving
//! the original bug. This is the highest-impact pass since stress-generated
//! repos often contain 20+ modules when only 1-3 are actually needed.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use crate::oracle::MatchResult;
use crate::reducer::Reducer;

use super::file_utils::copy_dir_recursive;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the module elimination pass.
///
/// Repeatedly scans all non-entrypoint `.vole` files, sorted by size
/// descending, and tries removing each one. Loops until a full sweep
/// makes no progress.
pub fn run(reducer: &mut Reducer<'_>) -> Result<(), String> {
    println!("Pass 1: module elimination");

    let mut round = 0u32;
    let mut total_removed = 0u32;
    let mut total_candidates = 0u32;

    loop {
        round += 1;
        let candidates = discover_candidates(&reducer.workspace.result, &reducer.entrypoint)?;

        if round == 1 {
            total_candidates = candidates.len() as u32;
            if candidates.is_empty() {
                println!("  No non-entrypoint modules found — skipping.");
                println!();
                return Ok(());
            }
            println!(
                "  Found {} non-entrypoint module(s), entrypoint: {}",
                candidates.len(),
                reducer.entrypoint.display(),
            );
        }

        let removed = try_remove_modules(reducer, &candidates)?;

        total_removed += removed;
        if removed == 0 {
            break;
        }

        if reducer.verbose {
            println!("  Round {round}: removed {removed} module(s), scanning again...");
        }
    }

    println!(
        "  Pass 1 complete: {total_removed}/{total_candidates} module(s) removed \
         ({round} round(s))",
    );
    println!();
    Ok(())
}

// ---------------------------------------------------------------------------
// Candidate discovery
// ---------------------------------------------------------------------------

/// A candidate module file, with its path and size in bytes.
struct Candidate {
    path: PathBuf,
    size: u64,
    line_count: u64,
}

/// Discover all non-entrypoint `.vole` files, sorted by size descending.
fn discover_candidates(result_dir: &Path, entrypoint: &Path) -> Result<Vec<Candidate>, String> {
    let mut candidates = Vec::new();

    collect_vole_files(result_dir, entrypoint, &mut candidates)?;

    // Sort by size descending — try removing biggest files first.
    candidates.sort_by(|a, b| b.size.cmp(&a.size));

    Ok(candidates)
}

/// Recursively collect `.vole` files under `dir`, excluding the entrypoint.
fn collect_vole_files(
    dir: &Path,
    entrypoint: &Path,
    out: &mut Vec<Candidate>,
) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("failed to read directory '{}': {e}", dir.display()))?;

    for entry in entries {
        let entry =
            entry.map_err(|e| format!("failed to read entry in '{}': {e}", dir.display()))?;
        let path = entry.path();

        if path.is_dir() {
            collect_vole_files(&path, entrypoint, out)?;
            continue;
        }

        if path.extension().is_some_and(|ext| ext == "vole") && path != entrypoint {
            let metadata = fs::metadata(&path)
                .map_err(|e| format!("failed to stat '{}': {e}", path.display()))?;
            let content = fs::read_to_string(&path)
                .map_err(|e| format!("failed to read '{}': {e}", path.display()))?;
            let line_count = content.lines().count() as u64;

            out.push(Candidate {
                path,
                size: metadata.len(),
                line_count,
            });
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Removal loop
// ---------------------------------------------------------------------------

/// Try removing each candidate module, returning how many were removed.
fn try_remove_modules(reducer: &mut Reducer<'_>, candidates: &[Candidate]) -> Result<u32, String> {
    let mut removed = 0u32;

    for candidate in candidates {
        // Skip files already removed in a previous round.
        if !candidate.path.exists() {
            continue;
        }

        let outcome = try_remove_one(reducer, candidate)?;

        match outcome {
            RemovalOutcome::Removed => removed += 1,
            RemovalOutcome::Needed | RemovalOutcome::Divergent => {}
        }
    }

    Ok(removed)
}

/// Outcome of attempting to remove a single module.
enum RemovalOutcome {
    /// Oracle said Same — file was successfully removed.
    Removed,
    /// Oracle said Pass — file is needed for the bug.
    Needed,
    /// Oracle said Different — divergent snapshot saved, file restored.
    Divergent,
}

/// Try removing a single module file and check the oracle.
fn try_remove_one(
    reducer: &mut Reducer<'_>,
    candidate: &Candidate,
) -> Result<RemovalOutcome, String> {
    let display_name = candidate
        .path
        .strip_prefix(&reducer.workspace.result)
        .unwrap_or(&candidate.path)
        .display();

    // Move the file to a temporary location (don't delete yet).
    let stash = stash_path(&candidate.path);
    fs::rename(&candidate.path, &stash).map_err(|e| {
        format!(
            "failed to stash '{}' -> '{}': {e}",
            candidate.path.display(),
            stash.display()
        )
    })?;

    // Run the oracle.
    let result = reducer.oracle.run(
        &reducer.workspace.result,
        &reducer.file_path,
        &reducer.dir_path,
    );
    reducer.stats.oracle_invocations += 1;

    let verdict = reducer.oracle.check(&result, reducer.baseline);

    match verdict {
        MatchResult::Same => {
            // Bug still reproduces — keep the file removed.
            fs::remove_file(&stash)
                .map_err(|e| format!("failed to remove stashed file '{}': {e}", stash.display()))?;
            reducer.stats.successful_reductions += 1;

            println!(
                "  Removed module: {display_name} ({} lines)",
                candidate.line_count,
            );
            Ok(RemovalOutcome::Removed)
        }

        MatchResult::Different => {
            // Different failure — save divergent snapshot, restore file.
            let snapshot_id = save_divergent_snapshot(reducer, candidate, &result)?;

            fs::rename(&stash, &candidate.path).map_err(|e| {
                format!(
                    "failed to restore '{}' from stash: {e}",
                    candidate.path.display()
                )
            })?;

            println!(
                "  Different failure after removing {display_name} \
                 — saved to divergent/{snapshot_id:03}/",
            );
            Ok(RemovalOutcome::Divergent)
        }

        MatchResult::Pass => {
            // Bug disappeared — this module is needed, restore it.
            fs::rename(&stash, &candidate.path).map_err(|e| {
                format!(
                    "failed to restore '{}' from stash: {e}",
                    candidate.path.display()
                )
            })?;

            if reducer.verbose {
                println!("  Kept module: {display_name} (bug disappears without it)",);
            }
            Ok(RemovalOutcome::Needed)
        }
    }
}

/// Compute a stash path for temporarily hiding a file.
///
/// Places the stash file alongside the original with a `.vole-reduce-stash`
/// extension so it won't be picked up as a Vole module.
fn stash_path(path: &Path) -> PathBuf {
    let mut stash = path.as_os_str().to_os_string();
    stash.push(".vole-reduce-stash");
    PathBuf::from(stash)
}

// ---------------------------------------------------------------------------
// Divergent snapshots
// ---------------------------------------------------------------------------

/// Save a divergent failure snapshot and return the snapshot number.
fn save_divergent_snapshot(
    reducer: &Reducer<'_>,
    candidate: &Candidate,
    result: &crate::oracle::OracleResult,
) -> Result<u32, String> {
    let snapshot_id = next_snapshot_id(&reducer.workspace.divergent)?;
    let snapshot_dir = reducer
        .workspace
        .divergent
        .join(format!("{snapshot_id:03}"));
    let files_dir = snapshot_dir.join("files");

    // Copy current workspace state (with the file removed) into snapshot.
    copy_dir_recursive(&reducer.workspace.result, &files_dir)?;

    // Write info.txt with context about what was removed and why.
    let info = build_snapshot_info(candidate, result, reducer);
    let info_path = snapshot_dir.join("info.txt");
    fs::write(&info_path, info)
        .map_err(|e| format!("failed to write '{}': {e}", info_path.display()))?;

    Ok(snapshot_id)
}

/// Determine the next divergent snapshot number by scanning existing entries.
fn next_snapshot_id(divergent_dir: &Path) -> Result<u32, String> {
    let mut max_id = 0u32;
    let entries = fs::read_dir(divergent_dir)
        .map_err(|e| format!("failed to read '{}': {e}", divergent_dir.display()))?;

    for entry in entries {
        let entry = entry
            .map_err(|e| format!("failed to read entry in '{}': {e}", divergent_dir.display()))?;
        if let Some(name) = entry.file_name().to_str()
            && let Ok(id) = name.parse::<u32>()
        {
            max_id = max_id.max(id);
        }
    }

    Ok(max_id + 1)
}

/// Build the info.txt content for a divergent snapshot.
fn build_snapshot_info(
    candidate: &Candidate,
    result: &crate::oracle::OracleResult,
    reducer: &Reducer<'_>,
) -> String {
    let display_name = candidate
        .path
        .strip_prefix(&reducer.workspace.result)
        .unwrap_or(&candidate.path)
        .display();

    let timestamp = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    let mut info = "Divergent failure snapshot\n\n".to_string();
    info.push_str(&format!("Removed: {display_name}\n"));
    info.push_str(&format!("Timestamp: {timestamp}\n\n"));

    info.push_str("Oracle result:\n");
    if let Some(code) = result.exit_code {
        info.push_str(&format!("  exit code: {code}\n"));
    }
    if let Some(signal) = result.signal {
        info.push_str(&format!("  signal:    {signal}\n"));
    }
    if result.timed_out {
        info.push_str("  timed out: yes\n");
    }
    if !result.stderr.is_empty() {
        let excerpt: String = result.stderr.chars().take(500).collect();
        info.push_str(&format!("  stderr:\n    {excerpt}\n"));
    }

    info
}
