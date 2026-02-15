// passes/line_delta.rs
//! Pass 6: Line-based delta debugging.
//!
//! Language-agnostic line-level reduction applied to each surviving `.vole` file.
//! This pass runs *after* all AST-aware passes and catches anything they missed:
//! partial expressions, comments, blank lines, or code that doesn't even parse.
//!
//! **Phase A** — Chunk removal (binary search style):
//! Start with `chunk_size = lines.len() / 2` and try removing each contiguous
//! chunk. On success restart from the beginning at the same chunk size; on a
//! full sweep with no progress halve the chunk size. Stop when chunk size
//! reaches zero.
//!
//! **Phase B** — Individual line removal (last to first):
//! Try removing each non-blank line one at a time.

use std::path::Path;

use crate::oracle::MatchResult;
use crate::reducer::Reducer;

use super::file_utils::{discover_vole_files, read_file, relative_display, write_file};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the line-based delta debugging pass over all `.vole` files.
pub fn run(reducer: &mut Reducer<'_>) -> Result<(), String> {
    println!("Pass 6: line-based delta debugging");

    let vole_files = discover_vole_files(&reducer.workspace.result)?;

    if vole_files.is_empty() {
        println!("  No .vole files found — skipping.");
        println!();
        return Ok(());
    }

    let mut total_lines_removed: u32 = 0;
    let mut files_touched: u32 = 0;

    for path in &vole_files {
        if limit_reached(reducer) {
            println!("  Iteration limit reached — stopping early.");
            break;
        }

        let removed = reduce_file(reducer, path)?;
        if removed > 0 {
            files_touched += 1;
            total_lines_removed += removed;
        }
    }

    println!("  Pass 6 complete: {total_lines_removed} lines removed from {files_touched} file(s)",);
    println!();
    Ok(())
}

// ---------------------------------------------------------------------------
// Per-file reduction
// ---------------------------------------------------------------------------

/// Apply both phases of delta debugging to a single file.
///
/// Returns the total number of lines removed.
fn reduce_file(reducer: &mut Reducer<'_>, path: &Path) -> Result<u32, String> {
    let chunk_removed = phase_a_chunk_removal(reducer, path)?;
    let line_removed = phase_b_individual_removal(reducer, path)?;
    Ok(chunk_removed + line_removed)
}

// ---------------------------------------------------------------------------
// Phase A — Chunk removal
// ---------------------------------------------------------------------------

/// Binary-search-style chunk removal.
///
/// Returns the number of lines removed.
fn phase_a_chunk_removal(reducer: &mut Reducer<'_>, path: &Path) -> Result<u32, String> {
    let mut total_removed: u32 = 0;

    loop {
        if limit_reached(reducer) {
            break;
        }

        let lines = read_lines(path)?;
        let line_count = lines.len();
        if line_count <= 1 {
            break;
        }

        let removed = chunk_sweep(reducer, path, &lines)?;
        if removed == 0 {
            break;
        }
        total_removed += removed;
    }

    Ok(total_removed)
}

/// Run one full series of chunk sweeps, halving the chunk size on each
/// pass that makes no progress.
///
/// Returns the total number of lines removed across all chunk sizes.
fn chunk_sweep(
    reducer: &mut Reducer<'_>,
    path: &Path,
    initial_lines: &[String],
) -> Result<u32, String> {
    let mut total_removed: u32 = 0;
    let mut chunk_size = initial_lines.len() / 2;

    while chunk_size > 0 {
        if limit_reached(reducer) {
            break;
        }

        let removed = sweep_at_chunk_size(reducer, path, chunk_size)?;

        if removed > 0 {
            total_removed += removed;
            // Re-read to get updated line count and restart at the same
            // chunk size (clamped to the new length).
            let new_lines = read_lines(path)?;
            if new_lines.len() <= 1 {
                break;
            }
            chunk_size = chunk_size.min(new_lines.len() / 2);
            if chunk_size == 0 {
                break;
            }
        } else {
            chunk_size /= 2;
        }
    }

    Ok(total_removed)
}

/// Try removing every chunk of `chunk_size` consecutive lines in the file.
///
/// On the first successful removal, restart from the beginning (same chunk
/// size). Returns the total lines removed in this sweep.
fn sweep_at_chunk_size(
    reducer: &mut Reducer<'_>,
    path: &Path,
    chunk_size: usize,
) -> Result<u32, String> {
    let mut total_removed: u32 = 0;

    'restart: loop {
        if limit_reached(reducer) {
            break;
        }

        let lines = read_lines(path)?;
        let line_count = lines.len();

        if chunk_size > line_count {
            break;
        }

        let mut offset = 0;

        while offset + chunk_size <= line_count {
            if limit_reached(reducer) {
                return Ok(total_removed);
            }

            let removed_count = chunk_size as u32;
            let start_line_1indexed = offset + 1;
            let end_line_1indexed = offset + chunk_size;

            let modified = remove_line_range(&lines, offset, offset + chunk_size);
            let outcome = test_modification(reducer, path, &lines, &modified)?;

            match outcome {
                TrialOutcome::Accepted => {
                    println!(
                        "  Removed chunk: lines {start_line_1indexed}-{end_line_1indexed} \
                         ({removed_count} lines)",
                    );
                    total_removed += removed_count;
                    // Restart from beginning with same chunk size.
                    continue 'restart;
                }
                TrialOutcome::Divergent | TrialOutcome::Rejected => {
                    offset += 1;
                }
            }
        }

        // Full sweep at this chunk_size made no progress.
        break;
    }

    Ok(total_removed)
}

// ---------------------------------------------------------------------------
// Phase B — Individual line removal
// ---------------------------------------------------------------------------

/// Remove individual lines from last to first, skipping blank lines.
///
/// Returns the number of lines removed.
fn phase_b_individual_removal(reducer: &mut Reducer<'_>, path: &Path) -> Result<u32, String> {
    let mut total_removed: u32 = 0;

    // We iterate backwards through line indices. After each successful
    // removal we re-read the file so indices stay valid.
    loop {
        if limit_reached(reducer) {
            break;
        }

        let lines = read_lines(path)?;
        let removed = single_line_sweep(reducer, path, &lines)?;
        if removed == 0 {
            break;
        }
        total_removed += removed;
    }

    Ok(total_removed)
}

/// Sweep through lines from last to first, trying to remove each non-blank
/// line individually.
///
/// Returns the number of lines removed. On the first successful removal we
/// return immediately so the caller can re-read the file.
fn single_line_sweep(
    reducer: &mut Reducer<'_>,
    path: &Path,
    lines: &[String],
) -> Result<u32, String> {
    // Iterate from last to first.
    for idx in (0..lines.len()).rev() {
        if limit_reached(reducer) {
            return Ok(0);
        }

        // Skip blank/whitespace-only lines — not worth an oracle call.
        if lines[idx].trim().is_empty() {
            continue;
        }

        let modified = remove_line_range(lines, idx, idx + 1);
        let outcome = test_modification(reducer, path, lines, &modified)?;

        match outcome {
            TrialOutcome::Accepted => {
                let line_1indexed = idx + 1;
                let content_preview = truncate_line(&lines[idx], 60);
                println!("  Removed line {line_1indexed}: \"{content_preview}\"");
                return Ok(1);
            }
            TrialOutcome::Divergent | TrialOutcome::Rejected => {}
        }
    }

    Ok(0)
}

// ---------------------------------------------------------------------------
// Oracle trial
// ---------------------------------------------------------------------------

/// Outcome of trying a single modification.
enum TrialOutcome {
    /// Oracle said Same — keep the modification.
    Accepted,
    /// Oracle said Pass — revert.
    Rejected,
    /// Oracle said Different — revert.
    Divergent,
}

/// Write `modified_lines` to `path`, run the oracle, and restore `original_lines`
/// if needed.
fn test_modification(
    reducer: &mut Reducer<'_>,
    path: &Path,
    original_lines: &[String],
    modified_lines: &[String],
) -> Result<TrialOutcome, String> {
    let modified_content = join_lines(modified_lines);
    write_file(path, &modified_content)?;

    let result = reducer.oracle.run(
        &reducer.workspace.result,
        &reducer.file_path,
        &reducer.dir_path,
    );
    reducer.stats.oracle_invocations += 1;

    let verdict = reducer.oracle.check(&result, reducer.baseline);

    match verdict {
        MatchResult::Same => {
            reducer.stats.successful_reductions += 1;
            Ok(TrialOutcome::Accepted)
        }
        MatchResult::Pass => {
            let original_content = join_lines(original_lines);
            write_file(path, &original_content)?;
            Ok(TrialOutcome::Rejected)
        }
        MatchResult::Different => {
            let original_content = join_lines(original_lines);
            write_file(path, &original_content)?;

            if reducer.verbose {
                let display_name = relative_display(path, &reducer.workspace.result);
                println!("  Different failure while reducing lines in {display_name}");
            }
            Ok(TrialOutcome::Divergent)
        }
    }
}

// ---------------------------------------------------------------------------
// Line manipulation helpers
// ---------------------------------------------------------------------------

/// Read a file into a vector of lines (preserving content but not newlines).
fn read_lines(path: &Path) -> Result<Vec<String>, String> {
    let content = read_file(path)?;
    Ok(content.lines().map(String::from).collect())
}

/// Remove lines in the range `[start, end)` (0-indexed) from the line vector.
fn remove_line_range(lines: &[String], start: usize, end: usize) -> Vec<String> {
    let mut result = Vec::with_capacity(lines.len().saturating_sub(end - start));
    result.extend_from_slice(&lines[..start]);
    result.extend_from_slice(&lines[end..]);
    result
}

/// Join lines back into a single string with newline separators.
fn join_lines(lines: &[String]) -> String {
    if lines.is_empty() {
        return String::new();
    }
    let mut result = lines.join("\n");
    result.push('\n');
    result
}

/// Truncate a line for display, appending "..." if it exceeds `max_len`.
fn truncate_line(line: &str, max_len: usize) -> String {
    let trimmed = line.trim();
    if trimmed.len() <= max_len {
        trimmed.to_string()
    } else {
        format!("{}...", &trimmed[..max_len.saturating_sub(3)])
    }
}

// ---------------------------------------------------------------------------
// Limit check
// ---------------------------------------------------------------------------

/// Returns `true` if the oracle invocation limit has been reached.
fn limit_reached(reducer: &Reducer<'_>) -> bool {
    reducer.stats.oracle_invocations >= reducer.max_iterations
}
