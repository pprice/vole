// passes/single_file_collapse.rs
//! Pass 5: Single-file collapse.
//!
//! Attempts to merge all remaining `.vole` files into the entrypoint file.
//! This is a single all-or-nothing attempt: if inlining breaks the bug
//! reproduction, all files are restored from a pre-collapse snapshot.
//!
//! Import statements that reference project-local files are stripped (since
//! those modules are now inlined). Module-qualified references (e.g. `mod.Type`)
//! are NOT rewritten — if inlining breaks compilation, the oracle returns Pass
//! and we restore.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use regex::Regex;

use crate::oracle::MatchResult;
use crate::reducer::Reducer;

use super::file_utils::{
    copy_dir_recursive, discover_vole_files, read_file, relative_display, write_file,
};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the single-file collapse pass.
///
/// If only one `.vole` file remains, this pass is a no-op. Otherwise it
/// attempts to merge all non-entrypoint modules into the entrypoint file
/// and checks whether the bug still reproduces.
pub fn run(reducer: &mut Reducer<'_>) -> Result<(), String> {
    println!("Pass 5: single-file collapse");

    let vole_files = discover_vole_files(&reducer.workspace.result)?;

    if vole_files.len() <= 1 {
        println!("  Only 1 file remains — skipping.");
        println!();
        return Ok(());
    }

    let file_count = vole_files.len();
    let entrypoint_display = relative_display(&reducer.entrypoint, &reducer.workspace.result);
    println!(
        "  Attempting single-file collapse: merging {file_count} files into {entrypoint_display}",
    );

    // Snapshot all files before attempting collapse.
    let snapshot = snapshot_all_files(&vole_files)?;

    // Build the combined content and determine which files to remove.
    let combined = build_combined_content(&snapshot, &reducer.entrypoint)?;

    // Write combined file and remove non-entrypoint files.
    apply_collapse(&reducer.entrypoint, &combined, &snapshot)?;

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
            reducer.stats.successful_reductions += 1;
            println!("  Single-file collapse successful: {file_count} files \u{2192} 1 file",);
        }
        MatchResult::Different => {
            restore_all_files(&snapshot)?;
            save_divergent_snapshot(reducer, &result)?;
            println!(
                "  Single-file collapse produced different failure — saved divergent snapshot, \
                 keeping {file_count} files",
            );
        }
        MatchResult::Pass => {
            restore_all_files(&snapshot)?;
            println!(
                "  Single-file collapse failed: module boundary matters, \
                 keeping {file_count} files",
            );
        }
    }

    println!();
    Ok(())
}

// ---------------------------------------------------------------------------
// File snapshot
// ---------------------------------------------------------------------------

/// A snapshot of a single file's path and content.
struct FileSnapshot {
    path: PathBuf,
    content: String,
}

/// Read and snapshot all `.vole` files so they can be restored on failure.
fn snapshot_all_files(paths: &[PathBuf]) -> Result<Vec<FileSnapshot>, String> {
    let mut snapshots = Vec::with_capacity(paths.len());
    for path in paths {
        let content = read_file(path)?;
        snapshots.push(FileSnapshot {
            path: path.clone(),
            content,
        });
    }
    Ok(snapshots)
}

/// Restore all files from their snapshots.
///
/// Recreates any files that were deleted during the collapse attempt.
fn restore_all_files(snapshots: &[FileSnapshot]) -> Result<(), String> {
    for snap in snapshots {
        write_file(&snap.path, &snap.content)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Building combined content
// ---------------------------------------------------------------------------

/// Build the combined file content by merging non-entrypoint modules into
/// the entrypoint.
///
/// Returns the combined source string to write to the entrypoint.
fn build_combined_content(snapshots: &[FileSnapshot], entrypoint: &Path) -> Result<String, String> {
    let import_re = build_local_import_regex();

    // Collect stripped content from non-entrypoint files.
    let mut non_entry_content = String::new();
    let mut entrypoint_content = String::new();

    for snap in snapshots {
        if snap.path == entrypoint {
            entrypoint_content = strip_local_imports(&snap.content, &import_re);
        } else {
            let stripped = strip_local_imports(&snap.content, &import_re);
            if !stripped.trim().is_empty() {
                non_entry_content.push_str(&stripped);
                if !stripped.ends_with('\n') {
                    non_entry_content.push('\n');
                }
                non_entry_content.push('\n');
            }
        }
    }

    // Prepend non-entrypoint content above the entrypoint's content.
    let mut combined = String::with_capacity(non_entry_content.len() + entrypoint_content.len());
    if !non_entry_content.is_empty() {
        combined.push_str(&non_entry_content);
    }
    combined.push_str(&entrypoint_content);

    Ok(combined)
}

/// Build a regex matching import statements that reference local project files.
///
/// Matches patterns like:
///   let x = import "./foo.vole"
///   let { a, b } = import "./bar"
///
/// Does NOT match stdlib imports like `import "std:collections/map"`.
fn build_local_import_regex() -> Regex {
    Regex::new(r#"(?m)^[ \t]*let\s[^=]+=\s*import\s+"\./?[^"]*"\s*$"#)
        .expect("local import regex should compile")
}

/// Strip lines that are local file imports from the source content.
fn strip_local_imports(source: &str, import_re: &Regex) -> String {
    let mut result = String::with_capacity(source.len());
    for line in source.lines() {
        if !import_re.is_match(line) {
            result.push_str(line);
            result.push('\n');
        }
    }
    // Preserve trailing newline behavior.
    if !source.ends_with('\n') && result.ends_with('\n') {
        result.pop();
    }
    result
}

// ---------------------------------------------------------------------------
// Applying and reverting collapse
// ---------------------------------------------------------------------------

/// Write the combined content to the entrypoint and remove non-entrypoint files.
fn apply_collapse(
    entrypoint: &Path,
    combined: &str,
    snapshots: &[FileSnapshot],
) -> Result<(), String> {
    write_file(entrypoint, combined)?;

    for snap in snapshots {
        if snap.path != entrypoint {
            fs::remove_file(&snap.path)
                .map_err(|e| format!("failed to remove '{}': {e}", snap.path.display()))?;
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Divergent snapshot
// ---------------------------------------------------------------------------

/// Save a divergent failure snapshot for the collapse attempt.
fn save_divergent_snapshot(
    reducer: &Reducer<'_>,
    result: &crate::oracle::OracleResult,
) -> Result<(), String> {
    let snapshot_id = next_snapshot_id(&reducer.workspace.divergent)?;
    let snapshot_dir = reducer
        .workspace
        .divergent
        .join(format!("{snapshot_id:03}"));
    let files_dir = snapshot_dir.join("files");

    // Copy current workspace state (collapsed) into the snapshot.
    copy_dir_recursive(&reducer.workspace.result, &files_dir)?;

    let info = build_snapshot_info(result);
    let info_path = snapshot_dir.join("info.txt");
    fs::write(&info_path, info)
        .map_err(|e| format!("failed to write '{}': {e}", info_path.display()))?;

    Ok(())
}

/// Determine the next divergent snapshot number.
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

/// Build info.txt content for a collapse divergent snapshot.
fn build_snapshot_info(result: &crate::oracle::OracleResult) -> String {
    let timestamp = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    let mut info = "Divergent failure snapshot (single-file collapse)\n\n".to_string();
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
