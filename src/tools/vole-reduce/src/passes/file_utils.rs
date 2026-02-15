// passes/file_utils.rs
//! Shared file-system utilities used across multiple reduction passes.

use std::fs;
use std::path::{Path, PathBuf};

/// Discover all `.vole` files in the workspace result directory.
pub(super) fn discover_vole_files(result_dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    collect_vole_files_recursive(result_dir, &mut files)?;
    files.sort();
    Ok(files)
}

/// Recursively collect `.vole` files.
pub(super) fn collect_vole_files_recursive(
    dir: &Path,
    out: &mut Vec<PathBuf>,
) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("failed to read directory '{}': {e}", dir.display()))?;

    for entry in entries {
        let entry =
            entry.map_err(|e| format!("failed to read entry in '{}': {e}", dir.display()))?;
        let path = entry.path();

        if path.is_dir() {
            collect_vole_files_recursive(&path, out)?;
        } else if path.extension().is_some_and(|ext| ext == "vole") {
            out.push(path);
        }
    }
    Ok(())
}

pub(super) fn read_file(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| format!("failed to read '{}': {e}", path.display()))
}

pub(super) fn write_file(path: &Path, content: &str) -> Result<(), String> {
    fs::write(path, content).map_err(|e| format!("failed to write '{}': {e}", path.display()))
}

/// Format a path relative to the workspace result directory for display.
pub(super) fn relative_display(path: &Path, result_dir: &Path) -> String {
    path.strip_prefix(result_dir)
        .unwrap_or(path)
        .display()
        .to_string()
}

/// Recursively copy a directory tree.
pub(super) fn copy_dir_recursive(src: &Path, dst: &Path) -> Result<(), String> {
    fs::create_dir_all(dst)
        .map_err(|e| format!("failed to create directory '{}': {e}", dst.display()))?;

    let entries = fs::read_dir(src)
        .map_err(|e| format!("failed to read directory '{}': {e}", src.display()))?;

    for entry in entries {
        let entry =
            entry.map_err(|e| format!("failed to read entry in '{}': {e}", src.display()))?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());

        if src_path.is_dir() {
            copy_dir_recursive(&src_path, &dst_path)?;
        } else {
            fs::copy(&src_path, &dst_path).map_err(|e| {
                format!(
                    "failed to copy '{}' -> '{}': {e}",
                    src_path.display(),
                    dst_path.display()
                )
            })?;
        }
    }

    Ok(())
}
