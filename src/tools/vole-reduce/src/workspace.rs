// workspace.rs
//! Working directory setup for vole-reduce.
//!
//! Creates the output directory structure used during reduction:
//!   <output>/original/   - pristine copy of the input
//!   <output>/result/     - working copy mutated during reduction
//!   <output>/divergent/  - variants that changed behavior unexpectedly
//!   <output>/log.txt     - reduction log

use std::fs;
use std::path::{Path, PathBuf};

/// Resolved workspace paths.
#[derive(Debug)]
pub struct Workspace {
    /// Root output directory.
    pub root: PathBuf,
    /// Pristine copy of the original input.
    pub original: PathBuf,
    /// Working copy that gets mutated during reduction.
    pub result: PathBuf,
    /// Variants that changed behavior unexpectedly.
    pub divergent: PathBuf,
    /// Reduction log file.
    pub log: PathBuf,
}

/// Determine the input directory to copy.
///
/// If the input path is a file, returns its parent directory.
/// If it is a directory, returns it directly.
fn resolve_input_dir(path: &Path) -> Result<PathBuf, String> {
    let canonical = path
        .canonicalize()
        .map_err(|e| format!("failed to resolve input path '{}': {}", path.display(), e))?;

    if canonical.is_file() {
        canonical.parent().map(|p| p.to_path_buf()).ok_or_else(|| {
            format!(
                "input file has no parent directory: {}",
                canonical.display()
            )
        })
    } else {
        Ok(canonical)
    }
}

/// Compute the default output path by appending `_reduced` to the input path.
fn default_output_path(input: &Path) -> Result<PathBuf, String> {
    let canonical = input
        .canonicalize()
        .map_err(|e| format!("failed to resolve input path '{}': {}", input.display(), e))?;

    // Use the directory itself (or file's parent) as the base for naming
    let base = if canonical.is_file() {
        canonical
            .parent()
            .ok_or_else(|| {
                format!(
                    "input file has no parent directory: {}",
                    canonical.display()
                )
            })?
            .to_path_buf()
    } else {
        canonical
    };

    let dir_name = base
        .file_name()
        .ok_or_else(|| format!("cannot determine directory name from: {}", base.display()))?;

    let mut output_name = dir_name.to_os_string();
    output_name.push("_reduced");

    let parent = base
        .parent()
        .ok_or_else(|| format!("cannot determine parent directory from: {}", base.display()))?;

    Ok(parent.join(output_name))
}

/// Recursively copy a directory tree from `src` to `dst`.
fn copy_dir_recursive(src: &Path, dst: &Path) -> Result<(), String> {
    fs::create_dir_all(dst)
        .map_err(|e| format!("failed to create directory '{}': {}", dst.display(), e))?;

    let entries = fs::read_dir(src)
        .map_err(|e| format!("failed to read directory '{}': {}", src.display(), e))?;

    for entry in entries {
        let entry =
            entry.map_err(|e| format!("failed to read entry in '{}': {}", src.display(), e))?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());

        if src_path.is_dir() {
            copy_dir_recursive(&src_path, &dst_path)?;
        } else {
            fs::copy(&src_path, &dst_path).map_err(|e| {
                format!(
                    "failed to copy '{}' to '{}': {}",
                    src_path.display(),
                    dst_path.display(),
                    e
                )
            })?;
        }
    }

    Ok(())
}

/// Set up the reduction workspace.
///
/// Creates the output directory structure and copies the input into it.
///
/// Returns a [`Workspace`] describing the created directory layout.
pub fn setup(input: &Path, output: Option<&Path>, force: bool) -> Result<Workspace, String> {
    let output_root = match output {
        Some(p) => p.to_path_buf(),
        None => default_output_path(input)?,
    };

    // Check for existing output directory
    if output_root.exists() {
        if force {
            fs::remove_dir_all(&output_root).map_err(|e| {
                format!(
                    "failed to remove existing output directory '{}': {}",
                    output_root.display(),
                    e
                )
            })?;
        } else {
            return Err(format!(
                "output directory already exists: {}\n\
                 Use --force to overwrite, or --output to specify a different path.",
                output_root.display()
            ));
        }
    }

    let original = output_root.join("original");
    let result = output_root.join("result");
    let divergent = output_root.join("divergent");
    let log = output_root.join("log.txt");

    // Create the directory structure
    fs::create_dir_all(&output_root).map_err(|e| {
        format!(
            "failed to create output directory '{}': {}",
            output_root.display(),
            e
        )
    })?;
    fs::create_dir(&divergent).map_err(|e| {
        format!(
            "failed to create divergent directory '{}': {}",
            divergent.display(),
            e
        )
    })?;

    // Copy input into original/ and result/
    let input_dir = resolve_input_dir(input)?;
    copy_dir_recursive(&input_dir, &original)?;
    copy_dir_recursive(&input_dir, &result)?;

    // Create log file
    fs::write(&log, "")
        .map_err(|e| format!("failed to create log file '{}': {}", log.display(), e))?;

    Ok(Workspace {
        root: output_root,
        original,
        result,
        divergent,
        log,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a temporary directory with a `.vole` file for testing.
    fn make_temp_input() -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().unwrap();
        let vole_file = dir.path().join("main.vole");
        fs::write(&vole_file, "func main() { }\n").unwrap();
        (dir, vole_file)
    }

    #[test]
    fn setup_creates_workspace_structure() {
        let (input_dir, _) = make_temp_input();
        let output_dir = tempfile::tempdir().unwrap();
        let output_path = output_dir.path().join("ws");

        let ws = setup(input_dir.path(), Some(&output_path), false).unwrap();

        assert!(ws.original.exists());
        assert!(ws.result.exists());
        assert!(ws.divergent.exists());
        assert!(ws.log.exists());
        assert!(ws.original.join("main.vole").exists());
        assert!(ws.result.join("main.vole").exists());
    }

    #[test]
    fn setup_rejects_existing_output_without_force() {
        let (input_dir, _) = make_temp_input();
        let output_dir = tempfile::tempdir().unwrap();
        let output_path = output_dir.path().join("ws");

        // Create the first workspace.
        setup(input_dir.path(), Some(&output_path), false).unwrap();

        // Second setup without --force should fail.
        let result = setup(input_dir.path(), Some(&output_path), false);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already exists"));
    }

    #[test]
    fn setup_force_overwrites_existing_output() {
        let (input_dir, _) = make_temp_input();
        let output_dir = tempfile::tempdir().unwrap();
        let output_path = output_dir.path().join("ws");

        // Create the first workspace.
        setup(input_dir.path(), Some(&output_path), false).unwrap();

        // Second setup with --force should succeed.
        let ws = setup(input_dir.path(), Some(&output_path), true).unwrap();
        assert!(ws.result.exists());
    }

    #[test]
    fn setup_copies_files_correctly() {
        let dir = tempfile::tempdir().unwrap();
        let a = dir.path().join("a.vole");
        let b = dir.path().join("b.vole");
        fs::write(&a, "file a content\n").unwrap();
        fs::write(&b, "file b content\n").unwrap();

        let output_dir = tempfile::tempdir().unwrap();
        let output_path = output_dir.path().join("ws");

        let ws = setup(dir.path(), Some(&output_path), false).unwrap();

        let original_a = fs::read_to_string(ws.original.join("a.vole")).unwrap();
        let result_b = fs::read_to_string(ws.result.join("b.vole")).unwrap();
        assert_eq!(original_a, "file a content\n");
        assert_eq!(result_b, "file b content\n");
    }
}
