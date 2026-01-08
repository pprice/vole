// src/cli/paths.rs
//
// Shared path expansion utilities for CLI commands.

use std::collections::HashSet;
use std::path::PathBuf;

use glob::glob;

/// Errors that can occur during path expansion
#[derive(Debug)]
pub enum PathError {
    /// Glob pattern syntax error
    InvalidPattern { pattern: String, message: String },
    /// IO error (permissions, etc.)
    IoError {
        path: PathBuf,
        source: std::io::Error,
    },
}

impl std::fmt::Display for PathError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathError::InvalidPattern { pattern, message } => {
                write!(f, "invalid glob pattern '{}': {}", pattern, message)
            }
            PathError::IoError { path, source } => {
                write!(f, "error reading '{}': {}", path.display(), source)
            }
        }
    }
}

impl std::error::Error for PathError {}

/// Expand a list of path patterns into concrete .vole file paths.
///
/// Each pattern can be:
/// - A direct file path (e.g., "foo.vole")
/// - A directory (expands to **/*.vole recursively)
/// - A glob pattern (e.g., "src/**/*.vole", "tests/*.vole")
///
/// Path ordering:
/// - Explicit file paths preserve their input order
/// - Glob/directory expansions are sorted and appended after explicit files
/// - Duplicates are removed (glob results matching explicit files are excluded)
///
/// Returns deduplicated paths. Empty result is valid (not an error).
pub fn expand_paths(patterns: &[String]) -> Result<Vec<PathBuf>, PathError> {
    let mut explicit_files = Vec::new();
    let mut glob_files = Vec::new();
    let mut seen: HashSet<PathBuf> = HashSet::new();

    for pattern in patterns {
        expand_pattern(pattern, &mut explicit_files, &mut glob_files, &mut seen)?;
    }

    // Combine: explicit files first (preserving order), then glob files (unsorted)
    // Duplicates already handled by the `seen` HashSet
    explicit_files.extend(glob_files);

    Ok(explicit_files)
}

/// Expand a single pattern into file paths
fn expand_pattern(
    pattern: &str,
    explicit_files: &mut Vec<PathBuf>,
    glob_files: &mut Vec<PathBuf>,
    seen: &mut HashSet<PathBuf>,
) -> Result<(), PathError> {
    let path = PathBuf::from(pattern);

    if path.is_file() {
        // Direct file path - add to explicit files (preserves order)
        if has_vole_extension(&path) {
            add_unique(path, explicit_files, seen);
        }
        // Silently skip non-.vole files when explicitly named
        // (commands can validate this if they want stricter behavior)
    } else if path.is_dir() {
        // Directory - expand to **/*.vole and add to glob files
        let glob_pattern = format!("{}/**/*.vole", pattern);
        expand_glob(&glob_pattern, glob_files, seen)?;
    } else {
        // Treat as glob pattern and add to glob files
        expand_glob(pattern, glob_files, seen)?;
    }

    Ok(())
}

/// Expand a glob pattern and add matching .vole files
fn expand_glob(
    pattern: &str,
    files: &mut Vec<PathBuf>,
    seen: &mut HashSet<PathBuf>,
) -> Result<(), PathError> {
    let entries = glob(pattern).map_err(|e| PathError::InvalidPattern {
        pattern: pattern.to_string(),
        message: e.msg.to_string(),
    })?;

    for entry in entries {
        match entry {
            Ok(path) => {
                if path.is_file() && has_vole_extension(&path) {
                    add_unique(path, files, seen);
                }
            }
            Err(e) => {
                return Err(PathError::IoError {
                    path: e.path().to_path_buf(),
                    source: e.into_error(),
                });
            }
        }
    }

    Ok(())
}

/// Add a path if not already seen (uses canonical path for deduplication)
fn add_unique(path: PathBuf, files: &mut Vec<PathBuf>, seen: &mut HashSet<PathBuf>) {
    let key = path.canonicalize().unwrap_or_else(|_| path.clone());
    if seen.insert(key) {
        files.push(path);
    }
}

/// Check if a path has a .vole extension
fn has_vole_extension(path: &std::path::Path) -> bool {
    path.extension().is_some_and(|ext| ext == "vole")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use tempfile::TempDir;

    fn create_file(dir: &std::path::Path, name: &str) -> PathBuf {
        let path = dir.join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        let mut file = File::create(&path).unwrap();
        file.write_all(b"// test").unwrap();
        path
    }

    #[test]
    fn test_expand_single_file() {
        let dir = TempDir::new().unwrap();
        let file = create_file(dir.path(), "test.vole");

        let files = expand_paths(&[file.to_string_lossy().to_string()]).unwrap();
        assert_eq!(files.len(), 1);
        assert_eq!(files[0], file);
    }

    #[test]
    fn test_expand_directory() {
        let dir = TempDir::new().unwrap();
        create_file(dir.path(), "a.vole");
        create_file(dir.path(), "b.vole");
        create_file(dir.path(), "c.txt");

        let files = expand_paths(&[dir.path().to_string_lossy().to_string()]).unwrap();
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_expand_nested_directory() {
        let dir = TempDir::new().unwrap();
        create_file(dir.path(), "root.vole");
        create_file(dir.path(), "sub/nested.vole");
        create_file(dir.path(), "sub/deep/file.vole");

        let files = expand_paths(&[dir.path().to_string_lossy().to_string()]).unwrap();
        assert_eq!(files.len(), 3);
    }

    #[test]
    fn test_expand_glob_pattern() {
        let dir = TempDir::new().unwrap();
        create_file(dir.path(), "test1.vole");
        create_file(dir.path(), "test2.vole");
        create_file(dir.path(), "other.txt");

        let pattern = format!("{}/*.vole", dir.path().display());
        let files = expand_paths(&[pattern]).unwrap();
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_deduplication() {
        let dir = TempDir::new().unwrap();
        let file = create_file(dir.path(), "test.vole");
        let file_str = file.to_string_lossy().to_string();

        // Same file specified twice
        let files = expand_paths(&[file_str.clone(), file_str]).unwrap();
        assert_eq!(files.len(), 1);
    }

    #[test]
    fn test_sorted_output() {
        let dir = TempDir::new().unwrap();
        create_file(dir.path(), "z.vole");
        create_file(dir.path(), "a.vole");
        create_file(dir.path(), "m.vole");

        let files = expand_paths(&[dir.path().to_string_lossy().to_string()]).unwrap();
        assert_eq!(files.len(), 3);

        // Should be sorted
        let names: Vec<_> = files.iter().map(|p| p.file_name().unwrap()).collect();
        assert!(names.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn test_empty_result_is_ok() {
        let dir = TempDir::new().unwrap();
        // No .vole files in directory
        create_file(dir.path(), "test.txt");

        let files = expand_paths(&[dir.path().to_string_lossy().to_string()]).unwrap();
        assert!(files.is_empty());
    }

    #[test]
    fn test_invalid_glob_pattern() {
        let result = expand_paths(&["[invalid".to_string()]);
        assert!(matches!(result, Err(PathError::InvalidPattern { .. })));
    }

    #[test]
    fn test_non_vole_file_skipped() {
        let dir = TempDir::new().unwrap();
        let file = create_file(dir.path(), "test.txt");

        let files = expand_paths(&[file.to_string_lossy().to_string()]).unwrap();
        assert!(files.is_empty());
    }
}
