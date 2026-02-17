//! Stdlib locator - finds the stdlib directory at runtime.
//!
//! Search order:
//! 1. $VOLE_STDLIB_PATH environment variable
//! 2. <exe_dir>/stdlib (release tarball layout — stdlib next to binary)
//! 3. <exe_dir>/../share/vole/stdlib (installed layout)
//! 4. <exe_dir>/../../stdlib (development layout)
//! 5. ./stdlib (current directory fallback)

use std::path::{Path, PathBuf};

/// Result of stdlib location search
#[derive(Debug, Clone)]
pub struct StdlibLocation {
    pub path: PathBuf,
    pub source: LocationSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocationSource {
    EnvVar,
    Sibling,
    Installed,
    Development,
    CurrentDir,
}

impl std::fmt::Display for StdlibLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({:?})", self.path.display(), self.source)
    }
}

/// Locator for finding the stdlib directory
pub struct StdlibLocator;

impl StdlibLocator {
    /// Locate the stdlib directory.
    /// Returns the path and how it was found, or None if not found.
    pub fn locate() -> Option<StdlibLocation> {
        // 1. Check environment variable
        if let Ok(env_path) = std::env::var("VOLE_STDLIB_PATH") {
            let path = PathBuf::from(&env_path);
            if Self::is_valid_stdlib(&path) {
                return Some(StdlibLocation {
                    path,
                    source: LocationSource::EnvVar,
                });
            }
        }

        // Get executable directory for relative path checks
        if let Ok(exe_path) = std::env::current_exe()
            && let Some(exe_dir) = exe_path.parent()
        {
            // 2. Check sibling layout: <exe_dir>/stdlib (release tarball)
            let sibling_path = exe_dir.join("stdlib");
            if Self::is_valid_stdlib(&sibling_path) {
                return Some(StdlibLocation {
                    path: sibling_path,
                    source: LocationSource::Sibling,
                });
            }

            // 3. Check installed layout: <exe_dir>/../share/vole/stdlib
            let installed_path = exe_dir.join("..").join("share").join("vole").join("stdlib");
            if Self::is_valid_stdlib(&installed_path) {
                return Some(StdlibLocation {
                    path: installed_path,
                    source: LocationSource::Installed,
                });
            }

            // 4. Check development layout: <exe_dir>/../../stdlib
            let dev_path = exe_dir.join("..").join("..").join("stdlib");
            if Self::is_valid_stdlib(&dev_path) {
                return Some(StdlibLocation {
                    path: dev_path,
                    source: LocationSource::Development,
                });
            }
        }

        // 5. Check current directory: ./stdlib
        let cwd_path = PathBuf::from("./stdlib");
        if Self::is_valid_stdlib(&cwd_path) {
            return Some(StdlibLocation {
                path: cwd_path,
                source: LocationSource::CurrentDir,
            });
        }

        None
    }

    /// Check if a directory looks like a valid stdlib
    fn is_valid_stdlib(path: &Path) -> bool {
        path.is_dir()
    }

    /// Resolve a std: import path to a file path
    pub fn resolve_std_path(stdlib_root: &Path, module_name: &str) -> Option<PathBuf> {
        let file_path = stdlib_root.join(format!("{}.vole", module_name));
        if file_path.exists() {
            Some(file_path)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_locate_does_not_panic() {
        // Just verify the function doesn't panic
        let _result = StdlibLocator::locate();
    }

    #[test]
    fn test_is_valid_stdlib_nonexistent() {
        assert!(!StdlibLocator::is_valid_stdlib(Path::new(
            "/nonexistent/path/xyz123"
        )));
    }
}
