//! Module loader for resolving and loading .vole files.
//!
//! Handles:
//! - Path resolution for std: imports
//! - File reading
//! - Circular import detection
//! - Module caching

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use rustc_hash::FxHashMap;

use super::locator::StdlibLocator;

#[derive(Debug)]
pub enum LoadError {
    FileNotFound(String),
    CircularImport(String),
    ReadError(String),
    StdlibNotFound,
    InvalidPath(String),
    /// Absolute paths like `/etc/passwd` are not allowed for security
    AbsolutePathNotAllowed(String),
    /// Import escapes the project sandbox (e.g., `../../../etc/passwd`)
    EscapesSandbox {
        import_path: String,
        resolved: PathBuf,
    },
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::FileNotFound(path) => write!(f, "module not found: {}", path),
            LoadError::CircularImport(path) => write!(f, "circular import detected: {}", path),
            LoadError::ReadError(msg) => write!(f, "failed to read module: {}", msg),
            LoadError::StdlibNotFound => write!(f, "stdlib directory not found"),
            LoadError::InvalidPath(path) => write!(f, "invalid import path: {}", path),
            LoadError::AbsolutePathNotAllowed(path) => {
                write!(f, "absolute imports not allowed: {}", path)
            }
            LoadError::EscapesSandbox {
                import_path,
                resolved,
            } => {
                write!(
                    f,
                    "import escapes project root: {} (resolved to {})",
                    import_path,
                    resolved.display()
                )
            }
        }
    }
}

/// Information about a loaded module
#[derive(Debug, Clone)]
pub struct ModuleInfo {
    /// Canonical path to the module file
    pub path: PathBuf,
    /// Source code content
    pub source: String,
    /// Module name (e.g., "math" for std:math)
    pub name: String,
}

/// Module loader with caching and cycle detection
pub struct ModuleLoader {
    /// Stdlib root directory
    stdlib_root: Option<PathBuf>,
    /// Project root directory (sandbox boundary for relative imports)
    project_root: Option<PathBuf>,
    /// Cache of loaded modules by canonical path
    cache: FxHashMap<PathBuf, ModuleInfo>,
    /// Stack of currently loading modules (for cycle detection)
    loading_stack: HashSet<PathBuf>,
}

impl ModuleLoader {
    pub fn new() -> Self {
        let stdlib_root = StdlibLocator::locate().map(|loc| loc.path);
        Self {
            stdlib_root,
            project_root: None,
            cache: FxHashMap::default(),
            loading_stack: HashSet::new(),
        }
    }

    /// Create a loader with explicit stdlib path (for testing)
    pub fn with_stdlib(stdlib_path: PathBuf) -> Self {
        Self {
            stdlib_root: Some(stdlib_path),
            project_root: None,
            cache: FxHashMap::default(),
            loading_stack: HashSet::new(),
        }
    }

    /// Set the project root for sandbox enforcement.
    /// Relative imports cannot escape this directory.
    pub fn set_project_root(&mut self, root: PathBuf) {
        self.project_root = Some(root);
    }

    /// Create a child loader with the same sandbox settings (stdlib_root, project_root)
    /// but empty cache and loading stack. Used for sub-analyzers.
    pub fn new_child(&self) -> Self {
        Self {
            stdlib_root: self.stdlib_root.clone(),
            project_root: self.project_root.clone(),
            cache: FxHashMap::default(),
            loading_stack: HashSet::new(),
        }
    }

    /// Detect project root from a file path.
    /// Searches upward for .git, vole.toml, or uses the file's directory.
    pub fn detect_project_root(file_path: &Path) -> PathBuf {
        let start_dir = if file_path.is_file() {
            file_path.parent().unwrap_or(file_path)
        } else {
            file_path
        };

        // Search upward for project markers
        let mut current = start_dir;
        loop {
            // Check for .git directory
            if current.join(".git").exists() {
                return current.to_path_buf();
            }
            // Check for vole.toml
            if current.join("vole.toml").exists() {
                return current.to_path_buf();
            }
            // Move to parent
            match current.parent() {
                Some(parent) if parent != current => current = parent,
                _ => break,
            }
        }

        // Fall back to the starting directory
        start_dir.to_path_buf()
    }

    /// Load a module by import path (e.g., "std:math")
    /// For relative imports, use `load_relative` instead.
    pub fn load(&mut self, import_path: &str) -> Result<ModuleInfo, LoadError> {
        // Reject relative imports without context
        if import_path.starts_with("./") || import_path.starts_with("../") {
            return Err(LoadError::InvalidPath(
                "relative imports require a source file context; use load_relative()".to_string(),
            ));
        }

        let resolved = self.resolve_path(import_path, None)?;
        self.load_resolved(import_path, resolved)
    }

    /// Load a module relative to the importing file.
    /// `from_file` is the canonical path of the file containing the import statement.
    pub fn load_relative(
        &mut self,
        import_path: &str,
        from_file: &Path,
    ) -> Result<ModuleInfo, LoadError> {
        let resolved = self.resolve_path(import_path, Some(from_file))?;
        self.load_resolved(import_path, resolved)
    }

    /// Internal: load a resolved path with caching and cycle detection.
    fn load_resolved(
        &mut self,
        import_path: &str,
        resolved: PathBuf,
    ) -> Result<ModuleInfo, LoadError> {
        // Check cache
        if let Some(cached) = self.cache.get(&resolved) {
            return Ok(cached.clone());
        }

        // Check for circular import
        if self.loading_stack.contains(&resolved) {
            return Err(LoadError::CircularImport(import_path.to_string()));
        }

        // Mark as loading - use a scope to ensure cleanup
        self.loading_stack.insert(resolved.clone());
        let result = self.load_uncached(&resolved, import_path);
        self.loading_stack.remove(&resolved);

        match result {
            Ok(info) => {
                self.cache.insert(resolved, info.clone());
                Ok(info)
            }
            Err(e) => Err(e),
        }
    }

    /// Internal: load a module without caching (used by load_resolved())
    fn load_uncached(
        &self,
        resolved: &PathBuf,
        import_path: &str,
    ) -> Result<ModuleInfo, LoadError> {
        // Read the file
        let source = std::fs::read_to_string(resolved).map_err(|_| {
            LoadError::FileNotFound(format!(
                "{} (resolved to {})",
                import_path,
                resolved.display()
            ))
        })?;

        // Extract module name
        let name = resolved
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        Ok(ModuleInfo {
            path: resolved.clone(),
            source,
            name,
        })
    }

    /// Resolve an import path to a canonical file path.
    /// `from_file` is required for relative imports.
    fn resolve_path(
        &self,
        import_path: &str,
        from_file: Option<&Path>,
    ) -> Result<PathBuf, LoadError> {
        // Security: reject absolute paths
        if import_path.starts_with('/') {
            return Err(LoadError::AbsolutePathNotAllowed(import_path.to_string()));
        }

        if let Some(module_name) = import_path.strip_prefix("std:") {
            // Standard library import (not sandboxed)
            let stdlib_root = self.stdlib_root.as_ref().ok_or(LoadError::StdlibNotFound)?;

            StdlibLocator::resolve_std_path(stdlib_root, module_name)
                .ok_or_else(|| LoadError::FileNotFound(import_path.to_string()))
        } else if import_path.starts_with("./") || import_path.starts_with("../") {
            // Relative import
            let from_file = from_file.ok_or_else(|| {
                LoadError::InvalidPath("relative imports require a source file context".to_string())
            })?;

            self.resolve_relative_path(import_path, from_file)
        } else {
            Err(LoadError::InvalidPath(import_path.to_string()))
        }
    }

    /// Resolve a relative import path to a canonical file path.
    fn resolve_relative_path(
        &self,
        import_path: &str,
        from_file: &Path,
    ) -> Result<PathBuf, LoadError> {
        // Get the directory containing the importing file
        let from_dir = from_file.parent().ok_or_else(|| {
            LoadError::InvalidPath(format!(
                "cannot determine directory for: {}",
                from_file.display()
            ))
        })?;

        // Join and normalize the path
        let joined = from_dir.join(import_path);

        // Try with .vole extension first, then without
        let resolved = if joined.extension().is_some() {
            // Path already has an extension
            joined.canonicalize().map_err(|_| {
                LoadError::FileNotFound(format!(
                    "{} (resolved to {})",
                    import_path,
                    joined.display()
                ))
            })?
        } else {
            // Try adding .vole extension
            let with_ext = joined.with_extension("vole");
            if with_ext.exists() {
                with_ext.canonicalize().map_err(|_| {
                    LoadError::FileNotFound(format!(
                        "{} (resolved to {})",
                        import_path,
                        with_ext.display()
                    ))
                })?
            } else if joined.exists() {
                // Maybe it's a directory or file without extension
                joined.canonicalize().map_err(|_| {
                    LoadError::FileNotFound(format!(
                        "{} (resolved to {})",
                        import_path,
                        joined.display()
                    ))
                })?
            } else {
                return Err(LoadError::FileNotFound(format!(
                    "{} (resolved to {})",
                    import_path,
                    with_ext.display()
                )));
            }
        };

        // Security: check sandbox boundary
        self.check_sandbox(&resolved, import_path, from_file)?;

        Ok(resolved)
    }

    /// Check that a resolved path is within the appropriate sandbox.
    ///
    /// - If importing from within stdlib, the resolved path must stay in stdlib
    /// - Otherwise, if project_root is set, the resolved path must stay in project root
    fn check_sandbox(
        &self,
        resolved: &Path,
        import_path: &str,
        from_file: &Path,
    ) -> Result<(), LoadError> {
        // Check if importing from within stdlib - if so, sandbox to stdlib
        if let Some(ref stdlib_root) = self.stdlib_root {
            let canonical_stdlib = stdlib_root
                .canonicalize()
                .unwrap_or_else(|_| stdlib_root.clone());
            let canonical_from = from_file
                .canonicalize()
                .unwrap_or_else(|_| from_file.to_path_buf());

            if canonical_from.starts_with(&canonical_stdlib) {
                // Importing from stdlib - sandbox to stdlib
                if !resolved.starts_with(&canonical_stdlib) {
                    return Err(LoadError::EscapesSandbox {
                        import_path: import_path.to_string(),
                        resolved: resolved.to_path_buf(),
                    });
                }
                return Ok(());
            }
        }

        // Check project root sandbox for user code
        if let Some(ref root) = self.project_root {
            // Canonicalize the root for comparison
            let canonical_root = root.canonicalize().unwrap_or_else(|_| root.clone());

            if !resolved.starts_with(&canonical_root) {
                return Err(LoadError::EscapesSandbox {
                    import_path: import_path.to_string(),
                    resolved: resolved.to_path_buf(),
                });
            }
        }
        Ok(())
    }

    /// Get the stdlib root path (if found)
    pub fn stdlib_root(&self) -> Option<&Path> {
        self.stdlib_root.as_deref()
    }

    /// Get the project root path (if set)
    pub fn project_root(&self) -> Option<&Path> {
        self.project_root.as_deref()
    }
}

impl Default for ModuleLoader {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn create_test_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&path, content).unwrap();
        path
    }

    #[test]
    fn test_relative_import_without_context() {
        let mut loader = ModuleLoader::new();
        let result = loader.load("./utils");
        assert!(matches!(result, Err(LoadError::InvalidPath(_))));
    }

    #[test]
    fn test_invalid_path() {
        let loader = ModuleLoader::new();
        let result = loader.resolve_path("invalid", None);
        assert!(matches!(result, Err(LoadError::InvalidPath(_))));
    }

    #[test]
    fn test_absolute_path_rejected() {
        let loader = ModuleLoader::new();
        let result = loader.resolve_path("/etc/passwd", None);
        assert!(matches!(result, Err(LoadError::AbsolutePathNotAllowed(_))));
    }

    #[test]
    fn test_relative_import_sibling() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create main.vole and utils.vole in the same directory
        let main_file = create_test_file(root, "main.vole", "// main");
        create_test_file(root, "utils.vole", "fn helper() {}");

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());

        let result = loader.load_relative("./utils", &main_file);
        assert!(result.is_ok());
        let info = result.unwrap();
        assert_eq!(info.name, "utils");
        assert!(info.source.contains("fn helper"));
    }

    #[test]
    fn test_relative_import_subdirectory() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create main.vole and sub/module.vole
        let main_file = create_test_file(root, "main.vole", "// main");
        create_test_file(root, "sub/module.vole", "fn nested() {}");

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());

        let result = loader.load_relative("./sub/module", &main_file);
        assert!(result.is_ok());
        let info = result.unwrap();
        assert_eq!(info.name, "module");
    }

    #[test]
    fn test_relative_import_parent() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create utils.vole at root and src/main.vole
        create_test_file(root, "utils.vole", "fn util() {}");
        let main_file = create_test_file(root, "src/main.vole", "// main");

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());

        let result = loader.load_relative("../utils", &main_file);
        assert!(result.is_ok());
        let info = result.unwrap();
        assert_eq!(info.name, "utils");
    }

    #[test]
    fn test_sandbox_escape_rejected() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create a subdirectory that's the "project root"
        let project = root.join("project");
        fs::create_dir(&project).unwrap();

        // Create a file outside the project
        create_test_file(root, "secret.vole", "// secret");
        let main_file = create_test_file(&project, "src/main.vole", "// main");

        let mut loader = ModuleLoader::new();
        loader.set_project_root(project.clone());

        // Try to escape with ../..
        let result = loader.load_relative("../../secret", &main_file);
        assert!(matches!(result, Err(LoadError::EscapesSandbox { .. })));
    }

    #[test]
    fn test_relative_import_caching() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        let main_file = create_test_file(root, "main.vole", "// main");
        create_test_file(root, "utils.vole", "fn helper() {}");

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());

        // Load twice - should be cached
        let result1 = loader.load_relative("./utils", &main_file);
        let result2 = loader.load_relative("./utils", &main_file);

        assert!(result1.is_ok());
        assert!(result2.is_ok());
        // Both should return the same content
        assert_eq!(result1.unwrap().source, result2.unwrap().source);
    }

    #[test]
    fn test_detect_project_root_git() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create .git directory and nested file
        fs::create_dir(root.join(".git")).unwrap();
        let file_path = create_test_file(root, "src/deep/main.vole", "// main");

        let detected = ModuleLoader::detect_project_root(&file_path);
        assert_eq!(
            detected.canonicalize().unwrap(),
            root.canonicalize().unwrap()
        );
    }

    #[test]
    fn test_detect_project_root_vole_toml() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create vole.toml and nested file
        create_test_file(root, "vole.toml", "# config");
        let file_path = create_test_file(root, "src/main.vole", "// main");

        let detected = ModuleLoader::detect_project_root(&file_path);
        assert_eq!(
            detected.canonicalize().unwrap(),
            root.canonicalize().unwrap()
        );
    }

    #[test]
    fn test_relative_import_not_found() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        let main_file = create_test_file(root, "main.vole", "// main");

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());

        let result = loader.load_relative("./nonexistent", &main_file);
        assert!(matches!(result, Err(LoadError::FileNotFound(_))));
    }

    #[test]
    fn test_stdlib_sandbox_escape_rejected() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create a mock stdlib directory
        let stdlib = root.join("stdlib");
        fs::create_dir(&stdlib).unwrap();
        let stdlib_file = create_test_file(&stdlib, "math.vole", "// math module");

        // Create a file outside stdlib
        create_test_file(root, "secret.vole", "// secret outside stdlib");

        // Create loader with stdlib root
        let mut loader = ModuleLoader::with_stdlib(stdlib);

        // Try to escape stdlib via relative import from a stdlib file
        let result = loader.load_relative("../secret", &stdlib_file);
        assert!(
            matches!(result, Err(LoadError::EscapesSandbox { .. })),
            "Expected sandbox escape error, got {:?}",
            result
        );
    }

    #[test]
    fn test_stdlib_relative_import_within_stdlib_allowed() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create a mock stdlib with nested files
        let stdlib = root.join("stdlib");
        let prelude = stdlib.join("prelude");
        fs::create_dir_all(&prelude).unwrap();

        let traits_file = create_test_file(&prelude, "traits.vole", "// traits module");
        create_test_file(&prelude, "bool.vole", "// bool module");

        // Create loader with stdlib root
        let mut loader = ModuleLoader::with_stdlib(stdlib);

        // Relative import within stdlib should be allowed
        let result = loader.load_relative("./bool", &traits_file);
        assert!(result.is_ok(), "Expected success, got {:?}", result);
    }

    #[test]
    fn test_new_child_inherits_roots() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // Create directories
        let stdlib = root.join("stdlib");
        let project = root.join("project");
        fs::create_dir_all(&stdlib).unwrap();
        fs::create_dir_all(&project).unwrap();

        // Create parent loader with both roots
        let mut parent = ModuleLoader::with_stdlib(stdlib.clone());
        parent.set_project_root(project.clone());

        // Create child
        let child = parent.new_child();

        // Child should inherit roots
        assert_eq!(child.stdlib_root(), Some(stdlib.as_path()));
        assert_eq!(child.project_root(), Some(project.as_path()));
    }
}
