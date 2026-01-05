//! Module loader for resolving and loading .vole files.
//!
//! Handles:
//! - Path resolution for std: imports
//! - File reading
//! - Circular import detection
//! - Module caching

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use super::locator::StdlibLocator;

#[derive(Debug)]
pub enum LoadError {
    FileNotFound(String),
    CircularImport(String),
    ReadError(String),
    StdlibNotFound,
    InvalidPath(String),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::FileNotFound(path) => write!(f, "module not found: {}", path),
            LoadError::CircularImport(path) => write!(f, "circular import detected: {}", path),
            LoadError::ReadError(msg) => write!(f, "failed to read module: {}", msg),
            LoadError::StdlibNotFound => write!(f, "stdlib directory not found"),
            LoadError::InvalidPath(path) => write!(f, "invalid import path: {}", path),
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
    /// Cache of loaded modules by canonical path
    cache: HashMap<PathBuf, ModuleInfo>,
    /// Stack of currently loading modules (for cycle detection)
    loading_stack: HashSet<PathBuf>,
}

impl ModuleLoader {
    pub fn new() -> Self {
        let stdlib_root = StdlibLocator::locate().map(|loc| loc.path);
        Self {
            stdlib_root,
            cache: HashMap::new(),
            loading_stack: HashSet::new(),
        }
    }

    /// Create a loader with explicit stdlib path (for testing)
    pub fn with_stdlib(stdlib_path: PathBuf) -> Self {
        Self {
            stdlib_root: Some(stdlib_path),
            cache: HashMap::new(),
            loading_stack: HashSet::new(),
        }
    }

    /// Load a module by import path (e.g., "std:math")
    pub fn load(&mut self, import_path: &str) -> Result<ModuleInfo, LoadError> {
        let resolved = self.resolve_path(import_path)?;

        // Check cache
        if let Some(cached) = self.cache.get(&resolved) {
            return Ok(cached.clone());
        }

        // Check for circular import
        if self.loading_stack.contains(&resolved) {
            return Err(LoadError::CircularImport(import_path.to_string()));
        }

        // Mark as loading
        self.loading_stack.insert(resolved.clone());

        // Read the file
        let source = std::fs::read_to_string(&resolved)
            .map_err(|e| LoadError::ReadError(e.to_string()))?;

        // Extract module name
        let name = resolved
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        let info = ModuleInfo {
            path: resolved.clone(),
            source,
            name,
        };

        // Cache and remove from loading stack
        self.loading_stack.remove(&resolved);
        self.cache.insert(resolved, info.clone());

        Ok(info)
    }

    /// Resolve an import path to a canonical file path
    fn resolve_path(&self, import_path: &str) -> Result<PathBuf, LoadError> {
        if let Some(module_name) = import_path.strip_prefix("std:") {
            // Standard library import
            let stdlib_root = self.stdlib_root.as_ref().ok_or(LoadError::StdlibNotFound)?;

            StdlibLocator::resolve_std_path(stdlib_root, module_name)
                .ok_or_else(|| LoadError::FileNotFound(import_path.to_string()))
        } else if import_path.starts_with("./") || import_path.starts_with("../") {
            // Relative import - not yet implemented
            // NOTE: Relative imports are the next feature after this
            Err(LoadError::InvalidPath(
                "relative imports not yet supported".to_string(),
            ))
        } else {
            Err(LoadError::InvalidPath(import_path.to_string()))
        }
    }

    /// Get the stdlib root path (if found)
    pub fn stdlib_root(&self) -> Option<&Path> {
        self.stdlib_root.as_deref()
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

    #[test]
    fn test_relative_import_not_supported() {
        let loader = ModuleLoader::new();
        let result = loader.resolve_path("./utils");
        assert!(matches!(result, Err(LoadError::InvalidPath(_))));
    }

    #[test]
    fn test_invalid_path() {
        let loader = ModuleLoader::new();
        let result = loader.resolve_path("invalid");
        assert!(matches!(result, Err(LoadError::InvalidPath(_))));
    }
}
