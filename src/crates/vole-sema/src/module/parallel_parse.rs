//! Parallel parse wavefront: parse all modules in the import tree concurrently.
//!
//! Uses breadth-first wavefront discovery:
//! 1. Parse the entry file (wave 0)
//! 2. Extract imports via `extract_imports`
//! 3. Resolve import paths to filesystem paths using `ModuleLoader`
//! 4. Filter already-parsed modules
//! 5. Parse new modules in parallel via `rayon::par_iter` (wave N)
//! 6. For each newly parsed module, extract its imports
//! 7. Repeat until no new imports are discovered
//!
//! Circular imports are handled naturally: if a module path is already in the
//! result map, it is skipped. Missing files and parse errors are stored as
//! `Err` variants for sema to report later.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rayon::prelude::*;

use vole_frontend::imports::extract_imports;
use vole_frontend::{Interner, ParseError, Parser, Program};
use vole_identity::{ModuleId, ModuleIdAllocator};

use super::loader::ModuleLoader;

/// A successfully parsed module, ready for sema analysis.
pub struct ParsedModule {
    pub program: Program,
    pub interner: Interner,
    pub source: String,
    pub file_path: String,
    pub module_id: ModuleId,
}

/// Error from the parallel parse pipeline.
#[derive(Debug)]
pub enum WavefrontError {
    /// File could not be read.
    IoError { path: String, message: String },
    /// Parser returned an error.
    Parse(ParseError),
    /// Module path could not be resolved (bad import path, sandbox escape, etc.)
    Resolution {
        import_path: String,
        message: String,
    },
}

impl std::fmt::Display for WavefrontError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WavefrontError::IoError { path, message } => {
                write!(f, "failed to read {}: {}", path, message)
            }
            WavefrontError::Parse(e) => write!(f, "parse error: {:?}", e.error),
            WavefrontError::Resolution {
                import_path,
                message,
            } => write!(f, "cannot resolve {}: {}", import_path, message),
        }
    }
}

/// Outcome of parsing a single module in the wavefront.
struct WaveResult {
    /// Canonical path used as map key.
    canonical_path: PathBuf,
    /// Parse result (success or error).
    result: Result<ParsedModule, WavefrontError>,
    /// Import paths discovered from this module (empty on error).
    discovered_imports: Vec<String>,
    /// The file path of the parsed module (for resolving relative imports from it).
    file_path: Option<PathBuf>,
}

/// Parse all modules in the import tree concurrently, starting from `entry_source`.
///
/// `entry_path` is the filesystem path of the entry file (used for resolving
/// relative imports and as the canonical key for the entry module).
///
/// `module_loader` provides path resolution (std: prefix, relative paths,
/// .vole extension, sandbox enforcement). It is used on the main thread for
/// path resolution; each wave's parsing happens in parallel.
///
/// `id_alloc` provides thread-safe module ID allocation.
///
/// Returns a map from canonical `PathBuf` to the parse result for every module
/// discovered in the import tree.
pub fn parallel_parse(
    entry_source: &str,
    entry_path: &Path,
    module_loader: &ModuleLoader,
    id_alloc: &ModuleIdAllocator,
) -> HashMap<PathBuf, Result<ParsedModule, WavefrontError>> {
    let mut results: HashMap<PathBuf, Result<ParsedModule, WavefrontError>> = HashMap::new();

    // Canonicalize entry path for consistent map keys.
    let entry_canonical = entry_path
        .canonicalize()
        .unwrap_or_else(|_| entry_path.to_path_buf());

    // Wave 0: parse the entry file on the current thread.
    let entry_module_id = id_alloc.next();
    let entry_result = parse_single(entry_source, &entry_canonical, entry_module_id);

    // Extract imports from the entry module (empty on parse error).
    let mut frontier: Vec<(String, PathBuf)> = Vec::new();
    let entry_file_path = entry_canonical.clone();
    if let Ok(parsed) = &entry_result {
        let imports = extract_imports(&parsed.program);
        for import_path in imports {
            match resolve_import(module_loader, &import_path, Some(&entry_file_path)) {
                Ok(canonical) => {
                    if !results.contains_key(&canonical) {
                        frontier.push((import_path, canonical));
                    }
                }
                Err(e) => {
                    // Store resolution errors keyed by a synthetic path.
                    let err_key = PathBuf::from(format!("<unresolved:{}>", import_path));
                    results.insert(err_key, Err(e));
                }
            }
        }
    }

    results.insert(entry_canonical, entry_result);

    // Wavefront loop: keep parsing until no new modules are discovered.
    while !frontier.is_empty() {
        // Deduplicate frontier against results and against itself.
        let mut wave_items: Vec<(String, PathBuf)> = Vec::new();
        let mut seen_in_wave: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();
        for (import_path, canonical) in frontier.drain(..) {
            if !results.contains_key(&canonical) && seen_in_wave.insert(canonical.clone()) {
                wave_items.push((import_path, canonical));
            }
        }

        if wave_items.is_empty() {
            break;
        }

        // Read file contents on the main thread (filesystem access), then parse in parallel.
        let wave_inputs: Vec<(PathBuf, ModuleId, Result<String, WavefrontError>)> = wave_items
            .iter()
            .map(|(_import_path, canonical)| {
                let module_id = id_alloc.next();
                let source =
                    std::fs::read_to_string(canonical).map_err(|e| WavefrontError::IoError {
                        path: canonical.display().to_string(),
                        message: e.to_string(),
                    });
                (canonical.clone(), module_id, source)
            })
            .collect();

        // Parse in parallel.
        let wave_results: Vec<WaveResult> = wave_inputs
            .into_par_iter()
            .map(
                |(canonical, module_id, source_result)| match source_result {
                    Ok(source) => {
                        let result = parse_single(&source, &canonical, module_id);
                        let discovered = match &result {
                            Ok(parsed) => extract_imports(&parsed.program),
                            Err(_) => Vec::new(),
                        };
                        WaveResult {
                            canonical_path: canonical.clone(),
                            result,
                            discovered_imports: discovered,
                            file_path: Some(canonical),
                        }
                    }
                    Err(e) => WaveResult {
                        canonical_path: canonical,
                        result: Err(e),
                        discovered_imports: Vec::new(),
                        file_path: None,
                    },
                },
            )
            .collect();

        // Collect results and build the next frontier.
        for wave_result in wave_results {
            // Resolve newly discovered imports.
            for import_path in &wave_result.discovered_imports {
                let from_file = wave_result.file_path.as_deref();
                match resolve_import(module_loader, import_path, from_file) {
                    Ok(canonical) => {
                        if !results.contains_key(&canonical) {
                            frontier.push((import_path.clone(), canonical));
                        }
                    }
                    Err(e) => {
                        let err_key = PathBuf::from(format!("<unresolved:{}>", import_path));
                        results.entry(err_key).or_insert(Err(e));
                    }
                }
            }

            results.insert(wave_result.canonical_path, wave_result.result);
        }
    }

    results
}

/// Parse a single source string into a `ParsedModule`.
fn parse_single(
    source: &str,
    canonical_path: &Path,
    module_id: ModuleId,
) -> Result<ParsedModule, WavefrontError> {
    let mut parser = Parser::new(source, module_id);
    let program = parser.parse_program().map_err(WavefrontError::Parse)?;
    let mut interner = parser.into_interner();
    interner.seed_builtin_symbols();

    Ok(ParsedModule {
        program,
        interner,
        source: source.to_string(),
        file_path: canonical_path.display().to_string(),
        module_id,
    })
}

/// Resolve an import path to a canonical filesystem path using the module loader.
fn resolve_import(
    loader: &ModuleLoader,
    import_path: &str,
    from_file: Option<&Path>,
) -> Result<PathBuf, WavefrontError> {
    loader
        .resolve_path(import_path, from_file)
        .map(|p| p.canonicalize().unwrap_or(p))
        .map_err(|e| WavefrontError::Resolution {
            import_path: import_path.to_string(),
            message: e.to_string(),
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn create_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&path, content).unwrap();
        path
    }

    #[test]
    fn single_file_no_imports() {
        let temp = TempDir::new().unwrap();
        let entry = create_file(temp.path(), "main.vole", "let x = 42\n");
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(temp.path().to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        assert_eq!(results.len(), 1);
        let canonical = entry.canonicalize().unwrap();
        let parsed = results.get(&canonical).unwrap().as_ref().unwrap();
        assert_eq!(parsed.module_id, ModuleId::new(0));
    }

    #[test]
    fn two_modules_one_import() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        create_file(root, "utils.vole", "func helper() -> i64 => 1\n");
        let entry = create_file(
            root,
            "main.vole",
            "let utils = import \"./utils\"\nlet x = 42\n",
        );
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        // Should have 2 modules: main + utils
        let ok_count = results.values().filter(|r| r.is_ok()).count();
        assert_eq!(ok_count, 2);
    }

    #[test]
    fn diamond_dependency() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // a imports b and c; both b and c import d
        create_file(root, "d.vole", "let value = 1\n");
        create_file(root, "b.vole", "let d = import \"./d\"\n");
        create_file(root, "c.vole", "let d = import \"./d\"\n");
        let entry = create_file(
            root,
            "a.vole",
            "let b = import \"./b\"\nlet c = import \"./c\"\n",
        );
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        // Should have exactly 4 modules (a, b, c, d), no duplicates
        let ok_count = results.values().filter(|r| r.is_ok()).count();
        assert_eq!(ok_count, 4);
    }

    #[test]
    fn circular_import_handled() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        // a imports b, b imports a → b is parsed once, a is already in results
        create_file(root, "b.vole", "let a = import \"./a\"\n");
        let entry = create_file(root, "a.vole", "let b = import \"./b\"\n");
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        // Both a and b should be parsed successfully (circularity is sema's concern)
        let ok_count = results.values().filter(|r| r.is_ok()).count();
        assert_eq!(ok_count, 2);
    }

    #[test]
    fn missing_import_stored_as_error() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        let entry = create_file(
            root,
            "main.vole",
            "let missing = import \"./nonexistent\"\n",
        );
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        // Entry module parsed OK; the missing import is a resolution error
        let err_count = results.values().filter(|r| r.is_err()).count();
        assert!(
            err_count >= 1,
            "expected at least one error for missing import"
        );
    }

    #[test]
    fn parse_error_stored() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        create_file(root, "bad.vole", "func { invalid syntax\n");
        let entry = create_file(root, "main.vole", "let bad = import \"./bad\"\n");
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        let bad_canonical = root.join("bad.vole").canonicalize().unwrap();
        let bad_result = results.get(&bad_canonical);
        assert!(bad_result.is_some(), "bad.vole should be in results");
        assert!(bad_result.unwrap().is_err(), "bad.vole should be an error");
    }

    #[test]
    fn unique_module_ids() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        create_file(root, "b.vole", "let x = 1\n");
        create_file(root, "c.vole", "let y = 2\n");
        let entry = create_file(
            root,
            "a.vole",
            "let b = import \"./b\"\nlet c = import \"./c\"\n",
        );
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        let mut ids: Vec<ModuleId> = results
            .values()
            .filter_map(|r| r.as_ref().ok())
            .map(|p| p.module_id)
            .collect();
        ids.sort_by_key(|id| format!("{:?}", id));
        let unique_count = {
            let mut deduped = ids.clone();
            deduped.dedup();
            deduped.len()
        };
        assert_eq!(ids.len(), unique_count, "all module IDs should be unique");
    }

    #[test]
    fn transitive_imports_three_deep() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();

        create_file(root, "c.vole", "let z = 3\n");
        create_file(root, "b.vole", "let c = import \"./c\"\n");
        let entry = create_file(root, "a.vole", "let b = import \"./b\"\n");
        let source = fs::read_to_string(&entry).unwrap();

        let mut loader = ModuleLoader::new();
        loader.set_project_root(root.to_path_buf());
        let alloc = ModuleIdAllocator::new();

        let results = parallel_parse(&source, &entry, &loader, &alloc);

        // a -> b -> c: three modules total
        let ok_count = results.values().filter(|r| r.is_ok()).count();
        assert_eq!(ok_count, 3);
    }
}
