//! Prelude file loading for standard library definitions.
//!
//! The prelude loader auto-discovers files from `stdlib/prelude/*.vole` and
//! loads them as proper modules. traits.vole is always loaded first as the
//! foundation for all other prelude files.
//!
//! Prelude files can use relative imports to import from sibling files
//! (e.g., `let { Equatable } = import "./traits"`).

use std::rc::Rc;

use super::Analyzer;
use crate::analysis_cache::CachedModule;
use crate::errors::{SemanticError, SemanticWarning};
use crate::type_arena::TypeId as ArenaTypeId;
use smallvec::smallvec;
use vole_frontend::ast::Decl;
use vole_frontend::{Interner, Parser, Span};
use vole_identity::NameId;

impl Analyzer {
    /// Load prelude files (trait definitions and primitive type implementations)
    /// This is called at the start of analyze() to make stdlib methods available.
    ///
    /// traits.vole is loaded first (defines interfaces like Equatable, Comparable, etc.),
    /// then all other prelude files are auto-discovered and loaded.
    pub(super) fn load_prelude(&mut self) {
        // Don't load prelude if we're already loading it (prevents recursion)
        if self.module.loading_prelude {
            return;
        }

        // Check if stdlib is available
        let stdlib_root = match self.module.module_loader.stdlib_root() {
            Some(root) => root.to_path_buf(),
            None => return,
        };

        self.module.loading_prelude = true;

        // Auto-discover prelude files from stdlib/prelude/*.vole
        let prelude_dir = stdlib_root.join("prelude");
        let prelude_files = self.discover_prelude_files(&prelude_dir);

        // Load traits first (defines interfaces like Equatable, Comparable, etc.)
        self.load_prelude_file("std:prelude/traits");

        // Load remaining prelude files (auto-discovered)
        for file_name in prelude_files {
            if file_name == "traits" {
                continue; // Already loaded
            }
            let import_path = format!("std:prelude/{}", file_name);
            self.load_prelude_file(&import_path);
        }

        self.module.loading_prelude = false;
    }

    /// Discover prelude files from the prelude directory.
    /// Returns file names without the .vole extension, sorted for deterministic order.
    fn discover_prelude_files(&self, prelude_dir: &std::path::Path) -> Vec<String> {
        let mut files = Vec::new();

        if let Ok(entries) = std::fs::read_dir(prelude_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().is_some_and(|ext| ext == "vole")
                    && let Some(stem) = path.file_stem().and_then(|s| s.to_str())
                {
                    files.push(stem.to_string());
                }
            }
        }

        // Sort for deterministic load order (after traits.vole)
        files.sort();
        files
    }

    /// Load a single prelude file as a proper module
    pub(super) fn load_prelude_file(&mut self, import_path: &str) {
        // Resolve path first, then canonicalize for consistent cache keys
        let resolved_path = match self.module.module_loader.resolve_path(import_path, None) {
            Ok(path) => path,
            Err(err) => {
                self.add_error(
                    SemanticError::PreludeNotFound {
                        path: import_path.to_string(),
                        message: err.to_string(),
                    },
                    Span::default(),
                );
                return;
            }
        };
        let canonical_path = resolved_path
            .canonicalize()
            .unwrap_or(resolved_path)
            .to_string_lossy()
            .to_string();

        // Check cache first using canonical_path for consistent lookup
        let cached_module = self
            .ctx
            .module_cache
            .as_ref()
            .and_then(|cache| cache.borrow().get(import_path).cloned());
        if let Some(cached) = cached_module {
            if cached.partial_error_count > 0 {
                self.add_warning(
                    SemanticWarning::PreludePartialAnalysis {
                        module: import_path.to_string(),
                        error_count: cached.partial_error_count,
                    },
                    Span::default(),
                );
            }

            // Use cached analysis results for per-Analyzer symbol tables.
            for (name, func_type) in &cached.functions_by_name {
                self.symbols
                    .functions_by_name
                    .insert(name.clone(), func_type.clone());
            }
            // Register generic prelude functions from cached module
            {
                let cached_module_id = self.name_table_mut().module_id(import_path);
                for decl in &cached.program.declarations {
                    if let Decl::Function(func) = decl
                        && !func.type_params.is_empty()
                    {
                        let name_str = cached.interner.resolve(func.name).to_string();
                        let name_id = self.name_table_mut().intern(
                            cached_module_id,
                            &[func.name],
                            &cached.interner,
                        );
                        self.symbols
                            .generic_prelude_functions
                            .insert(name_str, name_id);
                    }
                }
            }
            // ExpressionData and module_programs were pre-merged at AnalyzerContext
            // init time when the cache was provided, so skip redundant deep clones.
            if !self.ctx.prelude_expr_data_merged.get() {
                self.ctx.module_programs.borrow_mut().insert(
                    import_path.to_string(),
                    (cached.program.clone(), cached.interner.clone()),
                );
                use crate::expression_data::ExpressionData;
                let cached_data = ExpressionData {
                    types: cached.expr_types.clone(),
                    methods: cached.method_resolutions.clone(),
                    generics: cached.generic_calls.clone(),
                    class_method_generics: cached.class_method_generics.clone(),
                    static_method_generics: cached.static_method_generics.clone(),
                    is_check_results: cached.is_check_results.clone(),
                    declared_var_types: cached.declared_var_types,
                    ..Default::default()
                };
                self.ctx.merged_expr_data.borrow_mut().merge(cached_data);
            }
            return;
        }

        // Load source via module_loader
        let module_info = match self.module.module_loader.load(import_path) {
            Ok(info) => info,
            Err(err) => {
                self.add_error(
                    SemanticError::PreludeNotFound {
                        path: import_path.to_string(),
                        message: err.to_string(),
                    },
                    Span::default(),
                );
                return;
            }
        };

        // For prelude files, use the symbolic import_path (like "std:prelude/traits")
        // for module_id to maintain consistent type identity for interfaces.
        // This ensures Iterator<T> comparisons work correctly across modules.
        // Computed before parsing so NodeIds embed the correct ModuleId.
        let prelude_module = self.name_table_mut().module_id(import_path);

        // Parse the module (pass prelude_module so NodeIds are globally unique)
        let mut parser = Parser::new(&module_info.source, prelude_module);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(err) => {
                self.add_error(
                    SemanticError::PreludeParseError {
                        path: import_path.to_string(),
                        message: format!("{:?}", err.error),
                    },
                    Span::default(),
                );
                return;
            }
        };

        let mut prelude_interner = parser.into_interner();
        prelude_interner.seed_builtin_symbols();
        let prelude_interner = Rc::new(prelude_interner);

        // Create a sub-analyzer that shares the same context
        let mut sub_analyzer = self.fork_for_prelude(prelude_module, module_info.path.clone());

        // Analyze the prelude file
        let analyze_result = sub_analyzer.analyze(&program, &prelude_interner);
        let partial_error_count = match &analyze_result {
            Ok(()) => 0,
            Err(errors) => errors.len(),
        };
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "prelude analysis errors");
            self.add_warning(
                SemanticWarning::PreludePartialAnalysis {
                    module: import_path.to_string(),
                    error_count: errors.len(),
                },
                Span::default(),
            );
        }
        // Always store the module program, even if analysis had errors.
        // Partial analysis results (e.g. Map class with its methods) are still
        // valid and needed by codegen. Methods that reference unknown types
        // (like Iterator) simply won't be callable, but everything else works.

        // Convert the sub-analyzer's NodeMap to ExpressionData once, then use it
        // for both caching and merging. (CachedModule still stores individual maps
        // until codegen reads are migrated.)
        let prelude_data = sub_analyzer.results.node_map.into_expression_data();

        // Cache the analysis results
        if let Some(ref cache) = self.ctx.module_cache {
            cache.borrow_mut().insert(
                import_path.to_string(),
                CachedModule {
                    program: program.clone(),
                    interner: prelude_interner.clone(),
                    expr_types: prelude_data.types().clone(),
                    method_resolutions: prelude_data.methods().clone(),
                    generic_calls: prelude_data.generics().clone(),
                    class_method_generics: prelude_data.class_method_generics().clone(),
                    static_method_generics: prelude_data.static_method_generics().clone(),
                    functions_by_name: sub_analyzer.symbols.functions_by_name.clone(),
                    is_check_results: prelude_data.is_check_results().clone(),
                    declared_var_types: prelude_data.declared_var_types().clone(),
                    partial_error_count,
                },
            );
        }

        // Merge functions by name
        for (name, func_type) in sub_analyzer.symbols.functions_by_name {
            self.symbols.functions_by_name.insert(name, func_type);
        }

        // Register generic prelude functions for cross-interner generic lookup
        for decl in &program.declarations {
            if let Decl::Function(func) = decl
                && !func.type_params.is_empty()
            {
                let name_str = prelude_interner.resolve(func.name).to_string();
                let name_id =
                    self.name_table_mut()
                        .intern(prelude_module, &[func.name], &prelude_interner);
                self.symbols
                    .generic_prelude_functions
                    .insert(name_str, name_id);
            }
        }

        // Create module type with exports so other prelude files can import this one.
        // Only export interfaces - that's what prelude files need to import from each other.
        let mut exports: smallvec::SmallVec<[(NameId, ArenaTypeId); 8]> = smallvec![];
        for decl in &program.declarations {
            if let Decl::Interface(iface) = decl {
                let iface_str = prelude_interner.resolve(iface.name);
                // Resolve type_def_id first, then drop the borrow before getting name_id
                let type_def_id = self
                    .resolver(&prelude_interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry());
                if let Some(type_def_id) = type_def_id {
                    let name_id = self.name_table_mut().intern(
                        prelude_module,
                        &[iface.name],
                        &prelude_interner,
                    );
                    let iface_type_id = self.type_arena_mut().interface(type_def_id, smallvec![]);
                    exports.push((name_id, iface_type_id));
                }
            }
        }

        // Create module type and cache it
        // Use canonical_path for module_type_ids cache (for deduplication)
        let module_type_id = self.type_arena_mut().module(prelude_module, exports);
        self.ctx
            .module_type_ids
            .borrow_mut()
            .insert(canonical_path, module_type_id);

        // Use import_path for program/expr/method maps (consistent with module_id)
        self.ctx
            .module_programs
            .borrow_mut()
            .insert(import_path.to_string(), (program, prelude_interner));
        self.ctx.merged_expr_data.borrow_mut().merge(prelude_data);
    }

    /// Check if a function name refers to a generic function in a prelude module.
    /// Used for cross-interner detection of generic prelude functions like print/println.
    pub(crate) fn is_prelude_generic_function(
        &self,
        sym: vole_frontend::Symbol,
        interner: &Interner,
    ) -> bool {
        let name = interner.resolve(sym);
        let programs = self.ctx.module_programs.borrow();
        for (path, (_, module_interner)) in &*programs {
            if !path.starts_with("std:prelude/") {
                continue;
            }
            let Some(module_sym) = module_interner.lookup(name) else {
                continue;
            };
            let Some(module_id) = self.name_table().module_id_if_known(path) else {
                continue;
            };
            let name_id = self
                .name_table()
                .name_id(module_id, &[module_sym], module_interner);
            if let Some(name_id) = name_id
                && self
                    .entity_registry()
                    .function_by_name(name_id)
                    .is_some_and(|fid| {
                        self.entity_registry()
                            .get_function(fid)
                            .generic_info
                            .is_some()
                    })
            {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_cache::ModuleCache;
    use crate::errors::{SemanticError, SemanticWarning};
    use crate::module::ModuleLoader;
    use std::cell::RefCell;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::rc::Rc;
    use tempfile::TempDir;
    use vole_identity::ModuleId;

    fn copy_dir_recursive(src: &Path, dst: &Path) {
        fs::create_dir_all(dst).expect("create destination directory");
        for entry in fs::read_dir(src).expect("read source directory") {
            let entry = entry.expect("read dir entry");
            let src_path = entry.path();
            let dst_path = dst.join(entry.file_name());
            if src_path.is_dir() {
                copy_dir_recursive(&src_path, &dst_path);
            } else {
                fs::copy(&src_path, &dst_path).expect("copy file");
            }
        }
    }

    fn setup_project_with_broken_prelude() -> TempDir {
        let temp = tempfile::tempdir().expect("create temp dir");
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
        let stdlib_src = repo_root.join("stdlib");
        let stdlib_dst = temp.path().join("stdlib");
        copy_dir_recursive(&stdlib_src, &stdlib_dst);

        let probe_file = stdlib_dst.join("prelude/zz_partial_warning_probe.vole");
        fs::write(
            probe_file,
            r#"
func partial_warning_probe() -> i64 {
    return "not-an-i64"
}
"#,
        )
        .expect("write probe prelude file");

        fs::write(temp.path().join("main_a.vole"), "func main() {}\n").expect("write main_a");
        fs::write(temp.path().join("main_b.vole"), "func main() {}\n").expect("write main_b");
        temp
    }

    fn analyze_file(
        project_root: &Path,
        file_name: &str,
        cache: Option<Rc<RefCell<ModuleCache>>>,
    ) -> Vec<(String, usize)> {
        let file_path = project_root.join(file_name);
        let source = fs::read_to_string(&file_path).expect("read source");
        let mut parser = Parser::new(&source, ModuleId::new(0));
        let program = parser.parse_program().expect("parse source");
        let mut interner = parser.into_interner();
        interner.seed_builtin_symbols();

        let mut builder = crate::AnalyzerBuilder::new(file_path.to_string_lossy().as_ref())
            .with_project_root(Some(project_root));
        if let Some(cache) = cache {
            builder = builder.with_cache(cache);
        }
        let mut analyzer = builder.build();
        analyzer.module.module_loader = ModuleLoader::with_stdlib(project_root.join("stdlib"));
        analyzer
            .module
            .module_loader
            .set_project_root(project_root.to_path_buf());
        let result = analyzer.analyze(&program, &interner);
        assert!(
            result.is_ok(),
            "main program should still analyze successfully"
        );

        analyzer
            .take_warnings()
            .into_iter()
            .filter_map(|warn| match warn.warning {
                SemanticWarning::PreludePartialAnalysis {
                    module,
                    error_count,
                } => Some((module, error_count)),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn prelude_partial_analysis_emits_warning() {
        let project = setup_project_with_broken_prelude();
        let warnings = analyze_file(project.path(), "main_a.vole", None);
        assert!(
            warnings.iter().any(
                |(module, count)| module == "std:prelude/zz_partial_warning_probe" && *count > 0
            )
        );
    }

    #[test]
    fn cached_partial_prelude_still_emits_warning() {
        let project = setup_project_with_broken_prelude();
        let cache = ModuleCache::shared();

        let first = analyze_file(project.path(), "main_a.vole", Some(Rc::clone(&cache)));
        assert!(
            first.iter().any(
                |(module, count)| module == "std:prelude/zz_partial_warning_probe" && *count > 0
            )
        );

        let second = analyze_file(project.path(), "main_b.vole", Some(cache));
        assert!(
            second.iter().any(
                |(module, count)| module == "std:prelude/zz_partial_warning_probe" && *count > 0
            )
        );
    }

    fn setup_project_with_unparseable_prelude() -> TempDir {
        let temp = tempfile::tempdir().expect("create temp dir");
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
        let stdlib_src = repo_root.join("stdlib");
        let stdlib_dst = temp.path().join("stdlib");
        copy_dir_recursive(&stdlib_src, &stdlib_dst);

        // Write a prelude file with invalid syntax so parse_program() fails
        let bad_file = stdlib_dst.join("prelude/zz_unparseable.vole");
        fs::write(bad_file, "func @@@ this is not valid syntax { { { }")
            .expect("write unparseable prelude file");

        fs::write(temp.path().join("main.vole"), "func main() {}\n").expect("write main");
        temp
    }

    fn analyze_file_errors(project_root: &Path, file_name: &str) -> Vec<SemanticError> {
        let file_path = project_root.join(file_name);
        let source = fs::read_to_string(&file_path).expect("read source");
        let mut parser = Parser::new(&source, ModuleId::new(0));
        let program = parser.parse_program().expect("parse source");
        let mut interner = parser.into_interner();
        interner.seed_builtin_symbols();

        let mut analyzer = crate::AnalyzerBuilder::new(file_path.to_string_lossy().as_ref())
            .with_project_root(Some(project_root))
            .build();
        analyzer.module.module_loader = ModuleLoader::with_stdlib(project_root.join("stdlib"));
        analyzer
            .module
            .module_loader
            .set_project_root(project_root.to_path_buf());
        match analyzer.analyze(&program, &interner) {
            Ok(()) => vec![],
            Err(errors) => errors.into_iter().map(|e| e.error).collect(),
        }
    }

    #[test]
    fn unparseable_prelude_emits_error_not_panic() {
        let project = setup_project_with_unparseable_prelude();
        let errors = analyze_file_errors(project.path(), "main.vole");
        assert!(
            errors.iter().any(|e| matches!(
                e,
                SemanticError::PreludeParseError { path, .. }
                    if path == "std:prelude/zz_unparseable"
            )),
            "expected PreludeParseError, got: {errors:?}"
        );
    }
}
