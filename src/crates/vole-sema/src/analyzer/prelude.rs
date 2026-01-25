//! Prelude file loading for standard library definitions.
//!
//! The prelude loader auto-discovers files from `stdlib/prelude/*.vole` and
//! loads them. traits.vole is always loaded first as the foundation for all
//! other prelude files.
//!
//! Note: Prelude files don't need imports between themselves because all symbols
//! from traits.vole are globally available after it's loaded.

use super::Analyzer;
use crate::analysis_cache::CachedModule;
use crate::generic::TypeParamScopeStack;
use crate::module::ModuleLoader;
use crate::resolution::MethodResolutions;
use crate::scope::Scope;
use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;
use vole_frontend::{Interner, Parser};

impl Analyzer {
    /// Load prelude files (trait definitions and primitive type implementations)
    /// This is called at the start of analyze() to make stdlib methods available.
    ///
    /// traits.vole is loaded first (defines interfaces like Equatable, Comparable, etc.),
    /// then all other prelude files are auto-discovered and loaded.
    pub(super) fn load_prelude(&mut self, interner: &Interner) {
        // Don't load prelude if we're already loading it (prevents recursion)
        if self.loading_prelude {
            return;
        }

        // Check if stdlib is available
        let stdlib_root = match self.module_loader.stdlib_root() {
            Some(root) => root.to_path_buf(),
            None => return,
        };

        self.loading_prelude = true;

        // Auto-discover prelude files from stdlib/prelude/*.vole
        let prelude_dir = stdlib_root.join("prelude");
        let prelude_files = self.discover_prelude_files(&prelude_dir);

        // Load traits first (defines interfaces like Equatable, Comparable, etc.)
        self.load_prelude_file("std:prelude/traits", interner);

        // Load remaining prelude files (auto-discovered)
        for file_name in prelude_files {
            if file_name == "traits" {
                continue; // Already loaded
            }
            let import_path = format!("std:prelude/{}", file_name);
            self.load_prelude_file(&import_path, interner);
        }

        self.loading_prelude = false;
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

    /// Load a single prelude file and merge its registries
    pub(super) fn load_prelude_file(&mut self, import_path: &str, _interner: &Interner) {
        // Check cache first
        if let Some(ref cache) = self.module_cache
            && let Some(cached) = cache.borrow().get(import_path)
        {
            // Use cached analysis results.
            // Note: Registry data (types, methods, fields) is already in the shared
            // CompilationDb - we only need to restore per-module metadata.
            for (name, func_type) in &cached.functions_by_name {
                self.functions_by_name
                    .insert(name.clone(), func_type.clone());
            }
            self.module_programs.insert(
                import_path.to_string(),
                (cached.program.clone(), cached.interner.clone()),
            );
            // TypeIds are valid because cache was created with same shared arena
            self.module_expr_types
                .insert(import_path.to_string(), cached.expr_types.clone());
            self.module_method_resolutions
                .insert(import_path.to_string(), cached.method_resolutions.clone());
            return;
        }

        // Load source via module_loader
        let module_info = match self.module_loader.load(import_path) {
            Ok(info) => info,
            Err(_) => return, // Silently ignore missing prelude files
        };

        // Parse the module
        let mut parser = Parser::new(&module_info.source);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(_) => return, // Silently ignore parse errors in prelude
        };

        let mut prelude_interner = parser.into_interner();
        prelude_interner.seed_builtin_symbols();

        // Get the module ID for this prelude file path
        let prelude_module = self.name_table_mut().module_id(import_path);

        // Create a sub-analyzer that shares the same db
        // Note: We don't call new() because that would try to load prelude again
        let mut sub_analyzer = Analyzer {
            scope: Scope::new(),
            functions: FxHashMap::default(),
            functions_by_name: FxHashMap::default(),
            globals: FxHashMap::default(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: FxHashMap::default(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: FxHashMap::default(),
            is_check_results: FxHashMap::default(),
            method_resolutions: MethodResolutions::new(),
            module_loader: ModuleLoader::new(),
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            generic_calls: FxHashMap::default(),
            class_method_calls: FxHashMap::default(),
            static_method_calls: FxHashMap::default(),
            substituted_return_types: FxHashMap::default(),
            lambda_defaults: FxHashMap::default(),
            lambda_variables: FxHashMap::default(),
            scoped_function_types: FxHashMap::default(),
            declared_var_types: FxHashMap::default(),
            current_module: prelude_module, // Use the prelude module path!
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: None,      // Sub-analyzers don't need the cache
            db: Rc::clone(&self.db), // Share the compilation db
            current_file_path: None, // Prelude doesn't need relative imports
        };

        // Analyze the prelude file
        let analyze_result = sub_analyzer.analyze(&program, &prelude_interner);
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "prelude analysis errors");
        }
        if analyze_result.is_ok() {
            // Cache the analysis results.
            // Note: Registry data is already in the shared CompilationDb - we only
            // cache per-module metadata (expr_types, method_resolutions, etc.)
            if let Some(ref cache) = self.module_cache {
                cache.borrow_mut().insert(
                    import_path.to_string(),
                    CachedModule {
                        program: program.clone(),
                        interner: prelude_interner.clone(),
                        expr_types: sub_analyzer.expr_types.clone(),
                        method_resolutions: sub_analyzer.method_resolutions.clone_inner(),
                        functions_by_name: sub_analyzer.functions_by_name.clone(),
                        is_check_results: sub_analyzer.is_check_results.clone(),
                    },
                );
            }

            // Merge functions by name (for standalone external function declarations)
            // We use by_name because the Symbol lookup won't work across interners
            for (name, func_type) in sub_analyzer.functions_by_name {
                self.functions_by_name.insert(name, func_type);
            }

            // Store prelude program for codegen (needed for implement block compilation)
            self.module_programs
                .insert(import_path.to_string(), (program, prelude_interner));
            // Store module-specific expr_types separately (NodeIds are per-program)
            // TypeIds are valid because arena is shared between parent and sub-analyzer
            self.module_expr_types
                .insert(import_path.to_string(), sub_analyzer.expr_types.clone());
            // Store module-specific method_resolutions separately (NodeIds are per-program)
            self.module_method_resolutions.insert(
                import_path.to_string(),
                sub_analyzer.method_resolutions.into_inner(),
            );
        }
        // Silently ignore analysis errors in prelude
    }
}
