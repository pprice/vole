//! Prelude file loading for standard library definitions.

use super::Analyzer;
use crate::analysis_cache::CachedModule;
use crate::generic::TypeParamScopeStack;
use crate::module::ModuleLoader;
use crate::resolution::MethodResolutions;
use crate::scope::Scope;
use rustc_hash::FxHashMap;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use vole_frontend::{Interner, Parser};

impl Analyzer {
    /// Load prelude files (trait definitions and primitive type implementations)
    /// This is called at the start of analyze() to make stdlib methods available.
    pub(super) fn load_prelude(&mut self, interner: &Interner) {
        // Don't load prelude if we're already loading it (prevents recursion)
        if self.loading_prelude {
            return;
        }

        // Check if stdlib is available
        if self.module_loader.stdlib_root().is_none() {
            return;
        }

        self.loading_prelude = true;

        // Load traits first (defines interfaces like Sized)
        self.load_prelude_file("std:prelude/traits", interner);

        // Load type preludes (implement blocks for primitive types)
        for path in [
            "std:prelude/string",
            "std:prelude/i64",
            "std:prelude/i32",
            "std:prelude/f64",
            "std:prelude/f32",
            "std:prelude/bool",
            "std:prelude/iterators",
            "std:prelude/map",
            "std:prelude/set",
        ] {
            self.load_prelude_file(path, interner);
        }

        self.loading_prelude = false;
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
            functions: HashMap::new(),
            functions_by_name: FxHashMap::default(),
            globals: HashMap::new(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: HashMap::new(),
            is_check_results: HashMap::new(),
            method_resolutions: MethodResolutions::new(),
            module_loader: ModuleLoader::new(),
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            generic_calls: HashMap::new(),
            class_method_calls: HashMap::new(),
            static_method_calls: HashMap::new(),
            substituted_return_types: HashMap::new(),
            lambda_defaults: HashMap::new(),
            lambda_variables: HashMap::new(),
            scoped_function_types: HashMap::new(),
            declared_var_types: HashMap::new(),
            current_module: prelude_module, // Use the prelude module path!
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: None,      // Sub-analyzers don't need the cache
            db: Rc::clone(&self.db), // Share the compilation db
            found_return: false,
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
