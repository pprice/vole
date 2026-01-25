//! Prelude file loading for standard library definitions.

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
        // TODO: v-a5bd - auto-discover prelude files instead of hardcoded list
        for path in [
            "std:prelude/string",
            "std:prelude/bool",
            // Signed integers
            "std:prelude/i8",
            "std:prelude/i16",
            "std:prelude/i32",
            "std:prelude/i64",
            "std:prelude/i128",
            // Unsigned integers
            "std:prelude/u8",
            "std:prelude/u16",
            "std:prelude/u32",
            "std:prelude/u64",
            // Floats
            "std:prelude/f32",
            "std:prelude/f64",
            // Collections and utilities
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
