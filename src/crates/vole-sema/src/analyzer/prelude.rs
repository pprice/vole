//! Prelude file loading for standard library definitions.
//!
//! The prelude loader auto-discovers files from `stdlib/prelude/*.vole` and
//! loads them as proper modules. traits.vole is always loaded first as the
//! foundation for all other prelude files.
//!
//! Prelude files can use relative imports to import from sibling files
//! (e.g., `let { Equatable } = import "./traits"`).

use super::Analyzer;
use crate::analysis_cache::CachedModule;
use crate::type_arena::TypeId as ArenaTypeId;
use smallvec::smallvec;
use vole_frontend::ast::Decl;
use vole_frontend::{Interner, Parser};
use vole_identity::NameId;

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

    /// Load a single prelude file as a proper module
    pub(super) fn load_prelude_file(&mut self, import_path: &str, _interner: &Interner) {
        // Resolve path first, then canonicalize for consistent cache keys
        let resolved_path = self
            .module_loader
            .resolve_path(import_path, None)
            .unwrap_or_else(|err| {
                panic!(
                    "Failed to resolve prelude path '{import_path}': {err}\n\
                     This is a bug in the standard library or installation."
                )
            });
        let canonical_path = resolved_path
            .canonicalize()
            .unwrap_or(resolved_path)
            .to_string_lossy()
            .to_string();

        // Check cache first using canonical_path for consistent lookup
        if let Some(ref cache) = self.ctx.module_cache
            && let Some(cached) = cache.borrow().get(import_path)
        {
            // Use cached analysis results.
            for (name, func_type) in &cached.functions_by_name {
                self.functions_by_name
                    .insert(name.clone(), func_type.clone());
            }
            // Use import_path for prelude files (consistent with module_id)
            self.ctx.module_programs.borrow_mut().insert(
                import_path.to_string(),
                (cached.program.clone(), cached.interner.clone()),
            );
            self.module_expr_types
                .insert(import_path.to_string(), cached.expr_types.clone());
            self.module_method_resolutions
                .insert(import_path.to_string(), cached.method_resolutions.clone());
            return;
        }

        // Load source via module_loader
        let module_info = self.module_loader.load(import_path).unwrap_or_else(|err| {
            panic!(
                "Failed to load prelude file '{import_path}': {err}\n\
                     This is a bug in the standard library or installation."
            )
        });

        // Parse the module
        let mut parser = Parser::new(&module_info.source);
        let program = parser.parse_program().unwrap_or_else(|err| {
            panic!(
                "Failed to parse prelude file '{import_path}': {err:?}\n\
                 This is a bug in the standard library."
            )
        });

        let mut prelude_interner = parser.into_interner();
        prelude_interner.seed_builtin_symbols();

        // For prelude files, use the symbolic import_path (like "std:prelude/traits")
        // for module_id to maintain consistent type identity for interfaces.
        // This ensures Iterator<T> comparisons work correctly across modules.
        let prelude_module = self.name_table_mut().module_id(import_path);

        // Create a sub-analyzer that shares the same context
        let mut sub_analyzer = self.fork_for_prelude(prelude_module, module_info.path.clone());

        // Analyze the prelude file
        let analyze_result = sub_analyzer.analyze(&program, &prelude_interner);
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "prelude analysis errors");
        }
        if analyze_result.is_ok() {
            // Cache the analysis results
            if let Some(ref cache) = self.ctx.module_cache {
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

            // Merge functions by name
            for (name, func_type) in sub_analyzer.functions_by_name {
                self.functions_by_name.insert(name, func_type);
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
                        let iface_type_id =
                            self.type_arena_mut().interface(type_def_id, smallvec![]);
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
            self.module_expr_types
                .insert(import_path.to_string(), sub_analyzer.expr_types.clone());
            self.module_method_resolutions.insert(
                import_path.to_string(),
                sub_analyzer.method_resolutions.into_inner(),
            );
        }
    }
}
