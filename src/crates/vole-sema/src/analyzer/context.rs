// Shared context types for the analyzer.

use crate::analysis_cache::ModuleCache;
use crate::compilation_db::CompilationDb;
use crate::entity_registry::EntityRegistry;
use crate::resolve::ResolverEntityExt;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use vole_frontend::Interner;
use vole_frontend::ast::Program;
use vole_identity::{ModuleId, NameTable, Resolver, TypeDefId};

use vole_frontend::ast::Symbol;

/// Guard that holds a borrow of the name table and provides resolver access.
/// The name table borrow is independent of other CompilationDb fields,
/// so entities/types/implements can be borrowed simultaneously.
pub(crate) struct ResolverGuard<'a> {
    names: std::cell::Ref<'a, NameTable>,
    interner: &'a Interner,
    module_id: ModuleId,
    imports: &'a [ModuleId],
    priority_module: Option<ModuleId>,
}

impl<'a> ResolverGuard<'a> {
    pub(super) fn new(
        db: &'a CompilationDb,
        interner: &'a Interner,
        module_id: ModuleId,
        imports: &'a [ModuleId],
        priority_module: Option<ModuleId>,
    ) -> Self {
        Self {
            names: db.names(),
            interner,
            module_id,
            imports,
            priority_module,
        }
    }

    /// Get the resolver. The lifetime is tied to this guard.
    pub(crate) fn resolver(&self) -> Resolver<'_> {
        Resolver::new(self.interner, &self.names, self.module_id, self.imports)
            .with_priority_module(self.priority_module)
    }

    /// Resolve a Symbol to a TypeDefId through the resolution chain.
    pub(crate) fn resolve_type(&self, sym: Symbol, registry: &EntityRegistry) -> Option<TypeDefId> {
        self.resolver().resolve_type(sym, registry)
    }

    /// Resolve a type with fallback to interface/class short name search.
    pub(crate) fn resolve_type_or_interface(
        &self,
        sym: Symbol,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        self.resolver().resolve_type_or_interface(sym, registry)
    }

    /// Resolve a type string with fallback to interface/class short name search.
    pub(crate) fn resolve_type_str_or_interface(
        &self,
        name: &str,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        self.resolver()
            .resolve_type_str_or_interface(name, registry)
    }
}

/// Shared state across all Analyzer instances (parent + sub-analyzers).
/// Single `Rc` clone instead of 3-4 individual `Rc` clones per sub-analyzer.
pub(crate) struct AnalyzerContext {
    /// Unified compilation database containing all registries.
    /// Shared via `Rc` so sub-analyzers use the same db, making TypeIds
    /// valid across all analyzers and eliminating clone/merge operations.
    /// Each field within CompilationDb has its own RefCell for independent borrows.
    pub(crate) db: Rc<CompilationDb>,
    /// Cached module TypeIds by import path (avoids re-parsing).
    pub(crate) module_type_ids: RefCell<FxHashMap<String, ArenaTypeId>>,
    /// Parsed module programs and their interners (for compiling pure Vole functions).
    pub(crate) module_programs: RefCell<FxHashMap<String, (Program, Interner)>>,
    /// Merged expression data from all sub-analyzers (module analysis results).
    /// Because NodeIds are now globally unique (they embed a ModuleId), results
    /// from different modules can be merged into a single flat map without collision.
    pub(crate) merged_expr_data: RefCell<crate::expression_data::ExpressionData>,
    /// Optional shared cache for module analysis results.
    /// When set, modules are cached after analysis and reused across Analyzer instances.
    pub(crate) module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// Set of modules currently being analyzed (for circular import detection).
    /// Shared across all sub-analyzers via Rc<AnalyzerContext> so that cycles
    /// are detected even across nested module imports.
    pub(crate) modules_in_progress: RefCell<FxHashSet<String>>,
    /// Module paths that had sema errors during sub-analysis.
    /// Codegen should skip compiling function bodies for these modules
    /// to avoid encountering INVALID type IDs from failed type checking.
    pub(crate) modules_with_errors: RefCell<FxHashSet<String>>,
    /// Whether cached prelude ExpressionData has been pre-merged into merged_expr_data.
    /// Set once during init when a module cache contains prelude entries, so that
    /// load_prelude_file skips redundant deep clones on every compiled file.
    pub(crate) prelude_expr_data_merged: Cell<bool>,
}

impl AnalyzerContext {
    /// Create a new context with the given db and optional cache.
    /// When a cache is provided, pre-merges all cached prelude ExpressionData
    /// and module programs so that load_prelude_file can skip redundant clones.
    pub(super) fn new(db: Rc<CompilationDb>, cache: Option<Rc<RefCell<ModuleCache>>>) -> Self {
        let mut merged_expr_data = crate::expression_data::ExpressionData::new();
        let mut module_programs = FxHashMap::default();
        let prelude_merged =
            Self::pre_merge_cached_prelude(&cache, &mut merged_expr_data, &mut module_programs);
        Self {
            db,
            module_type_ids: RefCell::new(FxHashMap::default()),
            module_programs: RefCell::new(module_programs),
            merged_expr_data: RefCell::new(merged_expr_data),
            module_cache: cache,
            modules_in_progress: RefCell::new(FxHashSet::default()),
            modules_with_errors: RefCell::new(FxHashSet::default()),
            prelude_expr_data_merged: Cell::new(prelude_merged),
        }
    }

    /// Pre-merge cached prelude ExpressionData and module programs at init time.
    ///
    /// Iterates all `std:prelude/*` entries in the cache and merges their
    /// ExpressionData into `merged_expr_data` and programs into `module_programs`.
    /// Returns true if any prelude entries were merged.
    fn pre_merge_cached_prelude(
        cache: &Option<Rc<RefCell<ModuleCache>>>,
        merged_expr_data: &mut crate::expression_data::ExpressionData,
        module_programs: &mut FxHashMap<String, (Program, Interner)>,
    ) -> bool {
        let Some(cache_rc) = cache else {
            return false;
        };
        let cache_ref = cache_rc.borrow();
        let mut merged_any = false;
        for (path, cached) in cache_ref.prelude_entries() {
            module_programs.insert(
                path.to_string(),
                (cached.program.clone(), cached.interner.clone()),
            );
            let cached_data = crate::expression_data::ExpressionData {
                types: cached.expr_types.clone(),
                methods: cached.method_resolutions.clone(),
                generics: cached.generic_calls.clone(),
                class_method_generics: cached.class_method_generics.clone(),
                static_method_generics: cached.static_method_generics.clone(),
                is_check_results: cached.is_check_results.clone(),
                declared_var_types: cached.declared_var_types.clone(),
                ..Default::default()
            };
            merged_expr_data.merge(cached_data);
            merged_any = true;
        }
        merged_any
    }

    /// Create an empty context (for Default impl).
    pub(super) fn empty() -> Self {
        Self::new(Rc::new(CompilationDb::new()), None)
    }
}
