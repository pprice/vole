// Shared context types for the analyzer.

use crate::analysis_cache::ModuleCache;
use crate::compilation_db::CompilationDb;
use crate::entity_registry::EntityRegistry;
use crate::resolve::ResolverEntityExt;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
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
    /// Per-module analysis data (module path -> ModuleAnalysisData).
    /// NodeIds are file-local and collide across modules, so each module gets
    /// its own set of NodeId-keyed maps. Uses ArenaTypeId (= TypeId) internally.
    pub(crate) module_data: RefCell<FxHashMap<String, crate::expression_data::ModuleAnalysisData>>,
    /// Optional shared cache for module analysis results.
    /// When set, modules are cached after analysis and reused across Analyzer instances.
    pub(crate) module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// Set of modules currently being analyzed (for circular import detection).
    /// Shared across all sub-analyzers via Rc<AnalyzerContext> so that cycles
    /// are detected even across nested module imports.
    pub(crate) modules_in_progress: RefCell<FxHashSet<String>>,
}

impl AnalyzerContext {
    /// Create a new context with the given db and optional cache.
    pub(super) fn new(db: Rc<CompilationDb>, cache: Option<Rc<RefCell<ModuleCache>>>) -> Self {
        Self {
            db,
            module_type_ids: RefCell::new(FxHashMap::default()),
            module_programs: RefCell::new(FxHashMap::default()),
            module_data: RefCell::new(FxHashMap::default()),
            module_cache: cache,
            modules_in_progress: RefCell::new(FxHashSet::default()),
        }
    }

    /// Create an empty context (for Default impl).
    pub(super) fn empty() -> Self {
        Self::new(Rc::new(CompilationDb::new()), None)
    }
}

/// Module-level data extracted from `AnalyzerContext` during `into_analysis_results`.
///
/// Both the `Ok` (sole owner, move) and `Err` (shared, clone) branches of
/// `Rc::try_unwrap` populate this struct, letting the `ExpressionData` builder
/// chain appear exactly once.
pub(crate) struct ExtractedModuleData {
    pub(crate) data: FxHashMap<String, crate::expression_data::ModuleAnalysisData>,
}
