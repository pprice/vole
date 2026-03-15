// lowering/facade.rs
//
// VIR lowering orchestration — split into module-only and file-specific
// phases.  The module phase runs passes that depend only on imported modules
// and shared entity state; the file phase runs per-compilation passes that
// depend on the specific file being compiled.
//
// `lower_vir_program` is the single entry point: it calls `lower_module_vir`
// then `lower_file_vir` in sequence.  When a `CachedModuleVir` is provided
// and valid, the module phase is skipped entirely.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::annotation_inits::lower_annotation_inits;
use super::entity_metadata::{
    PopulateImplementBlockEntriesArgs, build_entity_metadata, build_name_to_type_id_map,
    extend_entity_metadata, populate_implement_block_entries,
    populate_implement_block_entries_file, populate_implement_block_entries_modules,
};
use super::field_default_inits::{
    LowerFieldDefaultInitsArgs, LowerModuleFieldDefaultInitsArgs, lower_field_default_inits,
    lower_module_field_default_inits,
};
use super::function_default_inits::{
    LowerFunctionDefaultInitsArgs, LowerModuleFunctionDefaultInitsArgs,
    lower_function_default_inits, lower_module_function_default_inits,
};
use super::functions::{
    LowerModuleFunctionsArgs, LowerTopLevelFunctionsArgs, lower_module_functions,
    lower_top_level_functions,
};
use super::global_inits::{lower_global_inits, lower_module_global_inits};
use super::implement_blocks::{
    LowerImplementBlockMethodsArgs, LowerModuleImplementBlockMethodsArgs,
    lower_implement_block_methods, lower_module_implement_block_methods,
};
use super::lambda_default_inits::{LowerLambdaDefaultInitsArgs, lower_lambda_default_inits};
use super::method_default_inits::{
    LowerMethodDefaultInitsArgs, LowerModuleMethodDefaultInitsArgs, lower_method_default_inits,
    lower_module_method_default_inits,
};
use super::module_bindings::{
    extract_cross_module_bindings, lower_module_bindings, lower_module_module_bindings,
};
use super::monomorph_info::{
    PopulatedMonomorphInfo, populate_monomorph_info, remap_monomorph_info,
};
use super::test_bodies::lower_test_bodies;
use super::test_scoped_type_methods::lower_test_scoped_type_methods;
use super::type_method_monomorph::{
    MethodMonomorphLoweringCtx, MethodMonomorphLoweringWork, lower_implement_method_monomorphs,
    lower_type_method_monomorphized_instances,
};
use super::type_methods::{lower_module_type_methods, lower_top_level_type_methods};
use super::vir_monomorph::{
    build_generic_vir_storage, run_early_vir_monomorphize, run_vir_monomorphize,
};
use crate::LoweringEntityLookup;
use crate::TypeArena;
use crate::implement_registry::ImplementRegistry;
use crate::vir_lower::type_translate::sweep_unmapped_type_ids;
use vole_frontend::{Interner, Program};
use vole_identity::{FunctionId, MethodId, ModuleId, NameId, NameTable, Span};
use vole_log::{compile_timed, compile_timing};
use vole_vir::entity_metadata::VirEntityMetadata;
use vole_vir::implement_dispatch::{VirExternalImport, VirImplementDispatch};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirFunction, VirProgram};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub struct LowerVirProgramArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a E,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a crate::NodeMap,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    pub module_id: ModuleId,
    pub modules_with_errors: &'a HashSet<String>,
    pub generic_vir_functions: Vec<(NameId, VirFunction)>,
    /// Shared VIR type table pre-populated by sema analysis.
    ///
    /// Generic VIR templates already use VirTypeIds from this table, so no
    /// merge/remap is needed. Concrete VIR lowering continues interning into
    /// the same table.
    pub vir_type_table: VirTypeTable,
    pub implements: &'a ImplementRegistry,
    /// Optional cache for module VIR output.  When present, the module phase
    /// is skipped on cache hit.  Stores multiple entries keyed by module
    /// path set so that different import combinations don't thrash a single
    /// cache slot.
    pub module_vir_cache: Option<Rc<RefCell<Vec<CachedModuleVir>>>>,
}

pub struct LowerVirProgramOutput {
    pub vir_program: VirProgram,
}

/// Run the codegen-side VIR lowering orchestration and return assembled outputs.
pub fn lower_vir_program<E>(args: LowerVirProgramArgs<'_, E>) -> LowerVirProgramOutput
where
    E: LoweringEntityLookup,
{
    let LowerVirProgramArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        mut module_programs,
        module_id,
        modules_with_errors,
        generic_vir_functions,
        vir_type_table,
        implements,
        module_vir_cache,
    } = args;

    // Collect module paths for cache invalidation.
    let module_paths: Vec<String> = {
        let mut paths: Vec<String> = module_programs.keys().cloned().collect();
        paths.sort();
        paths
    };

    // Build per-file metadata (NOT cached — these depend on shared registries
    // that grow as more modules are analyzed).
    let _t_module_phase = compile_timing!(DEBUG, "module_phase").entered();
    let implement_dispatch = build_implement_dispatch(implements, interner, names);
    let external_imports = collect_external_imports(implements, names);
    let (module_constants, module_exports) = collect_module_metadata(type_arena);

    // Try to use the cached module VIR functions, type table, full
    // entity metadata, and monomorph info (skipping build_entity_metadata
    // and populate_monomorph_info on cache hit).
    let (module_vir_functions, mut type_table, cached_entity_metadata, cached_monomorph_info) =
        match try_use_cache(&module_vir_cache, &module_paths) {
            CacheResult::Hit(cached) => restore_from_cache(
                cached,
                &module_paths,
                &mut module_programs,
                vir_type_table,
                entities,
            ),
            CacheResult::Partial {
                cached,
                delta_paths,
            } => restore_partial_cache(
                cached,
                delta_paths,
                &module_paths,
                &mut module_programs,
                vir_type_table,
                names,
                entities,
                type_arena,
                node_map,
                modules_with_errors,
                implements,
                interner,
                &module_vir_cache,
            ),
            CacheResult::Miss => run_full_module_lowering(
                &module_paths,
                &mut module_programs,
                vir_type_table,
                names,
                entities,
                type_arena,
                node_map,
                modules_with_errors,
                implements,
                interner,
                &module_vir_cache,
            ),
        };

    drop(_t_module_phase);

    // Phase F: file-specific passes.
    let _t_file_phase = compile_timing!(DEBUG, "file_phase").entered();
    lower_file_vir(LowerFileVirArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        module_programs,
        module_id,
        modules_with_errors,
        generic_vir_functions,
        type_table: &mut type_table,
        module_vir: ModuleVirOutput {
            implement_dispatch,
            external_imports,
            module_constants,
            module_exports,
            module_vir_functions,
        },
        implements,
        cached_entity_metadata,
        cached_monomorph_info,
    })
}

// ---------------------------------------------------------------------------
// Cache restore helpers
// ---------------------------------------------------------------------------

/// Restore from an exact cache hit: merge type table, remap VIR functions,
/// and reuse entity metadata and monomorph info.
fn restore_from_cache<E>(
    cached: CachedModuleVir,
    module_paths: &[String],
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    vir_type_table: VirTypeTable,
    entities: &E,
) -> (
    Vec<VirFunction>,
    VirTypeTable,
    Option<VirEntityMetadata>,
    Option<PopulatedMonomorphInfo>,
)
where
    E: LoweringEntityLookup,
{
    let _t = compile_timing!(TRACE, "cache_hit_restore").entered();
    apply_cached_interners(module_programs, &cached.module_interners);

    let mut type_table = vir_type_table;
    let merge_mapping = {
        let _t = compile_timing!(TRACE, "merge_type_table").entered();
        type_table.merge_from_additive(&cached.type_table)
    };

    let needs_remap = merge_mapping.iter().any(|(&old, &new)| old != new);
    let module_vir_functions = if needs_remap {
        let _t = compile_timing!(TRACE, "remap_vir_functions").entered();
        let remap_ctx = vole_vir::monomorph::rewrite::RewriteCtx::new(merge_mapping.clone());
        cached
            .module_vir_functions
            .iter()
            .map(|f| vole_vir::monomorph::rewrite::rewrite_function(f, &remap_ctx))
            .collect()
    } else {
        cached.module_vir_functions
    };

    let entity_metadata = if needs_remap {
        let _t = compile_timing!(TRACE, "remap_entity_metadata").entered();
        vole_vir::remap_entity_metadata(&cached.entity_metadata, &merge_mapping)
    } else {
        cached.entity_metadata
    };

    let current_counts = MonomorphCounts::from_entities(entities);
    let monomorph_info = if current_counts == cached.monomorph_counts {
        if needs_remap {
            let _t = compile_timing!(TRACE, "remap_monomorph_info").entered();
            Some(remap_monomorph_info(&cached.monomorph_info, &merge_mapping))
        } else {
            Some(cached.monomorph_info)
        }
    } else {
        tracing::debug!(
            cached = module_paths.len(),
            "monomorph info cache miss: counts changed"
        );
        None
    };

    (
        module_vir_functions,
        type_table,
        Some(entity_metadata),
        monomorph_info,
    )
}

/// Restore from a partial cache hit: reuse cached base VIR functions and
/// only lower the delta (additional) modules.
#[allow(clippy::too_many_arguments)]
fn restore_partial_cache<E>(
    cached: CachedModuleVir,
    delta_paths: HashSet<String>,
    module_paths: &[String],
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    vir_type_table: VirTypeTable,
    names: &NameTable,
    entities: &E,
    type_arena: &TypeArena,
    node_map: &crate::NodeMap,
    modules_with_errors: &HashSet<String>,
    implements: &ImplementRegistry,
    interner: &mut Interner,
    module_vir_cache: &Option<Rc<RefCell<Vec<CachedModuleVir>>>>,
) -> (
    Vec<VirFunction>,
    VirTypeTable,
    Option<VirEntityMetadata>,
    Option<PopulatedMonomorphInfo>,
)
where
    E: LoweringEntityLookup,
{
    let _t = compile_timing!(TRACE, "cache_partial_hit_restore").entered();
    // Restore cached interners for base modules.
    apply_cached_interners(module_programs, &cached.module_interners);

    // Merge cached type table into this file's sema type table.
    let mut type_table = vir_type_table;
    let merge_mapping = {
        let _t = compile_timing!(TRACE, "merge_type_table").entered();
        type_table.merge_from_additive(&cached.type_table)
    };
    let needs_remap = merge_mapping.iter().any(|(&old, &new)| old != new);

    // Remap cached VIR functions if needed.
    let mut module_vir_functions: Vec<VirFunction> = if needs_remap {
        let _t = compile_timing!(TRACE, "remap_vir_functions").entered();
        let remap_ctx = vole_vir::monomorph::rewrite::RewriteCtx::new(merge_mapping.clone());
        cached
            .module_vir_functions
            .iter()
            .map(|f| vole_vir::monomorph::rewrite::rewrite_function(f, &remap_ctx))
            .collect()
    } else {
        cached.module_vir_functions
    };

    // Build a skip set: mark all modules NOT in the delta as "errored" so
    // the lowering iterators skip them while keeping the full module_programs
    // available for cross-module lookups (e.g. interface default method AST).
    let skip_set = {
        let mut set = modules_with_errors.clone();
        for path in module_programs.keys() {
            if !delta_paths.contains(path) {
                set.insert(path.clone());
            }
        }
        set
    };

    // Lower only the delta modules' VIR functions.
    let mut delta_vir = lower_module_vir_functions(LowerModuleVirArgs {
        names,
        entities,
        type_arena,
        node_map,
        module_programs,
        modules_with_errors: &skip_set,
        type_table: &mut type_table,
        implements,
    });
    module_vir_functions.append(&mut delta_vir);

    // Entity metadata: reuse cached, extend with new entities, and populate
    // implement blocks for delta modules only.
    let mut entity_metadata = if needs_remap {
        let _t = compile_timing!(TRACE, "remap_entity_metadata").entered();
        vole_vir::remap_entity_metadata(&cached.entity_metadata, &merge_mapping)
    } else {
        cached.entity_metadata
    };
    extend_entity_metadata(
        &mut entity_metadata,
        entities,
        type_arena,
        &mut type_table,
        interner,
        names,
    );
    let registry = entities.as_entity_registry();
    let name_to_type_id = build_name_to_type_id_map(registry, type_arena);
    populate_implement_block_entries_modules(
        &mut entity_metadata,
        module_programs,
        &skip_set,
        names,
        entities,
        type_arena,
        &name_to_type_id,
    );

    // Monomorph info: reuse cached if counts haven't changed.
    let current_counts = MonomorphCounts::from_entities(entities);
    let monomorph_info = if current_counts == cached.monomorph_counts {
        if needs_remap {
            let _t = compile_timing!(TRACE, "remap_monomorph_info").entered();
            Some(remap_monomorph_info(&cached.monomorph_info, &merge_mapping))
        } else {
            Some(cached.monomorph_info)
        }
    } else {
        None
    };

    // Compute monomorph info for caching if not reused from the cached entry.
    let store_monomorph_info = match &monomorph_info {
        Some(info) => info.clone(),
        None => populate_monomorph_info(entities, type_arena, &mut type_table),
    };

    // Store the combined result in the cache for future exact hits.
    store_cache(
        module_vir_cache,
        &module_vir_functions,
        &type_table,
        module_programs,
        entity_metadata.clone(),
        store_monomorph_info,
        current_counts,
        module_paths.to_vec(),
    );

    (
        module_vir_functions,
        type_table,
        Some(entity_metadata),
        monomorph_info,
    )
}

/// Full cache miss: lower all modules, build metadata, and store in cache.
#[allow(clippy::too_many_arguments)]
fn run_full_module_lowering<E>(
    module_paths: &[String],
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    vir_type_table: VirTypeTable,
    names: &NameTable,
    entities: &E,
    type_arena: &TypeArena,
    node_map: &crate::NodeMap,
    modules_with_errors: &HashSet<String>,
    implements: &ImplementRegistry,
    interner: &mut Interner,
    module_vir_cache: &Option<Rc<RefCell<Vec<CachedModuleVir>>>>,
) -> (
    Vec<VirFunction>,
    VirTypeTable,
    Option<VirEntityMetadata>,
    Option<PopulatedMonomorphInfo>,
)
where
    E: LoweringEntityLookup,
{
    let mut type_table = vir_type_table;
    let mut module_vir_functions = lower_module_vir_functions(LowerModuleVirArgs {
        names,
        entities,
        type_arena,
        node_map,
        module_programs,
        modules_with_errors,
        type_table: &mut type_table,
        implements,
    });

    {
        let _t = compile_timing!(DEBUG, "lower_implement_method_monomorphized_instances").entered();
        lower_implement_method_monomorphs(
            &mut module_vir_functions,
            &mut type_table,
            entities,
            type_arena,
            names,
        );
    }

    let mut entity_metadata =
        build_entity_metadata(entities, type_arena, &mut type_table, interner, names);
    let registry = entities.as_entity_registry();
    let name_to_type_id = build_name_to_type_id_map(registry, type_arena);
    populate_implement_block_entries_modules(
        &mut entity_metadata,
        module_programs,
        modules_with_errors,
        names,
        entities,
        type_arena,
        &name_to_type_id,
    );

    let monomorph_info = populate_monomorph_info(entities, type_arena, &mut type_table);
    let monomorph_counts = MonomorphCounts::from_entities(entities);

    store_cache(
        module_vir_cache,
        &module_vir_functions,
        &type_table,
        module_programs,
        entity_metadata.clone(),
        monomorph_info.clone(),
        monomorph_counts,
        module_paths.to_vec(),
    );

    (
        module_vir_functions,
        type_table,
        Some(entity_metadata),
        Some(monomorph_info),
    )
}

// ---------------------------------------------------------------------------
// Monomorph counts (for cache invalidation)
// ---------------------------------------------------------------------------

/// Snapshot of entity registry monomorph cache sizes.
///
/// Used to detect whether new monomorphs were registered since the VIR
/// cache was built (e.g. by test-scoped generics in a later file).
#[derive(Clone, Copy, PartialEq, Eq)]
struct MonomorphCounts {
    free: usize,
    class_method: usize,
    static_method: usize,
}

impl MonomorphCounts {
    fn from_entities(entities: &impl LoweringEntityLookup) -> Self {
        Self {
            free: entities.monomorph_keyed_instances().len(),
            class_method: entities.class_method_monomorph_keyed_instances().len(),
            static_method: entities.static_method_monomorph_keyed_instances().len(),
        }
    }
}

// ---------------------------------------------------------------------------
// Module VIR cache
// ---------------------------------------------------------------------------

/// Cached module VIR lowering results for reuse across test file compilations.
///
/// Stores the module VIR functions (the expensive lowering result), a snapshot
/// of the `VirTypeTable`, the module Interners (which contain symbols
/// referenced by the VIR functions), and the full `VirEntityMetadata`
/// (including module-level implement blocks).
///
/// On cache hit, `build_entity_metadata()` is skipped entirely — only the
/// file-specific `populate_implement_block_entries_file()` runs against the
/// pre-built metadata.
///
/// Metadata that depends on shared registries (implement dispatch, module
/// constants, module exports) is NOT cached because those registries grow as
/// more modules are lazily analyzed.
pub struct CachedModuleVir {
    /// VIR functions lowered from imported modules.
    module_vir_functions: Vec<VirFunction>,
    /// Snapshot of the VirTypeTable after module function lowering.
    type_table: VirTypeTable,
    /// Module Interners after mutation by module function lowering.
    ///
    /// VIR functions reference `SymbolId`s that were interned into these
    /// Interners.  On cache hit, we inject these into the current file's
    /// `module_programs` so codegen can resolve those symbols.
    module_interners: FxHashMap<String, Rc<Interner>>,
    /// Full VIR entity metadata including module-level implement blocks.
    ///
    /// On cache hit, this is cloned (and remapped if type table positions
    /// shifted) then passed to `lower_file_vir`, which skips
    /// `build_entity_metadata()` entirely and only runs
    /// `populate_implement_block_entries_file()` for file-specific entries.
    entity_metadata: VirEntityMetadata,
    /// Populated monomorph info (free, class-method, static-method maps).
    ///
    /// `populate_monomorph_info()` reads from the entity registry and
    /// translates type keys via `VirTypeTable`.  On cache hit, the type
    /// table snapshot already contains the interned types, so the cached
    /// result is cloned (and VirTypeId-remapped if the merge shifted IDs).
    ///
    /// Because test-scoped generics can register new monomorphs between
    /// files, we store the entity registry's monomorph counts at cache
    /// time.  If they grow, we fall back to recomputing.
    monomorph_info: PopulatedMonomorphInfo,
    /// Entity registry monomorph counts at cache-store time.
    ///
    /// Used to detect whether new monomorphs were registered since the
    /// cache was built (e.g. by test-scoped generics in a later file).
    monomorph_counts: MonomorphCounts,
    /// Sorted module paths — the cache key for invalidation.
    module_paths: Vec<String>,
}

/// Result of cache lookup: exact hit, partial hit (superset of cached), or miss.
enum CacheResult {
    /// Exact match — all module paths match a cached entry.
    Hit(CachedModuleVir),
    /// Partial match — cached entry is a subset of the requested modules.
    /// Contains the cached data plus the set of module paths NOT in the cache.
    Partial {
        cached: CachedModuleVir,
        delta_paths: HashSet<String>,
    },
    /// No usable cache entry found.
    Miss,
}

/// Attempt to use a cached module VIR result.
///
/// Searches the multi-entry cache for:
///   1. An exact match (all module paths identical)
///   2. A subset match (cached entry's paths are a strict subset of the
///      requested paths) — only the delta modules need lowering.
///
/// For subset matching, selects the entry with the most matching paths
/// to minimize delta work.
fn try_use_cache(
    cache_cell: &Option<Rc<RefCell<Vec<CachedModuleVir>>>>,
    module_paths: &[String],
) -> CacheResult {
    let Some(cache_rc) = cache_cell.as_ref() else {
        return CacheResult::Miss;
    };
    let cache_ref = cache_rc.borrow();
    if cache_ref.is_empty() {
        return CacheResult::Miss;
    }

    let current_set: HashSet<&str> = module_paths.iter().map(|s| s.as_str()).collect();

    // First try exact match (fast path).
    if let Some(cached) = cache_ref
        .iter()
        .find(|entry| entry.module_paths == module_paths)
    {
        let _t = compile_timing!(TRACE, "vir_cache_hit").entered();
        return CacheResult::Hit(clone_cached(cached));
    }

    // Find the best subset match: the cached entry whose paths are all
    // contained in the current set and has the most paths (minimizes delta).
    let best_subset = cache_ref
        .iter()
        .filter(|entry| {
            entry
                .module_paths
                .iter()
                .all(|p| current_set.contains(p.as_str()))
        })
        .max_by_key(|entry| entry.module_paths.len());

    if let Some(base) = best_subset {
        let base_set: HashSet<&str> = base.module_paths.iter().map(|s| s.as_str()).collect();
        let delta_paths: HashSet<String> = current_set
            .difference(&base_set)
            .map(|s| s.to_string())
            .collect();
        let _t = compile_timing!(TRACE, "vir_cache_partial_hit").entered();
        return CacheResult::Partial {
            cached: clone_cached(base),
            delta_paths,
        };
    }

    CacheResult::Miss
}

/// Clone a cached entry for use by the current file.
fn clone_cached(cached: &CachedModuleVir) -> CachedModuleVir {
    CachedModuleVir {
        module_vir_functions: cached.module_vir_functions.clone(),
        type_table: cached.type_table.clone(),
        module_interners: cached.module_interners.clone(),
        entity_metadata: cached.entity_metadata.clone(),
        monomorph_info: cached.monomorph_info.clone(),
        monomorph_counts: cached.monomorph_counts,
        module_paths: cached.module_paths.clone(),
    }
}

/// Store module VIR lowering results in the cache.
///
/// Appends a new entry to the multi-entry cache.  Each entry is keyed by
/// its sorted `module_paths`, so different import combinations coexist
/// without thrashing.
fn store_cache(
    cache_cell: &Option<Rc<RefCell<Vec<CachedModuleVir>>>>,
    module_vir_functions: &[VirFunction],
    type_table: &VirTypeTable,
    module_programs: &FxHashMap<String, (Program, Rc<Interner>)>,
    entity_metadata: VirEntityMetadata,
    monomorph_info: PopulatedMonomorphInfo,
    monomorph_counts: MonomorphCounts,
    module_paths: Vec<String>,
) {
    if let Some(cache_rc) = cache_cell.as_ref() {
        let module_interners: FxHashMap<String, Rc<Interner>> = module_programs
            .iter()
            .map(|(path, (_prog, interner))| (path.clone(), Rc::clone(interner)))
            .collect();
        let _t = compile_timing!(TRACE, "vir_cache_miss").entered();
        cache_rc.borrow_mut().push(CachedModuleVir {
            module_vir_functions: module_vir_functions.to_vec(),
            type_table: type_table.clone(),
            module_interners,
            entity_metadata,
            monomorph_info,
            monomorph_counts,
            module_paths,
        });
    }
}

/// Apply cached module interners to the current file's module programs.
///
/// On a cache hit, the VIR functions reference symbols that were interned
/// during the first file's module lowering.  This function replaces the
/// Interner in each module program entry with the cached (mutated) version
/// so codegen can resolve those symbols.
fn apply_cached_interners(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    cached_interners: &FxHashMap<String, Rc<Interner>>,
) {
    for (path, (_prog, interner)) in module_programs.iter_mut() {
        if let Some(cached_interner) = cached_interners.get(path) {
            *interner = Rc::clone(cached_interner);
        }
    }
}

// ---------------------------------------------------------------------------
// Module VIR output: all results from module-only (cacheable) passes
// ---------------------------------------------------------------------------

/// Output from module-only VIR lowering passes.
///
/// Contains VIR data produced by passes that only depend on imported modules
/// and shared entity state (not on the specific file being compiled).
/// Cached across test file compilations via `CachedModuleVir`.
#[derive(Clone)]
pub struct ModuleVirOutput {
    /// Implement-dispatch metadata from the implement registry.
    pub implement_dispatch: VirImplementDispatch,
    /// Pre-resolved external function imports for codegen pre-declaration.
    pub external_imports: Vec<VirExternalImport>,
    /// Per-module compile-time constant values.
    pub module_constants: FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>,
    /// Module type exports.
    pub module_exports:
        FxHashMap<vole_identity::TypeId, (ModuleId, Vec<(NameId, vole_identity::TypeId)>)>,
    /// VIR functions lowered from imported modules (functions, type methods,
    /// implement-block methods).  Prepended to the file's function list.
    pub module_vir_functions: Vec<VirFunction>,
}

// ---------------------------------------------------------------------------
// Module VIR lowering args
// ---------------------------------------------------------------------------

/// Arguments for the module-only VIR function lowering pass.
struct LowerModuleVirArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    names: &'a NameTable,
    entities: &'a E,
    type_arena: &'a TypeArena,
    node_map: &'a crate::NodeMap,
    module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    modules_with_errors: &'a HashSet<String>,
    type_table: &'a mut VirTypeTable,
    implements: &'a ImplementRegistry,
}

// ---------------------------------------------------------------------------
// File VIR lowering args
// ---------------------------------------------------------------------------

/// Arguments for the file-specific VIR lowering pass.
struct LowerFileVirArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    program: &'a Program,
    interner: &'a mut Interner,
    names: &'a NameTable,
    entities: &'a E,
    type_arena: &'a TypeArena,
    node_map: &'a crate::NodeMap,
    tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    module_id: ModuleId,
    modules_with_errors: &'a HashSet<String>,
    generic_vir_functions: Vec<(NameId, VirFunction)>,
    type_table: &'a mut VirTypeTable,
    module_vir: ModuleVirOutput,
    implements: &'a ImplementRegistry,
    /// Cached entity metadata from a previous compilation.
    ///
    /// When `Some`, `build_entity_metadata()` is skipped entirely — only
    /// `populate_implement_block_entries_file()` runs to add file-specific
    /// implement blocks to the pre-built metadata.
    cached_entity_metadata: Option<VirEntityMetadata>,
    /// Cached monomorph info from a previous compilation.
    ///
    /// When `Some`, `populate_monomorph_info()` is skipped — the cached
    /// result (already VirTypeId-remapped) is used directly.
    cached_monomorph_info: Option<PopulatedMonomorphInfo>,
}

// ---------------------------------------------------------------------------
// Phase M: module-only passes
// ---------------------------------------------------------------------------

/// Lower module VIR functions (functions, type methods, implement-block methods).
///
/// This is the expensive part of module lowering — the main cache target.
/// Mutates `module_programs` in place (Interner gains new symbols via
/// `Rc::make_mut`).  The mutated Interners are later cached so subsequent
/// files can resolve VIR function symbol references.
fn lower_module_vir_functions<E>(args: LowerModuleVirArgs<'_, E>) -> Vec<VirFunction>
where
    E: LoweringEntityLookup,
{
    let LowerModuleVirArgs {
        names,
        entities,
        type_arena,
        node_map,
        module_programs,
        modules_with_errors,
        type_table,
        implements,
    } = args;

    // Compute prelude module IDs so each module's CrossModuleCtx can find
    // sibling prelude functions (e.g. assert calling panic).
    let prelude_module_ids: Vec<ModuleId> = module_programs
        .keys()
        .filter(|path| path.starts_with("std:prelude/"))
        .filter_map(|path| names.module_id_if_known(path))
        .collect();

    let mut module_vir_functions = Vec::new();
    lower_module_functions(LowerModuleFunctionsArgs {
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions: &mut module_vir_functions,
        type_table,
        prelude_module_ids: &prelude_module_ids,
        implements,
    });
    lower_module_type_methods(
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        &mut module_vir_functions,
        type_table,
        &prelude_module_ids,
        implements,
    );
    lower_module_implement_block_methods(LowerModuleImplementBlockMethodsArgs {
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions: &mut module_vir_functions,
        type_table,
        prelude_module_ids: &prelude_module_ids,
        implements,
    });

    module_vir_functions
}

// ---------------------------------------------------------------------------
// Phase F: file-specific passes (+ type-table-dependent module passes)
// ---------------------------------------------------------------------------

/// Run file-specific VIR lowering passes and assemble the final VirProgram.
fn lower_file_vir<E>(args: LowerFileVirArgs<'_, E>) -> LowerVirProgramOutput
where
    E: LoweringEntityLookup,
{
    let LowerFileVirArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        mut module_programs,
        module_id,
        modules_with_errors,
        generic_vir_functions,
        type_table,
        module_vir,
        implements,
        cached_entity_metadata,
        cached_monomorph_info,
    } = args;

    // Destructure module_vir up front so we can move fields independently.
    let ModuleVirOutput {
        implement_dispatch: module_implement_dispatch,
        external_imports,
        module_constants,
        module_exports,
        module_vir_functions,
    } = module_vir;

    // -----------------------------------------------------------------------
    // Cross-module call resolution context
    // -----------------------------------------------------------------------

    // Extract lightweight module bindings (Symbol → (ModuleId, Symbol)) from
    // destructured imports for VIR call resolution.  This runs before function
    // lowering so that `resolve_callee_function` can resolve cross-module
    // calls to `CallTarget::Direct` instead of falling through to codegen's
    // `call_dispatch()`.
    let xmod_bindings = extract_cross_module_bindings(program, node_map, type_arena);

    // Compute prelude module IDs from module_programs keys.
    let prelude_module_ids: Vec<_> = module_programs
        .keys()
        .filter(|path| path.starts_with("std:prelude/"))
        .filter_map(|path| names.module_id_if_known(path))
        .collect();

    let cross_module_ctx = crate::vir_lower::CrossModuleCtx {
        module_bindings: xmod_bindings,
        prelude_module_ids: prelude_module_ids.clone(),
    };

    // -----------------------------------------------------------------------
    // Function lowering (file-level + cached module functions)
    // -----------------------------------------------------------------------

    // File functions first, then module functions (preserves original ordering).
    let mut vir_functions = {
        let _timing = compile_timing!(DEBUG, "lower_top_level_functions").entered();
        let mut fns = lower_top_level_functions(LowerTopLevelFunctionsArgs {
            program,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            type_table,
            cross_module: &cross_module_ctx,
            implements,
        });
        fns.extend(module_vir_functions);
        fns
    };

    // -----------------------------------------------------------------------
    // Monomorphization (mixed pass)
    // -----------------------------------------------------------------------

    let (generic_vir_functions, generic_vir_map) = build_generic_vir_storage(generic_vir_functions);
    let early_instance_index = run_early_vir_monomorphize(
        &mut vir_functions,
        &generic_vir_functions,
        &generic_vir_map,
        type_table,
        entities,
        type_arena,
    );

    // -----------------------------------------------------------------------
    // Type methods and implement-block methods (file-level only)
    // -----------------------------------------------------------------------

    lower_top_level_type_methods(
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        Some(&module_programs),
        &mut vir_functions,
        type_table,
        &cross_module_ctx,
        implements,
    );
    // Note: module type methods and module implement-block methods are now
    // handled in the module phase (cached).
    lower_implement_block_methods(LowerImplementBlockMethodsArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        vir_functions: &mut vir_functions,
        type_table,
        cross_module: &cross_module_ctx,
        implements,
    });

    // -----------------------------------------------------------------------
    // Test-scoped type methods and method monomorphization
    // -----------------------------------------------------------------------

    lower_test_scoped_type_methods(
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        Some(&module_programs),
        module_id,
        &mut vir_functions,
        type_table,
        &cross_module_ctx,
        implements,
    );
    let method_monomorph_ctx = MethodMonomorphLoweringCtx {
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        cross_module: &cross_module_ctx,
        implements,
    };
    let mut method_monomorph_work = MethodMonomorphLoweringWork {
        program,
        interner,
        module_programs: &mut module_programs,
        tests_virtual_modules,
        module_id,
        vir_functions: &mut vir_functions,
        type_table,
    };
    lower_type_method_monomorphized_instances(&mut method_monomorph_work, &method_monomorph_ctx);
    // Note: lower_implement_method_monomorphized_instances has been moved to
    // the module phase (computed once, cached for subsequent files).

    // -----------------------------------------------------------------------
    // Lookup maps
    // -----------------------------------------------------------------------

    let (vir_monomorph_map, vir_function_map, vir_method_map) = {
        let _t = compile_timing!(DEBUG, "build_lookup_maps").entered();
        (
            build_vir_monomorph_map(&vir_functions),
            build_vir_function_map(&vir_functions),
            build_vir_method_map(&vir_functions),
        )
    };

    // -----------------------------------------------------------------------
    // Test bodies, global inits, module bindings (file + module)
    // -----------------------------------------------------------------------

    let vir_tests = lower_test_bodies(
        program,
        node_map,
        interner,
        type_arena,
        entities,
        names,
        type_table,
        module_id,
        &cross_module_ctx,
        implements,
    );
    let _t_globals = compile_timing!(DEBUG, "lower_global_inits").entered();
    let vir_global_inits = lower_global_inits(
        program,
        interner,
        node_map,
        type_arena,
        entities,
        names,
        type_table,
        module_id,
        &cross_module_ctx,
        implements,
    );
    let module_vir_global_inits = lower_module_global_inits(
        &mut module_programs,
        names,
        node_map,
        type_arena,
        entities,
        modules_with_errors,
        type_table,
        &prelude_module_ids,
        implements,
    );
    drop(_t_globals);

    let _t_bindings = compile_timing!(DEBUG, "lower_module_bindings").entered();
    let vir_module_bindings =
        lower_module_bindings(program, node_map, type_arena, names, interner, type_table);
    let vir_module_module_bindings = lower_module_module_bindings(
        &mut module_programs,
        names,
        node_map,
        type_arena,
        modules_with_errors,
        type_table,
    );

    drop(_t_bindings);

    // -----------------------------------------------------------------------
    // Default inits (file + module)
    // -----------------------------------------------------------------------

    let _t_defaults = compile_timing!(DEBUG, "lower_default_inits").entered();
    let mut vir_function_default_inits =
        lower_function_default_inits(LowerFunctionDefaultInitsArgs {
            program,
            interner,
            module_id,
            tests_virtual_modules,
            names,
            entities,
            node_map,
            type_arena,
            type_table,
            cross_module: &cross_module_ctx,
            implements,
        });
    // Module function defaults (type-table-dependent, logically module-only).
    // Uses the main interner so that VIR StringLiteral symbols are resolvable
    // from the main interner at codegen call sites (cross-module calls).
    let module_vir_function_default_inits =
        lower_module_function_default_inits(LowerModuleFunctionDefaultInitsArgs {
            module_programs: &mut module_programs,
            main_interner: interner,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table,
            prelude_module_ids: &prelude_module_ids,
            implements,
        });
    vir_function_default_inits.extend(module_vir_function_default_inits);

    let mut vir_method_default_inits = lower_method_default_inits(LowerMethodDefaultInitsArgs {
        program,
        interner,
        module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        type_table,
        cross_module: &cross_module_ctx,
        implements,
    });
    // Module method defaults (type-table-dependent, logically module-only).
    // Uses the main interner for the same cross-module re-interning reason.
    let module_vir_method_default_inits =
        lower_module_method_default_inits(LowerModuleMethodDefaultInitsArgs {
            module_programs: &mut module_programs,
            main_interner: interner,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table,
            prelude_module_ids: &prelude_module_ids,
            implements,
        });
    vir_method_default_inits.extend(module_vir_method_default_inits);

    // Lambda default inits (mixed pass).
    let vir_lambda_default_inits = lower_lambda_default_inits(LowerLambdaDefaultInitsArgs {
        program,
        interner,
        module_programs: &mut module_programs,
        main_module_id: module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        modules_with_errors,
        type_table,
        cross_module: &cross_module_ctx,
        implements,
    });

    let mut vir_field_default_inits = lower_field_default_inits(LowerFieldDefaultInitsArgs {
        program,
        interner,
        module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        type_table,
        cross_module: &cross_module_ctx,
        implements,
    });
    // Module field defaults (type-table-dependent, logically module-only).
    let module_vir_field_default_inits =
        lower_module_field_default_inits(LowerModuleFieldDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table,
            prelude_module_ids: &prelude_module_ids,
            implements,
        });
    vir_field_default_inits.extend(module_vir_field_default_inits);

    drop(_t_defaults);

    // -----------------------------------------------------------------------
    // Entity metadata and monomorph info
    // -----------------------------------------------------------------------

    let _t_entity = compile_timing!(DEBUG, "entity_metadata_and_monomorph_info").entered();
    let monomorph_info = if let Some(cached) = cached_monomorph_info {
        cached
    } else {
        populate_monomorph_info(entities, type_arena, type_table)
    };
    let vir_annotation_inits = lower_annotation_inits(entities, interner, names);
    let entity_metadata = if let Some(cached_meta) = cached_entity_metadata {
        // Cache hit: extend with entities registered after the cache was
        // built (e.g. test-scoped types/functions), then populate
        // file-specific implement block entries.
        let mut meta = cached_meta;
        extend_entity_metadata(&mut meta, entities, type_arena, type_table, interner, names);
        let registry = entities.as_entity_registry();
        let name_to_type_id = build_name_to_type_id_map(registry, type_arena);
        populate_implement_block_entries_file(
            &mut meta,
            program,
            interner,
            names,
            entities,
            type_arena,
            module_id,
            &name_to_type_id,
        );
        meta
    } else {
        // No cache — build entity metadata and populate all implement
        // block entries (file + modules).
        let mut meta = build_entity_metadata(entities, type_arena, type_table, interner, names);
        populate_implement_block_entries(PopulateImplementBlockEntriesArgs {
            program,
            interner,
            names,
            entities,
            type_arena,
            module_id,
            module_programs: &module_programs,
            modules_with_errors,
            meta: &mut meta,
        });
        meta
    };

    drop(_t_entity);

    // Collect module interners from module_programs for VirProgram.
    let module_interners: FxHashMap<String, Rc<Interner>> = module_programs
        .iter()
        .map(|(path, (_program, interner))| (path.clone(), Rc::clone(interner)))
        .collect();

    // -----------------------------------------------------------------------
    // Assemble the final VirProgram
    // -----------------------------------------------------------------------

    let _timing = compile_timing!(DEBUG, "assemble_vir_program").entered();
    assemble_vir_program(AssembleVirProgramArgs {
        vir_functions,
        vir_monomorph_map,
        vir_function_map,
        vir_method_map,
        generic_vir_functions,
        generic_vir_map,
        vir_tests,
        vir_global_inits,
        module_vir_global_inits,
        vir_function_default_inits,
        vir_method_default_inits,
        vir_lambda_default_inits,
        vir_field_default_inits,
        vir_annotation_inits,
        vir_module_bindings,
        vir_module_module_bindings,
        module_implement_dispatch,
        external_imports,
        module_constants,
        module_exports,
        monomorph_info,
        entity_metadata,
        module_interners,
        early_instance_index,
        type_table,
        type_arena,
    })
}

// ---------------------------------------------------------------------------
// VirProgram assembly (extracted to keep lower_file_vir under 80 lines)
// ---------------------------------------------------------------------------

struct AssembleVirProgramArgs<'a> {
    vir_functions: Vec<VirFunction>,
    vir_monomorph_map: FxHashMap<NameId, usize>,
    vir_function_map: FxHashMap<FunctionId, usize>,
    vir_method_map: FxHashMap<MethodId, usize>,
    generic_vir_functions: Vec<VirFunction>,
    generic_vir_map: FxHashMap<NameId, usize>,
    vir_tests: Vec<vole_vir::func::VirTest>,
    vir_global_inits: FxHashMap<vole_identity::Symbol, vole_vir::refs::VirRef>,
    module_vir_global_inits:
        FxHashMap<String, FxHashMap<vole_identity::Symbol, vole_vir::refs::VirRef>>,
    vir_function_default_inits: FxHashMap<(FunctionId, usize), vole_vir::refs::VirRef>,
    vir_method_default_inits: FxHashMap<(MethodId, usize), vole_vir::refs::VirRef>,
    vir_lambda_default_inits: FxHashMap<(vole_identity::NodeId, usize), vole_vir::refs::VirRef>,
    vir_field_default_inits: FxHashMap<vole_identity::FieldId, vole_vir::refs::VirRef>,
    vir_annotation_inits: FxHashMap<vole_identity::FieldId, Vec<vole_vir::types::VirAnnotation>>,
    vir_module_bindings: FxHashMap<
        vole_identity::Symbol,
        (ModuleId, vole_identity::Symbol, vole_identity::VirTypeId),
    >,
    vir_module_module_bindings: FxHashMap<
        String,
        FxHashMap<
            vole_identity::Symbol,
            (ModuleId, vole_identity::Symbol, vole_identity::VirTypeId),
        >,
    >,
    module_implement_dispatch: VirImplementDispatch,
    external_imports: Vec<VirExternalImport>,
    module_constants: FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>,
    module_exports:
        FxHashMap<vole_identity::TypeId, (ModuleId, Vec<(NameId, vole_identity::TypeId)>)>,
    monomorph_info: PopulatedMonomorphInfo,
    entity_metadata: VirEntityMetadata,
    module_interners: FxHashMap<String, Rc<Interner>>,
    early_instance_index: vole_vir::InstanceIndex,
    type_table: &'a mut VirTypeTable,
    type_arena: &'a TypeArena,
}

fn assemble_vir_program(args: AssembleVirProgramArgs<'_>) -> LowerVirProgramOutput {
    let AssembleVirProgramArgs {
        vir_functions,
        vir_monomorph_map,
        vir_function_map,
        vir_method_map,
        generic_vir_functions,
        generic_vir_map,
        vir_tests,
        vir_global_inits,
        module_vir_global_inits,
        vir_function_default_inits,
        vir_method_default_inits,
        vir_lambda_default_inits,
        vir_field_default_inits,
        vir_annotation_inits,
        vir_module_bindings,
        vir_module_module_bindings,
        module_implement_dispatch,
        external_imports,
        module_constants,
        module_exports,
        monomorph_info,
        entity_metadata,
        module_interners,
        early_instance_index,
        type_table,
        type_arena,
    } = args;

    let mut vir_program = VirProgram {
        type_table: std::mem::take(type_table),
        functions: vir_functions,
        monomorph_map: vir_monomorph_map,
        function_map: vir_function_map,
        method_map: vir_method_map,
        generic_functions: generic_vir_functions,
        generic_map: generic_vir_map,
        tests: vir_tests,
        global_inits: vir_global_inits,
        module_global_inits: module_vir_global_inits,
        function_default_inits: vir_function_default_inits,
        method_default_inits: vir_method_default_inits,
        lambda_default_inits: vir_lambda_default_inits,
        field_default_inits: vir_field_default_inits,
        annotation_inits: vir_annotation_inits,
        module_bindings: vir_module_bindings,
        module_module_bindings: vir_module_module_bindings,
        module_constants,
        module_exports,
        vir_monomorph_base: early_instance_index
            .values()
            .copied()
            .min()
            .unwrap_or(usize::MAX),
        vir_instance_index: early_instance_index,
        entity_metadata,
        implement_dispatch: module_implement_dispatch,
        external_imports,
        free_monomorphs: monomorph_info.free_monomorphs,
        free_monomorphs_by_key: monomorph_info.free_monomorphs_by_key,
        class_method_monomorphs: monomorph_info.class_method_monomorphs,
        static_method_monomorphs: monomorph_info.static_method_monomorphs,
        implement_method_monomorphs: monomorph_info.implement_method_monomorphs,
        module_interners,
        interner: Rc::new(Interner::new()),
        name_table: Rc::new(NameTable::new()),
        tests_virtual_modules: FxHashMap::default(),
        module_id: ModuleId::new(0),
        modules_with_errors: HashSet::new(),
        substitute_fallback: None,
    };
    run_vir_monomorphize(&mut vir_program);

    // Sweep all TypeIds in the arena and populate VirTypeId mappings for any
    // that were not encountered during on-demand lowering.
    sweep_unmapped_type_ids(&mut vir_program.type_table, type_arena);

    LowerVirProgramOutput { vir_program }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Collect module metadata (constants and exports) from the type arena for
/// codegen to use without direct arena access.
type ModuleConstants = FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>;
type ModuleExports =
    FxHashMap<vole_identity::TypeId, (ModuleId, Vec<(NameId, vole_identity::TypeId)>)>;

#[compile_timed(TRACE)]
fn collect_module_metadata(type_arena: &TypeArena) -> (ModuleConstants, ModuleExports) {
    let mut constants = FxHashMap::default();
    let mut exports = FxHashMap::default();

    for (module_id, meta) in type_arena.all_module_metadata() {
        for (name_id, value) in &meta.constants {
            constants.insert((*module_id, *name_id), value.clone());
        }
    }

    for (type_id, module_info) in type_arena.all_module_types() {
        let export_vec: Vec<(NameId, vole_identity::TypeId)> =
            module_info.exports.iter().map(|&(n, t)| (n, t)).collect();
        exports.insert(type_id, (module_info.module_id, export_vec));
    }

    (constants, exports)
}

fn build_vir_monomorph_map(vir_functions: &[VirFunction]) -> FxHashMap<NameId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(name_id) = vf.mangled_name_id {
            map.insert(name_id, idx);
        }
    }
    map
}

fn build_vir_function_map(vir_functions: &[VirFunction]) -> FxHashMap<FunctionId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if vf.mangled_name_id.is_none() && vf.method_id.is_none() {
            map.insert(vf.id, idx);
        }
    }
    map
}

fn build_vir_method_map(vir_functions: &[VirFunction]) -> FxHashMap<MethodId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(method_id) = vf.method_id {
            map.insert(method_id, idx);
        }
    }
    map
}

/// Build VIR implement-dispatch metadata from sema's `ImplementRegistry`.
///
/// Pre-interns module_path and native_name strings as `Symbol`s so the
/// post-monomorphization rederive pass can construct `CallTarget::Native`
/// without needing `&mut Interner`.
#[compile_timed(TRACE)]
fn build_implement_dispatch(
    registry: &ImplementRegistry,
    interner: &mut Interner,
    names: &NameTable,
) -> VirImplementDispatch {
    use crate::implement_registry::ImplTypeId;
    use vole_vir::{VirExternalFuncInfo, VirFuncSignature, VirMethodImplInfo};

    let mut dispatch = VirImplementDispatch::new();

    for (name, info) in registry.external_func_entries() {
        let module_path_str = names.last_segment_str(info.module_path).unwrap_or_default();
        let native_name_str = names.last_segment_str(info.native_name).unwrap_or_default();
        dispatch.insert_external_func(
            name.to_string(),
            VirExternalFuncInfo {
                module_path: info.module_path,
                native_name: info.native_name,
                module_path_sym: interner.intern(&module_path_str),
                native_name_sym: interner.intern(&native_name_str),
            },
        );
    }

    for (name, info) in registry.generic_external_entries() {
        dispatch.insert_generic_external(name.to_string(), convert_generic_info(info));
    }

    for (key, info) in registry.generic_external_method_entries() {
        dispatch.insert_generic_external_method(
            key.type_def_id,
            key.method_name,
            convert_generic_info(info),
        );
    }

    for (key, method_impl) in registry.method_entries() {
        let type_name_id = ImplTypeId::name_id(key.type_id);
        dispatch.insert_method(
            type_name_id,
            key.method_name,
            VirMethodImplInfo {
                func_sig: VirFuncSignature {
                    is_closure: method_impl.func_type.is_closure,
                    params: method_impl.func_type.params_id.to_vec(),
                    return_type: method_impl.func_type.return_type_id,
                },
                external_info: method_impl.external_info.map(|ei| {
                    let mp_str = names.last_segment_str(ei.module_path).unwrap_or_default();
                    let nn_str = names.last_segment_str(ei.native_name).unwrap_or_default();
                    VirExternalFuncInfo {
                        module_path: ei.module_path,
                        native_name: ei.native_name,
                        module_path_sym: interner.intern(&mp_str),
                        native_name_sym: interner.intern(&nn_str),
                    }
                }),
            },
        );
    }

    dispatch
}

/// Collect all external function imports from sema's `ImplementRegistry`.
///
/// Extracts `(module_path, func_name)` pairs from:
/// - Top-level external function entries (`external("mod") { func name() }`)
/// - Implement-block method entries with external bindings
///
/// These are stored in `VirProgram.external_imports` so codegen can
/// pre-declare all native imports before any compilation begins.
#[compile_timed(TRACE)]
fn collect_external_imports(
    registry: &ImplementRegistry,
    names: &NameTable,
) -> Vec<VirExternalImport> {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut imports = Vec::new();

    // Collect from top-level external functions.
    for (_name, info) in registry.external_func_entries() {
        let module_path = names.last_segment_str(info.module_path).unwrap_or_default();
        let func_name = names.last_segment_str(info.native_name).unwrap_or_default();
        let key = (module_path.clone(), func_name.clone());
        if seen.insert(key) {
            imports.push(VirExternalImport {
                module_path,
                func_name,
            });
        }
    }

    // Collect from implement-block method entries with external bindings.
    for (_key, method_impl) in registry.method_entries() {
        if let Some(ei) = method_impl.external_info {
            let module_path = names.last_segment_str(ei.module_path).unwrap_or_default();
            let func_name = names.last_segment_str(ei.native_name).unwrap_or_default();
            let key = (module_path.clone(), func_name.clone());
            if seen.insert(key) {
                imports.push(VirExternalImport {
                    module_path,
                    func_name,
                });
            }
        }
    }

    imports
}

fn convert_generic_info(
    info: &crate::implement_registry::GenericExternalInfo,
) -> vole_vir::VirGenericExternalInfo {
    use vole_vir::{VirGenericExternalInfo, VirTypeMappingEntry, VirTypeMappingKind};

    VirGenericExternalInfo {
        module_path: info.module_path,
        type_mappings: info
            .type_mappings
            .iter()
            .map(|entry| VirTypeMappingEntry {
                kind: match &entry.kind {
                    crate::implement_registry::TypeMappingKind::Exact(type_id) => {
                        VirTypeMappingKind::Exact(*type_id)
                    }
                    crate::implement_registry::TypeMappingKind::Default => {
                        VirTypeMappingKind::Default
                    }
                },
                intrinsic_key: entry.intrinsic_key.clone(),
            })
            .collect(),
    }
}
