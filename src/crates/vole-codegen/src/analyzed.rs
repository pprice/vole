// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use vole_frontend::{Decl, Interner, Program, Span};
use vole_identity::{ModuleId, NameId, NameTable, NamerLookup};
use vole_sema::{
    AnalysisOutput, CodegenDb, EntityRegistry, ImplementRegistry, NodeMap, ProgramQuery, TypeArena,
};
use vole_vir::{VirFunction, lower_function, lower_monomorphized_function};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Rc<Interner>,
    /// All expression-level metadata (types, method resolutions, generic calls).
    /// Vec-backed per-node store, keyed by `NodeId`.
    pub node_map: NodeMap,
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    /// Keyed by Span (not NodeId), so stored separately from NodeId-keyed NodeMap.
    pub tests_virtual_modules: FxHashMap<Span, ModuleId>,
    /// Parsed module programs for compiling pure Vole functions
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    /// Compilation database converted for codegen use (Rc-shared, immutable)
    pub db: CodegenDb,
    /// The module ID for the main program (may differ from main_module when using shared cache)
    pub module_id: ModuleId,
    /// Module paths that had sema errors. Codegen should skip compiling
    /// function bodies for these modules to avoid INVALID type IDs.
    pub modules_with_errors: HashSet<String>,
    /// VIR-lowered functions (Phase 0: top-level non-generic functions and
    /// their monomorphized instances).
    pub vir_functions: Vec<VirFunction>,
    /// Lookup map from monomorphized mangled NameId to index in `vir_functions`.
    /// Enables O(1) VIR function lookup during monomorphized compilation.
    pub vir_monomorph_map: FxHashMap<NameId, usize>,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    ///
    /// When the CompilationDb has a single owner (non-cached path), unwraps it
    /// directly. When shared (cached path, where module cache holds a reference),
    /// creates a CodegenDb that shares all data via Rc (O(1), zero cloning).
    pub fn from_analysis(program: Program, interner: Interner, output: AnalysisOutput) -> Self {
        let db = match Rc::try_unwrap(output.db) {
            // Non-cached path: sole owner, move data directly (zero-cost)
            Ok(compilation_db) => compilation_db.into_codegen(),
            // Cached path: share Rc-wrapped fields instead of cloning entire CompilationDb
            Err(rc) => rc.to_codegen_shared(),
        };
        let mut vir_functions = lower_top_level_functions(
            &program,
            &interner,
            &db.names,
            &db.entities,
            &output.node_map,
            output.module_id,
        );
        let generic_func_asts =
            build_generic_func_map(&program, &interner, &db.names, output.module_id);
        lower_monomorphized_instances(
            &generic_func_asts,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &mut vir_functions,
        );
        let vir_monomorph_map = build_vir_monomorph_map(&vir_functions);
        Self {
            program,
            interner: Rc::new(interner),
            node_map: output.node_map,
            tests_virtual_modules: output.tests_virtual_modules,
            module_programs: output.module_programs,
            db,
            module_id: output.module_id,
            modules_with_errors: output.modules_with_errors,
            vir_functions,
            vir_monomorph_map,
        }
    }

    /// Get a query interface for accessing type information and analysis results.
    pub fn query(&self) -> ProgramQuery<'_> {
        ProgramQuery::new(
            self.entity_registry(),
            &self.node_map,
            &self.tests_virtual_modules,
            self.name_table_ref(),
            &self.interner,
            self.implement_registry(),
            &self.module_programs,
            self.type_arena(),
        )
    }

    /// Get read-only access to the name table
    pub fn name_table(&self) -> &NameTable {
        &self.db.names
    }

    /// Get a shared reference to the name table Rc (cloned)
    pub fn name_table_rc(&self) -> Rc<NameTable> {
        Rc::clone(self.name_table_ref())
    }

    /// Get a reference to the name table Rc (borrowed, no clone)
    pub fn name_table_ref(&self) -> &Rc<NameTable> {
        &self.db.names
    }

    /// Get read-only access to the type arena
    pub fn type_arena(&self) -> &TypeArena {
        &self.db.types
    }

    /// Get read-only access to entity registry
    pub fn entity_registry(&self) -> &EntityRegistry {
        &self.db.entities
    }

    /// Get read-only access to implement registry
    pub fn implement_registry(&self) -> &ImplementRegistry {
        &self.db.implements
    }

    /// Look up a VIR function by its monomorphized mangled NameId.
    /// Returns `None` if no VIR function was lowered for this instance.
    pub fn get_vir_monomorph(&self, mangled_name_id: NameId) -> Option<&VirFunction> {
        self.vir_monomorph_map
            .get(&mangled_name_id)
            .map(|&idx| &self.vir_functions[idx])
    }
}

/// Lower top-level non-generic functions to VIR.
///
/// Iterates the program's declarations, looks up each non-generic function
/// in the entity registry, and calls `lower_function()` to produce a
/// `VirFunction`.  Generic functions and implicit generics are skipped
/// because they are monomorphized during codegen.
fn lower_top_level_functions(
    program: &Program,
    interner: &Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    node_map: &NodeMap,
    module_id: ModuleId,
) -> Vec<VirFunction> {
    let namer = NamerLookup::new(names, interner);
    let mut vir_functions = Vec::new();

    for decl in &program.declarations {
        let Decl::Function(func) = decl else { continue };
        // Skip generic functions — they are templates, not concrete
        if !func.type_params.is_empty() {
            continue;
        }
        // Look up the semantic FunctionId via NameTable
        let Some(name_id) = namer.function(module_id, func.name) else {
            continue;
        };
        let Some(func_id) = entities.function_by_name(name_id) else {
            continue;
        };
        let func_def = entities.get_function(func_id);
        // Skip implicit generics (structural type params)
        if func_def.generic_info.is_some() {
            continue;
        }
        // Build (Symbol, TypeId) pairs from AST param names + sema types
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(func_def.signature.params_id.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();
        let display_name = interner.resolve(func.name).to_string();
        let vir = lower_function(
            func,
            func_id,
            display_name,
            &param_types,
            func_def.signature.return_type_id,
            node_map,
        );
        vir_functions.push(vir);
    }

    vir_functions
}

/// Lower monomorphized function instances to VIR.
///
/// For each concrete instance in the monomorph cache, finds the generic
/// function's AST via `generic_func_asts` and lowers it with the substituted
/// (concrete) param and return types from the instance's `func_type`.
/// The body remains Ast-wrapped (Phase 2 migrates bodies).
///
/// Debug-asserts that no `TypeId` in the output contains a type parameter.
fn lower_monomorphized_instances(
    generic_func_asts: &FxHashMap<NameId, &vole_frontend::FuncDecl>,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    vir_functions: &mut Vec<VirFunction>,
) {
    // Iterate all monomorphized instances in the cache
    for (_, instance) in entities.monomorph_cache.instances() {
        let Some(func) = generic_func_asts.get(&instance.original_name) else {
            // AST not in the main program — may be in a module.
            // Module-originating monomorphs are lowered separately (future).
            continue;
        };

        // Look up the original FunctionId for the generic template
        let Some(func_id) = entities.function_by_name(instance.original_name) else {
            continue;
        };

        // Build (Symbol, TypeId) pairs from AST param names + substituted types
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(instance.func_type.params_id.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();

        let mangled_name = names.display(instance.mangled_name);

        let vir = lower_monomorphized_function(
            func,
            func_id,
            mangled_name,
            &param_types,
            instance.func_type.return_type_id,
            node_map,
            type_arena,
            instance.mangled_name,
        );
        vir_functions.push(vir);
    }
}

/// Build a map from NameId to generic `FuncDecl` for the main program.
///
/// Includes both explicitly generic functions (those with type_params in AST)
/// and implicitly generic functions (those with generic_info in entity
/// registry, e.g. structural type params).
fn build_generic_func_map<'a>(
    program: &'a Program,
    interner: &Interner,
    names: &NameTable,
    module_id: ModuleId,
) -> FxHashMap<NameId, &'a vole_frontend::FuncDecl> {
    let namer = NamerLookup::new(names, interner);
    let mut map = FxHashMap::default();

    for decl in &program.declarations {
        let Decl::Function(func) = decl else { continue };
        // Only include generic functions (explicit type params)
        if func.type_params.is_empty() {
            continue;
        }
        let Some(name_id) = namer.function(module_id, func.name) else {
            continue;
        };
        map.insert(name_id, func);
    }

    map
}

/// Build a lookup map from monomorphized mangled NameId to VirFunction index.
///
/// Only includes VIR functions that have a `mangled_name_id` set (i.e.,
/// monomorphized instances).  Non-generic functions are not indexed here
/// because they are compiled via the normal (non-monomorph) path.
fn build_vir_monomorph_map(vir_functions: &[VirFunction]) -> FxHashMap<NameId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(name_id) = vf.mangled_name_id {
            map.insert(name_id, idx);
        }
    }
    map
}
