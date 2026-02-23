// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use vole_frontend::{Decl, Interner, Program, Span};
use vole_identity::{ModuleId, NameTable, NamerLookup};
use vole_sema::{
    AnalysisOutput, CodegenDb, EntityRegistry, ImplementRegistry, NodeMap, ProgramQuery, TypeArena,
};
use vole_vir::{VirFunction, lower_function};

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
    /// VIR-lowered functions (Phase 0: top-level non-generic functions only).
    /// Codegen does not use these yet — they are carried for future phases.
    pub vir_functions: Vec<VirFunction>,
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
        let vir_functions = lower_top_level_functions(
            &program,
            &interner,
            &db.names,
            &db.entities,
            &output.node_map,
            output.module_id,
        );
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
