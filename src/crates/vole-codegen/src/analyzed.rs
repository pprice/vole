// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use vole_frontend::{Decl, Interner, LetInit, Program, Span, Symbol};
use vole_identity::{FunctionId, MethodId, ModuleId, NameId, NameTable, NamerLookup, TypeDefId};
use vole_sema::{
    AnalysisOutput, CodegenDb, EntityRegistry, ImplementRegistry, NodeMap, ProgramQuery, TypeArena,
};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirBody, VirFunction, VirRef, VirTest};

use crate::vir_lower::{
    lower_function, lower_interface_method, lower_method, lower_monomorphized_function,
    lower_test_body,
};

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
    /// VIR-lowered functions: top-level non-generic functions, their
    /// monomorphized instances, and type methods.
    pub vir_functions: Vec<VirFunction>,
    /// Lookup map from monomorphized mangled NameId to index in `vir_functions`.
    /// Enables O(1) VIR function lookup during monomorphized compilation.
    pub vir_monomorph_map: FxHashMap<NameId, usize>,
    /// Lookup map from semantic FunctionId to index in `vir_functions`.
    /// Enables O(1) VIR function lookup for non-generic top-level and module
    /// functions during compilation.
    pub vir_function_map: FxHashMap<FunctionId, usize>,
    /// Lookup map from semantic MethodId to index in `vir_functions`.
    /// Enables O(1) VIR function lookup for non-generic class/struct methods
    /// and static methods during compilation.
    pub vir_method_map: FxHashMap<MethodId, usize>,
    /// VIR-lowered test cases with names and bodies.
    pub vir_tests: Vec<VirTest>,
    /// VIR-lowered global variable initializer expressions for the main program.
    ///
    /// Keyed by the `let` binding's `Symbol`.  Used by `try_call_global()` to
    /// compile global lambda/functional-interface initializers through the VIR
    /// path instead of falling back to `self.expr()` (AST path).
    pub vir_global_inits: FxHashMap<Symbol, VirRef>,
    /// VIR-lowered global variable initializer expressions for imported modules.
    ///
    /// Keyed by module path, then by the `let` binding's `Symbol`.
    pub module_vir_global_inits: FxHashMap<String, FxHashMap<Symbol, VirRef>>,
    /// VIR type table populated during lowering.
    ///
    /// Maps `TypeId` → `VirTypeId` with interned VIR type descriptors and
    /// layout information.  Shared across all lowered functions and used by
    /// codegen for type queries.
    pub vir_type_table: VirTypeTable,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    ///
    /// When the CompilationDb has a single owner (non-cached path), unwraps it
    /// directly. When shared (cached path, where module cache holds a reference),
    /// creates a CodegenDb that shares all data via Rc (O(1), zero cloning).
    pub fn from_analysis(program: Program, mut interner: Interner, output: AnalysisOutput) -> Self {
        let db = match Rc::try_unwrap(output.db) {
            // Non-cached path: sole owner, move data directly (zero-cost)
            Ok(compilation_db) => compilation_db.into_codegen(),
            // Cached path: share Rc-wrapped fields instead of cloning entire CompilationDb
            Err(rc) => rc.to_codegen_shared(),
        };
        let mut module_programs = output.module_programs;
        let mut type_table = VirTypeTable::new();
        let mut vir_functions = lower_top_level_functions(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            output.module_id,
            &mut type_table,
        );
        lower_module_functions(
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut vir_functions,
            &mut type_table,
        );
        let generic_func_asts =
            build_generic_func_map(&program, &interner, &db.names, output.module_id);
        lower_monomorphized_instances(
            &generic_func_asts,
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut interner,
            &mut vir_functions,
            &mut type_table,
        );
        lower_top_level_type_methods(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            output.module_id,
            Some(&module_programs),
            &mut vir_functions,
            &mut type_table,
        );
        lower_module_type_methods(
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut vir_functions,
            &mut type_table,
        );
        lower_implement_block_methods(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            output.module_id,
            &mut vir_functions,
            &mut type_table,
        );
        lower_module_implement_block_methods(
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut vir_functions,
            &mut type_table,
        );
        lower_test_scoped_type_methods(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.tests_virtual_modules,
            Some(&module_programs),
            output.module_id,
            &mut vir_functions,
            &mut type_table,
        );
        // NOTE: Class method monomorphs (class_method_monomorph_cache) are NOT
        // VIR-lowered here because the NodeMap shares entries across all
        // monomorphized instances of the same method body.  Only the last
        // re-analyzed instance's data survives, producing incorrect VIR for
        // earlier instances (e.g., wrong union tag indices for Maybe<i64> vs
        // Maybe<string>).  Class method monomorphs continue to use the AST
        // path in compile_monomorphized_class_method.  VIR lowering requires
        // per-instance NodeMap snapshots (tracked separately).
        let vir_monomorph_map = build_vir_monomorph_map(&vir_functions);
        let vir_function_map = build_vir_function_map(&vir_functions);
        let vir_method_map = build_vir_method_map(&vir_functions);
        let vir_tests = lower_test_bodies(
            &program,
            &output.node_map,
            &mut interner,
            &db.types,
            &db.entities,
            &db.names,
            &mut type_table,
        );
        let vir_global_inits = lower_global_inits(
            &program,
            &mut interner,
            &output.node_map,
            &db.types,
            &db.entities,
            &db.names,
            &mut type_table,
        );
        let module_vir_global_inits = lower_module_global_inits(
            &mut module_programs,
            &db.names,
            &output.node_map,
            &db.types,
            &db.entities,
            &output.modules_with_errors,
            &mut type_table,
        );
        Self {
            program,
            interner: Rc::new(interner),
            node_map: output.node_map,
            tests_virtual_modules: output.tests_virtual_modules,
            module_programs,
            db,
            module_id: output.module_id,
            modules_with_errors: output.modules_with_errors,
            vir_functions,
            vir_monomorph_map,
            vir_function_map,
            vir_method_map,
            vir_tests,
            vir_global_inits,
            module_vir_global_inits,
            vir_type_table: type_table,
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

    /// Look up a VIR function by its semantic FunctionId.
    /// Returns `None` if no VIR function was lowered for this function.
    pub fn get_vir_function(&self, func_id: FunctionId) -> Option<&VirFunction> {
        self.vir_function_map
            .get(&func_id)
            .map(|&idx| &self.vir_functions[idx])
    }

    /// Look up a VIR function by its semantic MethodId.
    /// Returns `None` if no VIR function was lowered for this method.
    pub fn get_vir_method(&self, method_id: MethodId) -> Option<&VirFunction> {
        self.vir_method_map
            .get(&method_id)
            .map(|&idx| &self.vir_functions[idx])
    }

    /// Look up a VIR test body by the test case's span.
    /// Returns `None` if no VIR body was lowered for this test.
    pub fn get_vir_test(&self, span: Span) -> Option<&VirBody> {
        self.vir_tests
            .iter()
            .find(|t| t.span == span)
            .map(|t| &t.body)
    }
}

/// Lower global variable initializer expressions from the main program to VIR.
///
/// Iterates `Decl::Let` declarations and lowers each initializer expression
/// using `lower_expr`.  The resulting map is keyed by the binding's `Symbol`.
fn lower_global_inits(
    program: &Program,
    interner: &mut Interner,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    names: &NameTable,
    type_table: &mut VirTypeTable,
) -> FxHashMap<Symbol, VirRef> {
    use crate::vir_lower::LoweringCtx;
    use crate::vir_lower::expr::lower_expr;

    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table: names,
        type_table,
    };

    let mut map = FxHashMap::default();
    for decl in &program.declarations {
        if let Decl::Let(let_stmt) = decl
            && let LetInit::Expr(expr) = &let_stmt.init
        {
            // Only lower if sema analyzed the expression (has type info)
            if node_map.get_type(expr.id).is_some() {
                let vir = lower_expr(expr, &mut ctx);
                map.insert(let_stmt.name, vir);
            }
        }
    }
    map
}

/// Lower global variable initializer expressions from imported modules to VIR.
///
/// Iterates each module's `Decl::Let` declarations and lowers their
/// initializer expressions.  Returns a nested map keyed first by module path,
/// then by the binding's `Symbol`.
fn lower_module_global_inits(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<String, FxHashMap<Symbol, VirRef>> {
    use crate::vir_lower::LoweringCtx;
    use crate::vir_lower::expr::lower_expr;

    let mut result = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let interner = Rc::make_mut(module_interner);
        let mut ctx = LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities,
            name_table: names,
            type_table,
        };

        let mut map = FxHashMap::default();
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl
                && let LetInit::Expr(expr) = &let_stmt.init
                && node_map.get_type(expr.id).is_some()
            {
                let vir = lower_expr(expr, &mut ctx);
                map.insert(let_stmt.name, vir);
            }
        }
        if !map.is_empty() {
            result.insert(module_path.clone(), map);
        }
    }
    result
}

/// Lower top-level non-generic functions to VIR.
///
/// Iterates the program's declarations, looks up each non-generic function
/// in the entity registry, and calls `lower_function()` to produce a
/// `VirFunction`.  Generic functions and implicit generics are skipped
/// because they are monomorphized during codegen.
#[allow(clippy::too_many_arguments)]
fn lower_top_level_functions(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    type_table: &mut VirTypeTable,
) -> Vec<VirFunction> {
    // Collect (func_decl, func_id, func_def) tuples first while interner is
    // borrowed immutably by NamerLookup, then lower with &mut interner.
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        program
            .declarations
            .iter()
            .filter_map(|decl| {
                let Decl::Function(func) = decl else {
                    return None;
                };
                if !func.type_params.is_empty() {
                    return None;
                }
                let name_id = namer.function(module_id, func.name)?;
                let func_id = entities.function_by_name(name_id)?;
                let func_def = entities.get_function(func_id);
                if func_def.generic_info.is_some() {
                    return None;
                }
                Some((func, func_id, func_def))
            })
            .collect()
    };

    let mut vir_functions = Vec::new();
    for (func, func_id, func_def) in resolved {
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
            interner,
            type_arena,
            entities,
            names,
            type_table,
        );
        vir_functions.push(vir);
    }

    vir_functions
}

/// Lower monomorphized function instances to VIR.
///
/// For each concrete instance in the monomorph cache, finds the generic
/// function's AST in the main program (`generic_func_asts`) or in module
/// programs and lowers it with the substituted (concrete) param and return
/// types from the instance's `func_type`.
///
/// Debug-asserts that no `TypeId` in the output contains a type parameter.
#[allow(clippy::too_many_arguments)]
fn lower_monomorphized_instances(
    generic_func_asts: &FxHashMap<NameId, &vole_frontend::FuncDecl>,
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    interner: &mut Interner,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Iterate all monomorphized instances in the cache
    for (_, instance) in entities.monomorph_cache.instances() {
        if let Some(func) = generic_func_asts.get(&instance.original_name) {
            // Found in the main program — lower with the main interner
            lower_single_monomorph(
                func,
                instance,
                names,
                entities,
                type_arena,
                node_map,
                interner,
                vir_functions,
                type_table,
            );
            continue;
        }

        // Not in the main program — search module programs
        lower_module_monomorph(
            instance,
            module_programs,
            names,
            entities,
            type_arena,
            node_map,
            modules_with_errors,
            vir_functions,
            type_table,
        );
    }
}

/// Lower a single monomorphized instance whose AST is in the main program.
#[allow(clippy::too_many_arguments)]
fn lower_single_monomorph(
    func: &vole_frontend::FuncDecl,
    instance: &vole_sema::generic::MonomorphInstance,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    interner: &mut Interner,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let Some(func_id) = entities.function_by_name(instance.original_name) else {
        return;
    };
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
        interner,
        entities,
        names,
        type_table,
    );
    vir_functions.push(vir);
}

/// Lower a single monomorphized instance whose AST originates from a module.
///
/// Resolves the module from `instance.original_name`, finds the generic
/// function AST in that module's program, and lowers it with the module's
/// interner.  Skips lowering if sema never analyzed the function body (i.e.,
/// the NodeMap has no entries for body nodes) — codegen falls back to the
/// AST path for those instances.
#[allow(clippy::too_many_arguments)]
fn lower_module_monomorph(
    instance: &vole_sema::generic::MonomorphInstance,
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let Some(func_id) = entities.function_by_name(instance.original_name) else {
        return;
    };
    let module_id = names.module_of(instance.original_name);
    let module_path = names.module_path(module_id).to_string();
    if modules_with_errors.contains(&module_path) {
        return;
    }
    let Some((module_program, module_interner)) = module_programs.get_mut(&module_path) else {
        return;
    };
    let interner = Rc::make_mut(module_interner);

    // Find the generic function in the module by checking all function decls
    let func = module_program.declarations.iter().find_map(|decl| {
        let Decl::Function(func) = decl else {
            return None;
        };
        if func.type_params.is_empty() {
            return None;
        }
        let namer = NamerLookup::new(names, interner);
        let name_id = namer.function(module_id, func.name)?;
        if name_id == instance.original_name {
            Some(func)
        } else {
            None
        }
    });

    let Some(func) = func else { return };

    // Check if sema analyzed this function's body.  Generic function bodies
    // are skipped during initial module analysis and only analyzed later
    // during `analyze_monomorph_bodies`.  If the body was never analyzed,
    // the NodeMap won't have entries and VIR lowering would panic.
    if !body_has_sema_data(&func.body, node_map) {
        return;
    }

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
        interner,
        entities,
        names,
        type_table,
    );
    vir_functions.push(vir);
}

/// Check whether sema has analyzed a function body by probing for NodeMap
/// entries.  Returns `true` if body node data exists, `false` otherwise.
///
/// Generic function bodies are skipped during initial sema analysis.  The
/// monomorph body analysis pass (`analyze_monomorph_bodies`) re-analyzes them
/// with concrete substitutions — for both main-program and module-originating
/// generics.  This check is a safety guard: if sema analysis failed to
/// populate the NodeMap for a body (e.g., due to errors), VIR lowering would
/// panic, so we skip and let codegen fall back to the AST path.
fn body_has_sema_data(body: &vole_frontend::ast::FuncBody, node_map: &NodeMap) -> bool {
    use vole_frontend::ast::FuncBody;
    match body {
        FuncBody::Expr(expr) => node_map.get_type(expr.id).is_some(),
        FuncBody::Block(block) => {
            // Check the first expression NodeId reachable from the first statement
            for stmt in &block.stmts {
                if let Some(node_id) = first_expr_node_id(stmt) {
                    return node_map.get_type(node_id).is_some();
                }
            }
            // Empty body — trivially analyzed
            true
        }
    }
}

/// Extract the first expression NodeId from a statement, if any.
fn first_expr_node_id(stmt: &vole_frontend::ast::Stmt) -> Option<vole_identity::NodeId> {
    use vole_frontend::ast::Stmt;
    match stmt {
        Stmt::Expr(s) => Some(s.expr.id),
        Stmt::Let(s) => s.init.as_expr().map(|e| e.id),
        Stmt::LetTuple(s) => Some(s.init.id),
        Stmt::If(s) => Some(s.condition.id),
        Stmt::While(s) => Some(s.condition.id),
        Stmt::For(s) => Some(s.iterable.id),
        Stmt::Return(s) => s.value.as_ref().map(|e| e.id),
        Stmt::Raise(_) => None,
        Stmt::Break(_) | Stmt::Continue(_) => None,
    }
}

/// Build a map from NameId to generic `FuncDecl` for the main program.
///
/// Includes both explicitly generic functions (those with type_params in AST)
/// and implicitly generic functions (those with generic_info in entity
/// registry, e.g. structural type params).  Recurses into `Decl::Tests`
/// blocks so that test-scoped generic functions are also available for
/// monomorphized VIR lowering.
fn build_generic_func_map<'a>(
    program: &'a Program,
    interner: &Interner,
    names: &NameTable,
    module_id: ModuleId,
) -> FxHashMap<NameId, &'a vole_frontend::FuncDecl> {
    let namer = NamerLookup::new(names, interner);
    let mut map = FxHashMap::default();

    collect_generic_funcs(&program.declarations, &namer, module_id, &mut map);

    map
}

/// Recursively collect generic function ASTs from a slice of declarations.
///
/// Test-scoped functions are registered under the program's module_id (not the
/// virtual test module), so we use the same `module_id` for name resolution
/// regardless of nesting depth.
fn collect_generic_funcs<'a>(
    decls: &'a [Decl],
    namer: &NamerLookup<'_>,
    module_id: ModuleId,
    map: &mut FxHashMap<NameId, &'a vole_frontend::FuncDecl>,
) {
    for decl in decls {
        match decl {
            Decl::Function(func) => {
                if func.type_params.is_empty() {
                    continue;
                }
                let Some(name_id) = namer.function(module_id, func.name) else {
                    continue;
                };
                map.insert(name_id, func);
            }
            Decl::Tests(tests_decl) => {
                collect_generic_funcs(&tests_decl.decls, namer, module_id, map);
            }
            _ => {}
        }
    }
}

/// Lower non-generic functions from imported modules to VIR.
///
/// Iterates each module's parsed program, resolves function identities through
/// the module's interner and module ID, and calls `lower_function()` for each
/// non-generic, non-implicitly-generic function.  Modules with sema errors are
/// skipped to avoid INVALID type IDs.
#[allow(clippy::too_many_arguments)]
fn lower_module_functions(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);
        lower_module_program_functions(
            program,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            vir_functions,
            type_table,
        );
    }
}

/// Lower non-generic functions from a single module program to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_module_program_functions(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        program
            .declarations
            .iter()
            .filter_map(|decl| {
                let Decl::Function(func) = decl else {
                    return None;
                };
                if !func.type_params.is_empty() {
                    return None;
                }
                let name_id = namer.function(module_id, func.name)?;
                let func_id = entities.function_by_name(name_id)?;
                let func_def = entities.get_function(func_id);
                if func_def.generic_info.is_some() {
                    return None;
                }
                Some((func, func_id, func_def))
            })
            .collect()
    };

    for (func, func_id, func_def) in resolved {
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
            interner,
            type_arena,
            entities,
            names,
            type_table,
        );
        vir_functions.push(vir);
    }
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

/// Build a lookup map from semantic FunctionId to VirFunction index.
///
/// Only includes non-monomorphized functions (those without a `mangled_name_id`).
/// Monomorphized instances are looked up via `vir_monomorph_map` instead.
fn build_vir_function_map(vir_functions: &[VirFunction]) -> FxHashMap<FunctionId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if vf.mangled_name_id.is_none() && vf.method_id.is_none() {
            map.insert(vf.id, idx);
        }
    }
    map
}

/// Build a lookup map from semantic MethodId to VirFunction index.
///
/// Only includes VIR functions that have a `method_id` set (class/struct
/// methods and static methods).
fn build_vir_method_map(vir_functions: &[VirFunction]) -> FxHashMap<MethodId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(method_id) = vf.method_id {
            map.insert(method_id, idx);
        }
    }
    map
}

/// Lower non-generic class/struct instance methods and static methods to VIR.
///
/// Iterates the program's class and struct declarations, looks up each type's
/// methods in the entity registry, and lowers non-generic methods to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_top_level_type_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        match decl {
            Decl::Class(class) => {
                if !class.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &class.methods,
                    class.statics.as_ref(),
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    vir_functions,
                    type_table,
                );
                // Also lower default methods from implemented interfaces
                let direct_method_names: HashSet<String> = class
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Struct(s) => {
                if !s.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &s.methods,
                    s.statics.as_ref(),
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    vir_functions,
                    type_table,
                );
                // Also lower default methods from implemented interfaces
                let direct_method_names: HashSet<String> = s
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            _ => {}
        }
    }
}

/// Lower instance methods and static methods for a single type declaration.
#[allow(clippy::too_many_arguments)]
fn lower_type_methods(
    methods: &[vole_frontend::FuncDecl],
    statics: Option<&vole_frontend::ast::StaticsBlock>,
    type_name: Symbol,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Resolve all name lookups first while interner is borrowed immutably
    let (type_def_id, resolved_methods, resolved_statics) = {
        let namer = NamerLookup::new(names, interner);
        let Some(type_name_id) = names.name_id(module_id, &[type_name], interner) else {
            return;
        };
        let Some(type_def_id) = entities.type_by_name(type_name_id) else {
            return;
        };

        let resolved_methods: Vec<_> = methods
            .iter()
            .filter_map(|method| {
                if !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect();

        let resolved_statics: Vec<_> = statics
            .map(|s| {
                s.methods
                    .iter()
                    .filter_map(|method| {
                        if method.body.is_none() || !method.type_params.is_empty() {
                            return None;
                        }
                        let method_name_id = namer.method(method.name)?;
                        let mid =
                            entities.find_static_method_on_type(type_def_id, method_name_id)?;
                        let method_def = entities.get_method(mid);
                        if !method_def.method_type_params.is_empty() {
                            return None;
                        }
                        Some((method, mid, method_def))
                    })
                    .collect()
            })
            .unwrap_or_default();

        (type_def_id, resolved_methods, resolved_statics)
    };

    // Now lower with &mut interner (namer is dropped, no immutable borrow)
    let _ = type_def_id;
    let type_name_str = interner.resolve(type_name).to_string();

    for (method, mid, method_def) in resolved_methods {
        lower_single_method(
            method,
            mid,
            method_def,
            &type_name_str,
            interner,
            names,
            node_map,
            type_arena,
            entities,
            vir_functions,
            type_table,
        );
    }

    for (method, mid, method_def) in resolved_statics {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();
        if let Some(vir) = lower_interface_method(
            method,
            mid,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities,
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower default methods from implemented interfaces for a class or struct.
///
/// Finds interface default methods inherited by `type_name` and lowers them to VIR.
/// Direct methods (explicitly defined on the type) are skipped since they override
/// the default. This covers default methods from the type's own `implements` clause,
/// as opposed to `lower_implement_default_methods` which covers `extend T with I` blocks.
#[allow(clippy::too_many_arguments)]
fn lower_type_default_methods(
    direct_method_names: &HashSet<String>,
    type_name: Symbol,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    program: &Program,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Resolve type_def_id
    let Some(type_name_id) = names.name_id(module_id, &[type_name], interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };

    let type_name_str = interner.resolve(type_name).to_string();

    // Find default methods from implemented interfaces
    let default_methods =
        collect_default_method_ids(type_def_id, entities, names, direct_method_names);

    for (impl_method_id, method_name_str, interface_tdef_id) in default_methods {
        let iface_name_str = names
            .last_segment_str(entities.get_type(interface_tdef_id).name_id)
            .unwrap_or_default();
        let iface_method = find_interface_method_ast(
            &iface_name_str,
            &method_name_str,
            program,
            interner,
            module_programs,
        );
        let Some(iface_method) = iface_method else {
            continue;
        };

        let method_def = entities.get_method(impl_method_id);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = iface_method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        if let Some(vir) = lower_interface_method(
            iface_method,
            impl_method_id,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities,
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower a single instance method to VIR and push it onto the functions vec.
#[allow(clippy::too_many_arguments)]
fn lower_single_method(
    method: &vole_frontend::FuncDecl,
    method_id: MethodId,
    method_def: &vole_sema::MethodDef,
    type_name_str: &str,
    interner: &mut Interner,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let arena_sig = method_def.signature_id;
    // We need the type arena to unwrap the signature, but we don't have it here.
    // Instead, use the AST param names + entity registry param types.
    // MethodDef doesn't store params_id directly, so we extract from signature.
    // Since we can't unwrap_function without the TypeArena, pass param names
    // paired with placeholder types (UNKNOWN).  VIR lowering embeds types from
    // sema's NodeMap, so the placeholder types are not used for codegen.
    let method_name_str = interner.resolve(method.name);
    let display_name = format!("{}::{}", type_name_str, method_name_str);

    // Create placeholder entries matching the AST params.
    let param_types: Vec<_> = method
        .params
        .iter()
        .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
        .collect();

    let vir = lower_method(
        method,
        method_id,
        display_name,
        &param_types,
        arena_sig, // return_type from entity registry
        node_map,
        interner,
        type_arena,
        entities,
        names,
        type_table,
    );
    vir_functions.push(vir);
}

/// Lower non-generic type methods from imported modules to VIR.
///
/// Two passes: first lowers direct instance + static methods, then lowers
/// default methods from implemented interfaces.  The second pass needs
/// immutable access to `module_programs` for cross-module interface AST
/// lookup, so we collect per-type work items during the first (mutable) pass
/// and process them in a second (immutable) pass.
#[allow(clippy::too_many_arguments)]
fn lower_module_type_methods(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // --- Pass 1: lower direct + static methods (needs &mut interner) ---
    // Also collect (module_path, type_name, direct_method_names) for pass 2.
    struct DefaultMethodWork {
        module_path: String,
        type_name: Symbol,
        direct_method_names: HashSet<String>,
    }
    let mut default_method_work: Vec<DefaultMethodWork> = Vec::new();

    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    if !class.type_params.is_empty() {
                        continue;
                    }
                    lower_type_methods(
                        &class.methods,
                        class.statics.as_ref(),
                        class.name,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        module_id,
                        vir_functions,
                        type_table,
                    );
                    let direct_method_names: HashSet<String> = class
                        .methods
                        .iter()
                        .map(|m| interner.resolve(m.name).to_string())
                        .collect();
                    default_method_work.push(DefaultMethodWork {
                        module_path: module_path.clone(),
                        type_name: class.name,
                        direct_method_names,
                    });
                }
                Decl::Struct(s) => {
                    if !s.type_params.is_empty() {
                        continue;
                    }
                    lower_type_methods(
                        &s.methods,
                        s.statics.as_ref(),
                        s.name,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        module_id,
                        vir_functions,
                        type_table,
                    );
                    let direct_method_names: HashSet<String> = s
                        .methods
                        .iter()
                        .map(|m| interner.resolve(m.name).to_string())
                        .collect();
                    default_method_work.push(DefaultMethodWork {
                        module_path: module_path.clone(),
                        type_name: s.name,
                        direct_method_names,
                    });
                }
                _ => {}
            }
        }
    }

    // --- Pass 2: lower default methods from interfaces (needs shared module_programs) ---
    for work in default_method_work {
        let Some((program, module_interner)) = module_programs.get_mut(&work.module_path) else {
            continue;
        };
        let module_id = names
            .module_id_if_known(&work.module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        // For module types, pass only the module's own program for interface lookup.
        // Cross-module interface lookup is not available here (borrow limitation),
        // but module types typically implement interfaces defined in the same module
        // or in the stdlib (which is also in module_programs).  The implement-block
        // lowering handles cross-module cases separately.
        lower_type_default_methods(
            &work.direct_method_names,
            work.type_name,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            None, // cross-module lookup not available in this pass
            vir_functions,
            type_table,
        );
    }
}

/// Lower type methods for classes/structs declared inside test blocks.
///
/// Test blocks can contain `Decl::Class` and `Decl::Struct` declarations that
/// are scoped to a virtual module.  This function recursively walks `Decl::Tests`
/// blocks and lowers their class/struct methods (direct + default) to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_test_scoped_type_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_type_methods(
                tests_decl,
                program,
                interner,
                names,
                entities,
                type_arena,
                node_map,
                tests_virtual_modules,
                module_programs,
                module_id,
                vir_functions,
                type_table,
            );
        }
    }
}

/// Recursively lower type methods from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_type_methods(
    tests_decl: &vole_frontend::ast::TestsDecl,
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let virtual_module_id = tests_virtual_modules
        .get(&tests_decl.span)
        .copied()
        .unwrap_or_else(|| names.main_module());

    // Test-scoped functions are registered under the program's module_id (not the virtual
    // test module), so use the passed module_id for function name resolution. This must
    // match what codegen uses in compile_function (program_module = analyzed.module_id).
    let main_module_id = module_id;

    for inner_decl in &tests_decl.decls {
        match inner_decl {
            Decl::Function(func) => {
                if !func.type_params.is_empty() {
                    continue;
                }
                // Resolve the function in the main module (test-scoped functions use
                // program_module for name resolution, same as top-level functions)
                let func_id_and_def = {
                    let namer = NamerLookup::new(names, interner);
                    let name_id = namer.function(main_module_id, func.name);
                    name_id.and_then(|nid| {
                        let fid = entities.function_by_name(nid)?;
                        let fdef = entities.get_function(fid);
                        if fdef.generic_info.is_some() {
                            return None;
                        }
                        Some((fid, fdef))
                    })
                };
                if let Some((func_id, func_def)) = func_id_and_def {
                    let param_types: Vec<_> = func
                        .params
                        .iter()
                        .zip(func_def.signature.params_id.iter())
                        .map(|(p, &ty)| (p.name, ty))
                        .collect();
                    let vir = lower_function(
                        func,
                        func_id,
                        interner.resolve(func.name).to_string(),
                        &param_types,
                        func_def.signature.return_type_id,
                        node_map,
                        interner,
                        type_arena,
                        entities,
                        names,
                        type_table,
                    );
                    vir_functions.push(vir);
                }
            }
            Decl::Class(class) => {
                if !class.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &class.methods,
                    class.statics.as_ref(),
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    vir_functions,
                    type_table,
                );
                let direct_method_names: HashSet<String> = class
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Struct(s) => {
                if !s.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &s.methods,
                    s.statics.as_ref(),
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    vir_functions,
                    type_table,
                );
                let direct_method_names: HashSet<String> = s
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Implement(impl_block) => {
                let type_def_id = resolve_implement_target(
                    &impl_block.target_type,
                    interner,
                    names,
                    entities,
                    virtual_module_id,
                );
                if let Some(type_def_id) = type_def_id {
                    lower_implement_direct_methods(
                        &impl_block.methods,
                        type_def_id,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        vir_functions,
                        type_table,
                    );
                    if let Some(ref statics) = impl_block.statics {
                        lower_implement_static_methods(
                            statics,
                            type_def_id,
                            interner,
                            names,
                            entities,
                            type_arena,
                            node_map,
                            vir_functions,
                            type_table,
                        );
                    }
                    lower_implement_default_methods(
                        impl_block,
                        type_def_id,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        virtual_module_id,
                        program,
                        module_programs,
                        vir_functions,
                        type_table,
                    );
                }
            }
            Decl::Tests(nested) => {
                lower_tests_decl_type_methods(
                    nested,
                    program,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    tests_virtual_modules,
                    module_programs,
                    module_id,
                    vir_functions,
                    type_table,
                );
            }
            _ => {}
        }
    }
}

/// Lower all test function bodies in the program to VIR.
///
/// Walks the program's `Decl::Tests` blocks (including nested ones) and
/// lowers each `TestCase.body` to a `VirBody`.  Returns a map keyed by
/// the `TestCase`'s `Span` for O(1) lookup during test compilation.
fn lower_test_bodies(
    program: &Program,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    names: &NameTable,
    type_table: &mut VirTypeTable,
) -> Vec<VirTest> {
    let mut tests = Vec::new();
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_bodies(
                tests_decl, node_map, interner, type_arena, entities, names, &mut tests, type_table,
            );
        }
    }
    tests
}

/// Recursively lower test bodies from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_bodies(
    tests_decl: &vole_frontend::ast::TestsDecl,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    names: &NameTable,
    tests: &mut Vec<VirTest>,
    type_table: &mut VirTypeTable,
) {
    for test in &tests_decl.tests {
        let vir_body = lower_test_body(
            &test.body, node_map, interner, type_arena, entities, names, type_table,
        );
        tests.push(VirTest {
            name: test.name.clone(),
            body: vir_body,
            span: test.span,
        });
    }
    // Recurse into nested tests blocks
    for decl in &tests_decl.decls {
        if let Decl::Tests(nested) = decl {
            lower_tests_decl_bodies(
                nested, node_map, interner, type_arena, entities, names, tests, type_table,
            );
        }
    }
}

/// Lower implement block methods (direct + statics) to VIR.
///
/// Iterates `Decl::Implement` blocks in the main program, resolves each
/// method's `MethodId` from the entity registry, and lowers the body.
/// Default interface methods (not in the implement block AST) are handled
/// by [`lower_implement_default_methods`].
#[allow(clippy::too_many_arguments)]
fn lower_implement_block_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        let Decl::Implement(impl_block) = decl else {
            continue;
        };
        lower_single_implement_block(
            impl_block,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            vir_functions,
            type_table,
        );
    }
}

/// Lower a single implement block's direct methods and statics to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_single_implement_block(
    impl_block: &vole_frontend::ast::ImplementBlock,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    program: &Program,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let Some(type_def_id) = resolve_implement_target(
        &impl_block.target_type,
        interner,
        names,
        entities,
        module_id,
    ) else {
        return;
    };

    // Lower direct instance methods
    lower_implement_direct_methods(
        &impl_block.methods,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        vir_functions,
        type_table,
    );

    // Lower static methods
    if let Some(ref statics) = impl_block.statics {
        lower_implement_static_methods(
            statics,
            type_def_id,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            vir_functions,
            type_table,
        );
    }

    // Lower interface default methods (inherited, not overridden)
    lower_implement_default_methods(
        impl_block,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        program,
        None,
        vir_functions,
        type_table,
    );
}

/// Resolve the target type of an implement block to a `TypeDefId`.
///
/// Handles `Named`, `Generic`, `Primitive`, `Handle`, and `Array` target types.
fn resolve_implement_target(
    target_type: &vole_frontend::TypeExpr,
    interner: &Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    module_id: ModuleId,
) -> Option<TypeDefId> {
    use vole_frontend::TypeExprKind;
    match &target_type.kind {
        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
            // Try normal module-scoped lookup first (class/struct types)
            if let Some(name_id) = names.name_id(module_id, &[*sym], interner)
                && let Some(tdef) = entities.type_by_name(name_id)
            {
                return Some(tdef);
            }
            // Fall back to short-name lookup for named primitives (e.g. "range")
            let sym_str = interner.resolve(*sym);
            entities.type_by_short_name(sym_str, names)
        }
        TypeExprKind::Primitive(p) => {
            let prim_type = vole_sema::PrimitiveType::from_ast(*p);
            let prim_name = prim_type.name();
            entities.type_by_short_name(prim_name, names)
        }
        TypeExprKind::Handle => entities.type_by_short_name("handle", names),
        TypeExprKind::Array(_) => entities
            .array_name_id()
            .and_then(|n| entities.type_by_name(n)),
        _ => None,
    }
}

/// Lower direct instance methods from an implement block to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_implement_direct_methods(
    methods: &[vole_frontend::FuncDecl],
    type_def_id: TypeDefId,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    // Resolve all methods first while interner is borrowed immutably
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        methods
            .iter()
            .filter_map(|method| {
                if !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect()
    };

    for (method, mid, method_def) in resolved {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        let vir = lower_method(
            method,
            mid,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities,
            names,
            type_table,
        );
        vir_functions.push(vir);
    }
}

/// Lower static methods from an implement block's statics section to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_implement_static_methods(
    statics: &vole_frontend::ast::StaticsBlock,
    type_def_id: TypeDefId,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        statics
            .methods
            .iter()
            .filter_map(|method| {
                if method.body.is_none() || !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_static_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect()
    };

    for (method, mid, method_def) in resolved {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();
        if let Some(vir) = lower_interface_method(
            method,
            mid,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities,
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower interface default methods for an implement block.
///
/// Finds default methods from implemented interfaces that are NOT overridden
/// by the implement block's direct methods. For each such default method,
/// locates the interface's AST body and lowers it with the implementing
/// type's MethodId.
#[allow(clippy::too_many_arguments)]
fn lower_implement_default_methods(
    impl_block: &vole_frontend::ast::ImplementBlock,
    type_def_id: TypeDefId,
    interner: &mut Interner,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    _module_id: ModuleId,
    program: &Program,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    // Collect direct method names to skip
    let direct_method_names: HashSet<String> = impl_block
        .methods
        .iter()
        .map(|m| interner.resolve(m.name).to_string())
        .collect();

    // Find default methods from implemented interfaces
    let default_methods =
        collect_default_method_ids(type_def_id, entities, names, &direct_method_names);

    for (impl_method_id, method_name_str, interface_tdef_id) in default_methods {
        // Find the interface AST method body
        let iface_name_str = names
            .last_segment_str(entities.get_type(interface_tdef_id).name_id)
            .unwrap_or_default();
        let iface_method = find_interface_method_ast(
            &iface_name_str,
            &method_name_str,
            program,
            interner,
            module_programs,
        );
        let Some(iface_method) = iface_method else {
            continue;
        };

        let method_def = entities.get_method(impl_method_id);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = iface_method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        // Use lower_interface_method since the AST is an InterfaceMethod
        if let Some(vir) = lower_interface_method(
            iface_method,
            impl_method_id,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities,
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Collect interface default method IDs for a type, skipping overridden ones.
///
/// Returns `(impl_method_id, method_name_str, interface_tdef_id)` tuples.
fn collect_default_method_ids(
    type_def_id: TypeDefId,
    entities: &EntityRegistry,
    names: &NameTable,
    direct_method_names: &HashSet<String>,
) -> Vec<(MethodId, String, TypeDefId)> {
    let mut results = Vec::new();
    for interface_tdef_id in entities.get_implemented_interfaces(type_def_id) {
        // Note: we intentionally do NOT skip interfaces with abstract type params
        // (e.g. Iterable<T> on [T]). The VIR body is the same regardless of T —
        // substitutions are applied at compile time by passing `concrete_subs`.
        // Skipping abstract params would leave array Iterable default methods
        // without VIR bodies.

        for iface_method_id in entities.methods_on_type(interface_tdef_id) {
            let method_def = entities.get_method(iface_method_id);
            if !method_def.has_default || method_def.external_binding.is_some() {
                continue;
            }
            let method_name_str = names
                .last_segment_str(method_def.name_id)
                .unwrap_or_default();
            if direct_method_names.contains(&method_name_str) {
                continue;
            }
            if let Some(impl_method_id) =
                entities.find_method_on_type(type_def_id, method_def.name_id)
            {
                results.push((impl_method_id, method_name_str, interface_tdef_id));
            }
        }
    }
    results
}

/// Find an interface method's AST node by interface and method name.
///
/// Searches the main program and optionally module programs for the
/// interface declaration, then finds the default method with a body.
fn find_interface_method_ast<'a>(
    interface_name: &str,
    method_name: &str,
    program: &'a Program,
    interner: &Interner,
    module_programs: Option<&'a FxHashMap<String, (Program, Rc<Interner>)>>,
) -> Option<&'a vole_frontend::ast::InterfaceMethod> {
    // Search main program using the main interner
    for decl in &program.declarations {
        if let Decl::Interface(iface) = decl {
            if interner.resolve(iface.name) != interface_name {
                continue;
            }
            for method in &iface.methods {
                if interner.resolve(method.name) == method_name && method.body.is_some() {
                    return Some(method);
                }
            }
        }
    }

    // Search module programs using their interners
    if let Some(module_programs) = module_programs {
        for (program, module_interner) in module_programs.values() {
            for decl in &program.declarations {
                if let Decl::Interface(iface) = decl {
                    if module_interner.resolve(iface.name) != interface_name {
                        continue;
                    }
                    for method in &iface.methods {
                        if module_interner.resolve(method.name) == method_name
                            && method.body.is_some()
                        {
                            return Some(method);
                        }
                    }
                }
            }
        }
    }

    None
}

/// Lower implement block methods from imported modules to VIR.
///
/// Two passes: first lowers direct instance + static methods, then lowers
/// default methods from implemented interfaces.  The second pass needs
/// immutable access to `module_programs` for cross-module interface AST
/// lookup, so we collect per-block work items during the first pass.
#[allow(clippy::too_many_arguments)]
fn lower_module_implement_block_methods(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &EntityRegistry,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // --- Pass 1: lower direct + static methods, collect default method work items ---
    struct ImplDefaultWork {
        module_path: String,
        /// Index of the Decl::Implement within the module's declarations.
        impl_decl_index: usize,
        type_def_id: TypeDefId,
    }
    let mut default_work: Vec<ImplDefaultWork> = Vec::new();

    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        for (decl_idx, decl) in program.declarations.iter().enumerate() {
            let Decl::Implement(impl_block) = decl else {
                continue;
            };
            let Some(type_def_id) = resolve_implement_target(
                &impl_block.target_type,
                interner,
                names,
                entities,
                module_id,
            ) else {
                continue;
            };

            lower_implement_direct_methods(
                &impl_block.methods,
                type_def_id,
                interner,
                names,
                entities,
                type_arena,
                node_map,
                vir_functions,
                type_table,
            );

            if let Some(ref statics) = impl_block.statics {
                lower_implement_static_methods(
                    statics,
                    type_def_id,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    vir_functions,
                    type_table,
                );
            }

            default_work.push(ImplDefaultWork {
                module_path: module_path.clone(),
                impl_decl_index: decl_idx,
                type_def_id,
            });
        }
    }

    // --- Pass 2: lower default methods from interfaces ---
    // We need both &mut Interner (for the current module) and &module_programs
    // (for cross-module interface AST lookup). Clone the Rc<Interner> so we can
    // borrow module_programs immutably while mutating our own copy.
    for work in default_work {
        let module_id = names
            .module_id_if_known(&work.module_path)
            .unwrap_or_else(|| names.main_module());

        // Clone the Rc<Interner> so we can mutate it independently
        let Some((program, module_interner_rc)) = module_programs.get(&work.module_path) else {
            continue;
        };
        let mut interner_clone = (**module_interner_rc).clone();

        // Re-extract the implement block from the known index
        let Decl::Implement(impl_block) = &program.declarations[work.impl_decl_index] else {
            continue;
        };

        lower_implement_default_methods(
            impl_block,
            work.type_def_id,
            &mut interner_clone,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            Some(module_programs),
            vir_functions,
            type_table,
        );
    }
}
