use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::generic::MonomorphInstance;
use crate::vir_lower::lower_monomorphized_function;
use crate::{NodeMap, TypeArena};
use vole_frontend::ast::{FuncBody, Stmt};
use vole_frontend::{Decl, FuncDecl, Interner, Program};
use vole_identity::{FunctionId, ModuleId, NameId, NameTable, NamerLookup, NodeId, Span};
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

pub struct LowerMonomorphizedInstancesArgs<'a, 'decl> {
    pub generic_func_asts: &'a FxHashMap<NameId, &'decl FuncDecl>,
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub modules_with_errors: &'a HashSet<String>,
    pub interner: &'a mut Interner,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
    pub vir_handled_function_ids: &'a HashSet<FunctionId>,
}

struct LowerSingleMonomorphArgs<'a> {
    func: &'a FuncDecl,
    instance: &'a MonomorphInstance,
    names: &'a NameTable,
    entities: &'a dyn LoweringEntityLookup,
    type_arena: &'a TypeArena,
    node_map: &'a NodeMap,
    interner: &'a mut Interner,
    vir_functions: &'a mut Vec<VirFunction>,
    type_table: &'a mut VirTypeTable,
}

struct LowerModuleMonomorphArgs<'a> {
    instance: &'a MonomorphInstance,
    module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &'a NameTable,
    entities: &'a dyn LoweringEntityLookup,
    type_arena: &'a TypeArena,
    node_map: &'a NodeMap,
    modules_with_errors: &'a HashSet<String>,
    vir_functions: &'a mut Vec<VirFunction>,
    type_table: &'a mut VirTypeTable,
}

/// AST-based fallback for monomorphized instances not handled by VIR monomorph.
///
/// For each concrete instance in the monomorph cache, finds the generic
/// function's AST in the main program (`generic_func_asts`) or in module
/// programs and lowers it with the substituted (concrete) param and return
/// types from the instance's `func_type`.
///
/// Instances whose `original_name` resolves to a `FunctionId` in
/// `vir_handled_function_ids` are skipped -- those were already produced
/// by the VIR monomorphization pass. The remaining instances (e.g.,
/// module-originating generics without VIR templates) are lowered here.
///
/// Debug-asserts that no `TypeId` in the output contains a type parameter.
pub fn lower_monomorphized_instances(args: LowerMonomorphizedInstancesArgs<'_, '_>) {
    let LowerMonomorphizedInstancesArgs {
        generic_func_asts,
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        interner,
        vir_functions,
        type_table,
        vir_handled_function_ids,
    } = args;

    // Iterate all monomorphized instances in the cache
    for instance in entities.monomorph_instances() {
        // Skip instances already handled by VIR monomorphization.
        // VIR monomorph produced concrete functions for these via type
        // substitution on generic templates.
        if let Some(func_id) = entities.function_by_name(instance.original_name)
            && vir_handled_function_ids.contains(&func_id)
        {
            continue;
        }

        if let Some(func) = generic_func_asts.get(&instance.original_name) {
            // Found in the main program — lower with the main interner
            lower_single_monomorph(LowerSingleMonomorphArgs {
                func,
                instance: &instance,
                names,
                entities,
                type_arena,
                node_map,
                interner,
                vir_functions,
                type_table,
            });
            continue;
        }

        // Not in the main program — search module programs
        lower_module_monomorph(LowerModuleMonomorphArgs {
            instance: &instance,
            module_programs,
            names,
            entities,
            type_arena,
            node_map,
            modules_with_errors,
            vir_functions,
            type_table,
        });
    }
}

/// Lower a single monomorphized instance whose AST is in the main program.
fn lower_single_monomorph(args: LowerSingleMonomorphArgs<'_>) {
    let LowerSingleMonomorphArgs {
        func,
        instance,
        names,
        entities,
        type_arena,
        node_map,
        interner,
        vir_functions,
        type_table,
    } = args;

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
    let module_id = names.module_of(instance.original_name);
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
        entities.as_entity_registry(),
        names,
        type_table,
        module_id,
    );
    vir_functions.push(vir);
}

/// Lower a single monomorphized instance whose AST originates from a module.
///
/// Resolves the module from `instance.original_name`, finds the generic
/// function AST in that module's program, and lowers it with the module's
/// interner. Skips lowering if sema never analyzed the function body (i.e.,
/// the NodeMap has no entries for body nodes) — codegen falls back to the
/// AST path for those instances.
fn lower_module_monomorph(args: LowerModuleMonomorphArgs<'_>) {
    let LowerModuleMonomorphArgs {
        instance,
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions,
        type_table,
    } = args;

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

    // Check if sema analyzed this function's body. Generic function bodies
    // are skipped during initial module analysis and only analyzed later
    // during `analyze_monomorph_bodies`. If the body was never analyzed,
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
        entities.as_entity_registry(),
        names,
        type_table,
        module_id,
    );
    vir_functions.push(vir);
}

/// Check whether sema has analyzed a function body by probing for NodeMap
/// entries. Returns `true` if body node data exists, `false` otherwise.
///
/// Generic function bodies are skipped during initial sema analysis. The
/// monomorph body analysis pass (`analyze_monomorph_bodies`) re-analyzes them
/// with concrete substitutions — for both main-program and module-originating
/// generics. This check is a safety guard: if sema analysis failed to
/// populate the NodeMap for a body (e.g., due to errors), VIR lowering would
/// panic, so we skip and let codegen fall back to the AST path.
pub fn body_has_sema_data(body: &FuncBody, node_map: &NodeMap) -> bool {
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
fn first_expr_node_id(stmt: &Stmt) -> Option<NodeId> {
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
/// registry, e.g. structural type params). Recurses into `Decl::Tests`
/// blocks so that test-scoped generic functions are also available for
/// monomorphized VIR lowering.
pub fn build_generic_func_map<'decl>(
    program: &'decl Program,
    interner: &Interner,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_id: ModuleId,
) -> FxHashMap<NameId, &'decl FuncDecl> {
    let namer = NamerLookup::new(names, interner);
    let mut collector = GenericFuncCollector {
        namer: &namer,
        names,
        entities,
        tests_virtual_modules,
        root_module_id: module_id,
        map: FxHashMap::default(),
    };
    collector.collect(&program.declarations, module_id);
    collector.map
}

/// Collect generic function ASTs from declarations, including test-scoped
/// functions that live under virtual test modules.
struct GenericFuncCollector<'a, 'namer> {
    namer: &'namer NamerLookup<'namer>,
    names: &'namer NameTable,
    entities: &'namer dyn LoweringEntityLookup,
    tests_virtual_modules: &'namer FxHashMap<Span, ModuleId>,
    root_module_id: ModuleId,
    map: FxHashMap<NameId, &'a FuncDecl>,
}

impl<'a, 'namer> GenericFuncCollector<'a, 'namer> {
    fn collect(&mut self, decls: &'a [Decl], module_id: ModuleId) {
        for decl in decls {
            match decl {
                Decl::Function(func) => {
                    // Include both explicit generics (`type_params`) and
                    // implicit generics (`generic_info`, e.g. structural constraints).
                    let module_candidates =
                        [module_id, self.root_module_id, self.names.main_module()];
                    for (idx, candidate_module) in module_candidates.into_iter().enumerate() {
                        if module_candidates[..idx].contains(&candidate_module) {
                            continue;
                        }
                        let Some(name_id) = self.namer.function(candidate_module, func.name) else {
                            continue;
                        };
                        let Some(func_id) = self.entities.function_by_name(name_id) else {
                            continue;
                        };
                        let is_generic = !func.type_params.is_empty()
                            || self.entities.get_function(func_id).generic_info.is_some();
                        if is_generic {
                            self.map.insert(name_id, func);
                        }
                    }
                }
                Decl::Tests(tests_decl) => {
                    let tests_module_id = self
                        .tests_virtual_modules
                        .get(&tests_decl.span)
                        .copied()
                        .unwrap_or(module_id);
                    self.collect(&tests_decl.decls, tests_module_id);
                }
                _ => {}
            }
        }
    }
}
