use std::collections::HashSet;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::NodeMap;
use vole_frontend::ast::{FuncBody, Stmt};
use vole_frontend::{Decl, FuncDecl, Interner, Program};
use vole_identity::{FunctionId, ModuleId, NameId, NameTable, NamerLookup, NodeId, Span};

pub struct LowerMonomorphizedInstancesArgs<'a> {
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub vir_handled_function_ids: &'a HashSet<FunctionId>,
}

/// Asserts that all monomorphized instances were handled by VIR monomorph.
///
/// For each concrete instance in the monomorph cache, checks that it was either
/// handled by VIR monomorphization or is an external function (intrinsic).
/// Panics if any instance was missed — this proves the AST fallback path is
/// dead.
pub fn lower_monomorphized_instances(args: LowerMonomorphizedInstancesArgs<'_>) {
    let LowerMonomorphizedInstancesArgs {
        names,
        entities,
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

        // Skip generic external functions (e.g. compiler intrinsics).
        // These have no body to lower — codegen handles them via
        // call_dispatch() and intrinsic key resolution.
        if let Some(func_id) = entities.function_by_name(instance.original_name)
            && entities.get_function(func_id).is_external
        {
            continue;
        }

        // All monomorphized instances should be handled by VIR monomorph or
        // skipped as externals above. If we reach here, a generic function
        // was not lowered to a VIR template — this is a bug.
        let func_name = names.display(instance.original_name);
        let module_id = names.module_of(instance.original_name);
        let module_path = names.module_path(module_id);
        panic!(
            "AST fallback reached for monomorphized instance: \
             func={func_name}, module={module_path}. \
             All generic functions should have VIR templates."
        );
    }
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
