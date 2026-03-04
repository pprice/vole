use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::lambda_search::collect_lambdas_in_program;
use crate::LoweringEntityLookup;
use crate::{NodeMap, TypeArena};
use vole_frontend::{Interner, LambdaExpr, Program};
use vole_identity::{ModuleId, NameTable, NodeId, Span};
use vole_vir::VirRef;
use vole_vir::type_table::VirTypeTable;

pub struct LowerLambdaDefaultInitsArgs<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub main_module_id: ModuleId,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub node_map: &'a NodeMap,
    pub type_arena: &'a TypeArena,
    pub modules_with_errors: &'a HashSet<String>,
    pub type_table: &'a mut VirTypeTable,
}

struct LowerSingleLambdaDefaultInitArgs<'a> {
    lambda_node_id: NodeId,
    lambda: &'a LambdaExpr,
    interner: &'a mut Interner,
    names: &'a NameTable,
    entities: &'a dyn LoweringEntityLookup,
    node_map: &'a NodeMap,
    type_arena: &'a TypeArena,
    type_table: &'a mut VirTypeTable,
    map: &'a mut FxHashMap<(NodeId, usize), VirRef>,
}

/// Lower default parameter expressions for lambdas referenced by call-site
/// `LambdaDefaults` metadata.
pub fn lower_lambda_default_inits(
    args: LowerLambdaDefaultInitsArgs<'_>,
) -> FxHashMap<(NodeId, usize), VirRef> {
    let LowerLambdaDefaultInitsArgs {
        program,
        interner,
        module_programs,
        main_module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        modules_with_errors,
        type_table,
    } = args;

    let mut map = FxHashMap::default();
    let lambda_nodes = node_map.collect_lambda_default_nodes();
    if lambda_nodes.is_empty() {
        return map;
    }

    let mut main_module_ids = HashSet::<ModuleId>::default();
    let _ = main_module_ids.insert(main_module_id);
    let _ = main_module_ids.insert(names.main_module());
    main_module_ids.extend(tests_virtual_modules.values().copied());

    // Partition lambda nodes by source: main program vs external modules.
    let mut main_lambda_nodes = Vec::new();
    // module_path -> Vec<NodeId>
    let mut external_lambda_nodes: FxHashMap<String, Vec<NodeId>> = FxHashMap::default();
    for lambda_node_id in lambda_nodes {
        if main_module_ids.contains(&lambda_node_id.module) {
            main_lambda_nodes.push(lambda_node_id);
        } else {
            let module_path = names.module_path(lambda_node_id.module).to_string();
            if !modules_with_errors.contains(&module_path) {
                external_lambda_nodes
                    .entry(module_path)
                    .or_default()
                    .push(lambda_node_id);
            }
        }
    }

    // Batch: collect all lambdas from the main program in one walk, then do
    // O(1) lookups per lambda node.
    if !main_lambda_nodes.is_empty() {
        let main_lambdas = collect_lambdas_in_program(program);
        for lambda_node_id in main_lambda_nodes {
            let Some(lambda) = main_lambdas.get(&lambda_node_id) else {
                continue;
            };
            lower_single_lambda_default_init(LowerSingleLambdaDefaultInitArgs {
                lambda_node_id,
                lambda,
                interner,
                names,
                entities,
                node_map,
                type_arena,
                type_table,
                map: &mut map,
            });
        }
    }

    // For external modules: collect all lambdas per module in one walk each.
    for (module_path, node_ids) in external_lambda_nodes {
        let Some((module_program, module_interner)) = module_programs.get_mut(&module_path) else {
            continue;
        };
        let module_interner = Rc::make_mut(module_interner);
        let module_lambdas = collect_lambdas_in_program(module_program);
        for lambda_node_id in node_ids {
            let Some(lambda) = module_lambdas.get(&lambda_node_id) else {
                continue;
            };
            lower_single_lambda_default_init(LowerSingleLambdaDefaultInitArgs {
                lambda_node_id,
                lambda,
                interner: module_interner,
                names,
                entities,
                node_map,
                type_arena,
                type_table,
                map: &mut map,
            });
        }
    }

    map
}

/// Lower default parameter expressions for a single lambda expression node.
fn lower_single_lambda_default_init(args: LowerSingleLambdaDefaultInitArgs<'_>) {
    use crate::vir_lower::expr::lower_expr;

    let LowerSingleLambdaDefaultInitArgs {
        lambda_node_id,
        lambda,
        interner,
        names,
        entities,
        node_map,
        type_arena,
        type_table,
        map,
    } = args;

    let mut ctx = crate::vir_lower::LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
        func_return_type: vole_identity::TypeId::VOID,
    };

    for (slot, param) in lambda.params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        let vir = lower_expr(default_expr, &mut ctx);
        map.insert((lambda_node_id, slot), vir);
    }
}
