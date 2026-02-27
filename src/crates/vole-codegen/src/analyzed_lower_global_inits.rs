use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::analyzed_lowering_lookup::LoweringEntityLookup;
use vole_frontend::{Decl, Interner, LetInit, Program, Symbol};
use vole_identity::NameTable;
use vole_sema::{NodeMap, TypeArena};
use vole_vir::VirRef;
use vole_vir::type_table::VirTypeTable;

/// Lower global variable initializer expressions from the main program to VIR.
///
/// Iterates `Decl::Let` declarations and lowers each initializer expression
/// using `lower_expr`. The resulting map is keyed by the binding's `Symbol`.
pub(crate) fn lower_global_inits(
    program: &Program,
    interner: &mut Interner,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    type_table: &mut VirTypeTable,
) -> FxHashMap<Symbol, VirRef> {
    use vole_sema::vir_lower::LoweringCtx;
    use vole_sema::vir_lower::expr::lower_expr;

    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
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
/// initializer expressions. Returns a nested map keyed first by module path,
/// then by the binding's `Symbol`.
pub(crate) fn lower_module_global_inits(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<String, FxHashMap<Symbol, VirRef>> {
    use vole_sema::vir_lower::expr::lower_expr;

    let mut result = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let interner = Rc::make_mut(module_interner);
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
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
