use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, ExprKind, Interner, PatternKind, Program, Symbol};
use vole_identity::{ModuleId, NameTable, VirTypeId};
use vole_vir::type_table::VirTypeTable;

use crate::vir_lower::type_translate::translate_type_id;

/// Pre-resolved module export binding: (module_id, export_name, export_vir_type).
pub type VirModuleExportBinding = (ModuleId, Symbol, VirTypeId);

/// Extract lightweight module bindings (Symbol → (ModuleId, Symbol)) from top-level
/// destructuring imports.  Used to populate `CrossModuleCtx` for VIR call resolution
/// before VirTypeTable-dependent lowering runs.
pub fn extract_cross_module_bindings(
    program: &Program,
    node_map: &NodeMap,
    type_arena: &TypeArena,
) -> FxHashMap<Symbol, (ModuleId, Symbol)> {
    let mut map = FxHashMap::default();
    for decl in &program.declarations {
        if let Decl::LetTuple(let_tuple) = decl
            && let ExprKind::Import(_) = &let_tuple.init.kind
        {
            let Some(module_type_id) = node_map.get_type(let_tuple.init.id) else {
                continue;
            };
            let Some(module_info) = type_arena.unwrap_module(module_type_id) else {
                continue;
            };
            if let PatternKind::Record { fields, .. } = &let_tuple.pattern.kind {
                for field_pattern in fields {
                    map.insert(
                        field_pattern.binding,
                        (module_info.module_id, field_pattern.field_name),
                    );
                }
            }
        }
    }
    map
}

/// Extract module export bindings from top-level destructuring imports in the main program.
///
/// Scans `Decl::LetTuple` declarations where the init expression is an `import`.
/// For each destructured field, resolves the module's export type and produces
/// a binding keyed by the local binding symbol.
pub fn lower_module_bindings(
    program: &Program,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    names: &NameTable,
    interner: &Interner,
    type_table: &mut VirTypeTable,
) -> FxHashMap<Symbol, VirModuleExportBinding> {
    let mut map = FxHashMap::default();
    for decl in &program.declarations {
        if let Decl::LetTuple(let_tuple) = decl
            && let ExprKind::Import(_) = &let_tuple.init.kind
        {
            extract_bindings_from_let_tuple(
                let_tuple, node_map, type_arena, names, interner, type_table, &mut map,
            );
        }
    }
    map
}

/// Extract module export bindings from top-level destructuring imports in imported modules.
///
/// Iterates each module's declarations and extracts bindings from `let { ... } = import "..."`.
/// Returns a nested map keyed first by module path, then by local binding symbol.
pub fn lower_module_module_bindings(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<String, FxHashMap<Symbol, VirModuleExportBinding>> {
    let mut result = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let mut map = FxHashMap::default();
        for decl in &program.declarations {
            if let Decl::LetTuple(let_tuple) = decl
                && let ExprKind::Import(_) = &let_tuple.init.kind
            {
                extract_bindings_from_let_tuple(
                    let_tuple,
                    node_map,
                    type_arena,
                    names,
                    module_interner,
                    type_table,
                    &mut map,
                );
            }
        }
        if !map.is_empty() {
            result.insert(module_path.clone(), map);
        }
    }
    result
}

/// Extract module bindings from a single LetTuple destructuring import statement.
fn extract_bindings_from_let_tuple(
    let_tuple: &vole_frontend::ast::LetTupleStmt,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    names: &NameTable,
    interner: &Interner,
    type_table: &mut VirTypeTable,
    map: &mut FxHashMap<Symbol, VirModuleExportBinding>,
) {
    let Some(module_type_id) = node_map.get_type(let_tuple.init.id) else {
        return;
    };
    let Some(module_info) = type_arena.unwrap_module(module_type_id) else {
        return;
    };
    if let PatternKind::Record { fields, .. } = &let_tuple.pattern.kind {
        for field_pattern in fields {
            let export_name = field_pattern.field_name;
            let export_name_str = interner.resolve(export_name);

            let export_type_id = module_info
                .exports
                .iter()
                .find(|(name_id, _)| {
                    names.last_segment_str(*name_id).as_deref() == Some(export_name_str)
                })
                .map(|(_, ty)| *ty);

            if let Some(export_type_id) = export_type_id {
                let vir_export_ty = translate_type_id(type_table, export_type_id, type_arena);
                map.insert(
                    field_pattern.binding,
                    (module_info.module_id, export_name, vir_export_ty),
                );
            }
        }
    }
}
