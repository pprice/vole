use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use vole_frontend::ast::FieldDef;
use vole_frontend::{Decl, Interner, Program, Symbol};
use vole_identity::{FieldId, ModuleId, NameTable, Span};
use vole_sema::LoweringEntityLookup;
use vole_sema::{NodeMap, TypeArena};
use vole_vir::VirRef;
use vole_vir::type_table::VirTypeTable;

pub(crate) struct LowerFieldDefaultInitsArgs<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub module_id: ModuleId,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub node_map: &'a NodeMap,
    pub type_arena: &'a TypeArena,
    pub type_table: &'a mut VirTypeTable,
}

pub(crate) struct LowerModuleFieldDefaultInitsArgs<'a> {
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub node_map: &'a NodeMap,
    pub type_arena: &'a TypeArena,
    pub modules_with_errors: &'a HashSet<String>,
    pub type_table: &'a mut VirTypeTable,
}

/// Lower default field initializer expressions from main-program type declarations to VIR.
///
/// Includes declarations nested in `tests {}` blocks (using virtual test-module
/// IDs when available) so test-scoped types can use VIR default initializers.
pub(crate) fn lower_field_default_inits(
    args: LowerFieldDefaultInitsArgs<'_>,
) -> FxHashMap<FieldId, VirRef> {
    use vole_sema::vir_lower::LoweringCtx;

    let LowerFieldDefaultInitsArgs {
        program,
        interner,
        module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        type_table,
    } = args;

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
    lower_field_default_inits_in_decls(
        &program.declarations,
        module_id,
        Some(tests_virtual_modules),
        names,
        entities,
        &mut ctx,
        &mut map,
    );
    map
}

/// Lower default field initializer expressions from imported module type declarations to VIR.
pub(crate) fn lower_module_field_default_inits(
    args: LowerModuleFieldDefaultInitsArgs<'_>,
) -> FxHashMap<FieldId, VirRef> {
    let LowerModuleFieldDefaultInitsArgs {
        module_programs,
        names,
        entities,
        node_map,
        type_arena,
        modules_with_errors,
        type_table,
    } = args;

    let mut map = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
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
        lower_field_default_inits_in_decls(
            &program.declarations,
            module_id,
            None,
            names,
            entities,
            &mut ctx,
            &mut map,
        );
    }
    map
}

/// Recursively lower default field initializer expressions in declarations.
fn lower_field_default_inits_in_decls(
    decls: &[Decl],
    module_id: ModuleId,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<FieldId, VirRef>,
) {
    for decl in decls {
        match decl {
            Decl::Class(class_decl) => {
                lower_type_default_fields(
                    class_decl.name,
                    &class_decl.fields,
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Struct(struct_decl) => {
                lower_type_default_fields(
                    struct_decl.name,
                    &struct_decl.fields,
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                lower_field_default_inits_in_decls(
                    &tests_decl.decls,
                    tests_module_id,
                    tests_virtual_modules,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            _ => {}
        }
    }
}

/// Lower default field initializers for a single class/struct declaration.
fn lower_type_default_fields(
    type_name: Symbol,
    fields: &[FieldDef],
    module_id: ModuleId,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<FieldId, VirRef>,
) {
    use vole_sema::vir_lower::expr::lower_expr;

    let Some(type_name_id) = names.name_id(module_id, &[type_name], ctx.interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };
    let type_def = entities.get_type(type_def_id);
    for (slot, field) in fields.iter().enumerate() {
        let Some(default_expr) = field.default_value.as_ref() else {
            continue;
        };
        // Skip expressions sema never analyzed (e.g. parse/type errors).
        if ctx.node_map.get_type(default_expr.id).is_none() {
            continue;
        }
        let Some(&field_id) = type_def.fields.get(slot) else {
            continue;
        };
        let vir = lower_expr(default_expr, ctx);
        map.insert(field_id, vir);
    }
}
