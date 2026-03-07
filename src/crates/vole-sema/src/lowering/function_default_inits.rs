use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::{NodeMap, TypeArena};
use vole_frontend::ast::{ExternalFunc, FuncDecl};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{FunctionId, ModuleId, NameTable, Span};
use vole_vir::VirRef;
use vole_vir::type_table::VirTypeTable;

pub struct LowerFunctionDefaultInitsArgs<'a> {
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

pub struct LowerModuleFunctionDefaultInitsArgs<'a> {
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    /// Main program interner — used to re-intern string literal symbols so
    /// they are resolvable from the main interner at codegen call sites.
    pub main_interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub node_map: &'a NodeMap,
    pub type_arena: &'a TypeArena,
    pub modules_with_errors: &'a HashSet<String>,
    pub type_table: &'a mut VirTypeTable,
}

/// Lower default parameter expressions for functions in the main program.
pub fn lower_function_default_inits(
    args: LowerFunctionDefaultInitsArgs<'_>,
) -> FxHashMap<(FunctionId, usize), VirRef> {
    let LowerFunctionDefaultInitsArgs {
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

    let mut ctx = crate::vir_lower::LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        module_id,
        generic: false,
        func_return_type: vole_identity::TypeId::VOID,
    };
    let mut map = FxHashMap::default();
    lower_function_default_inits_in_decls(
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

/// Lower default parameter expressions for imported-module functions.
pub fn lower_module_function_default_inits(
    args: LowerModuleFunctionDefaultInitsArgs<'_>,
) -> FxHashMap<(FunctionId, usize), VirRef> {
    let LowerModuleFunctionDefaultInitsArgs {
        module_programs,
        main_interner,
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
        let mut ctx = crate::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            module_id,
            generic: false,
            func_return_type: vole_identity::TypeId::VOID,
        };
        let before_keys: Vec<(FunctionId, usize)> = map.keys().copied().collect();
        lower_function_default_inits_in_decls(
            &program.declarations,
            module_id,
            None,
            names,
            entities,
            &mut ctx,
            &mut map,
        );

        // Re-intern string literal symbols from this module's interner
        // into the main interner.  Default VIR expressions are compiled
        // by codegen at the *caller's* call site (which uses the main
        // interner), so StringLiteral symbols must be resolvable there.
        let before_set: HashSet<(FunctionId, usize)> = before_keys.into_iter().collect();
        for (key, vir_ref) in map.iter_mut() {
            if !before_set.contains(key) {
                reintern_vir_string_literal(vir_ref, interner, main_interner);
            }
        }
    }
    map
}

/// Re-intern a `VirExpr::StringLiteral` symbol from `source_interner` into
/// `target_interner`.  Default expressions are typically simple literals, so
/// only the top-level node needs re-interning.
fn reintern_vir_string_literal(
    vir_ref: &mut VirRef,
    source_interner: &Interner,
    target_interner: &mut Interner,
) {
    use vole_vir::VirExpr;
    if let VirExpr::StringLiteral(sym) = vir_ref.as_mut() {
        let s = source_interner.resolve(*sym);
        *sym = target_interner.intern(s);
    }
}

/// Recursively lower function default parameter expressions in declarations.
fn lower_function_default_inits_in_decls(
    decls: &[Decl],
    module_id: ModuleId,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(FunctionId, usize), VirRef>,
) {
    for decl in decls {
        match decl {
            Decl::Function(func_decl) => {
                lower_function_default_params(func_decl, module_id, names, entities, ctx, map);
            }
            Decl::External(external_block) => {
                for external_func in &external_block.functions {
                    lower_external_function_default_params(
                        external_func,
                        module_id,
                        names,
                        entities,
                        ctx,
                        map,
                    );
                }
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                lower_function_default_inits_in_decls(
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

/// Lower default parameter expressions for a single external function declaration.
fn lower_external_function_default_params(
    func: &ExternalFunc,
    module_id: ModuleId,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(FunctionId, usize), VirRef>,
) {
    use crate::vir_lower::expr::lower_expr;

    let Some(name_id) = names.name_id(module_id, &[func.vole_name], ctx.interner) else {
        return;
    };
    let Some(func_id) = entities.function_by_name(name_id) else {
        return;
    };
    for (slot, param) in func.params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        if ctx.node_map.get_type(default_expr.id).is_none() {
            continue;
        }
        let vir = lower_expr(default_expr, ctx);
        map.insert((func_id, slot), vir);
    }
}

/// Lower default parameter expressions for a single function declaration.
fn lower_function_default_params(
    func: &FuncDecl,
    module_id: ModuleId,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(FunctionId, usize), VirRef>,
) {
    use crate::vir_lower::expr::lower_expr;

    let Some(name_id) = names.name_id(module_id, &[func.name], ctx.interner) else {
        return;
    };
    let Some(func_id) = entities.function_by_name(name_id) else {
        return;
    };
    for (slot, param) in func.params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        if ctx.node_map.get_type(default_expr.id).is_none() {
            continue;
        }
        let vir = lower_expr(default_expr, ctx);
        map.insert((func_id, slot), vir);
    }
}
