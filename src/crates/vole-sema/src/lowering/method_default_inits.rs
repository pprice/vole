use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::{NodeMap, TypeArena};
use vole_frontend::ast::{
    ExternalBlock, ExternalFunc, FuncDecl, ImplementBlock, InterfaceMethod, Param, StaticsBlock,
};
use vole_frontend::{Decl, Interner, PrimitiveType, Program, Symbol, TypeExpr, TypeExprKind};
use vole_identity::{MethodId, ModuleId, NameTable, NamerLookup, Span, TypeDefId};
use vole_vir::VirRef;
use vole_vir::type_table::VirTypeTable;

pub struct LowerMethodDefaultInitsArgs<'a> {
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

pub struct LowerModuleMethodDefaultInitsArgs<'a> {
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub node_map: &'a NodeMap,
    pub type_arena: &'a TypeArena,
    pub modules_with_errors: &'a HashSet<String>,
    pub type_table: &'a mut VirTypeTable,
}

/// Lower default parameter expressions for methods in the main program.
pub fn lower_method_default_inits(
    args: LowerMethodDefaultInitsArgs<'_>,
) -> FxHashMap<(MethodId, usize), VirRef> {
    let LowerMethodDefaultInitsArgs {
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
        generic: false,
        func_return_type: vole_identity::TypeId::VOID,
    };
    let mut map = FxHashMap::default();
    lower_method_default_inits_in_decls(
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

/// Lower default parameter expressions for methods in imported modules.
pub fn lower_module_method_default_inits(
    args: LowerModuleMethodDefaultInitsArgs<'_>,
) -> FxHashMap<(MethodId, usize), VirRef> {
    let LowerModuleMethodDefaultInitsArgs {
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
        lower_method_default_inits_in_decls(
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

/// Recursively lower method default parameter expressions in declarations.
fn lower_method_default_inits_in_decls(
    decls: &[Decl],
    module_id: ModuleId,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    for decl in decls {
        match decl {
            Decl::Class(class_decl) => {
                lower_type_decl_method_default_inits(
                    class_decl.name,
                    &class_decl.methods,
                    class_decl.statics.as_ref(),
                    class_decl.external.as_ref().into_iter(),
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Struct(struct_decl) => {
                lower_type_decl_method_default_inits(
                    struct_decl.name,
                    &struct_decl.methods,
                    struct_decl.statics.as_ref(),
                    std::iter::empty(),
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Interface(iface_decl) => {
                lower_type_decl_method_default_inits(
                    iface_decl.name,
                    &[],
                    iface_decl.statics.as_ref(),
                    iface_decl.external_blocks.iter(),
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
                lower_interface_method_decl_defaults(
                    iface_decl.name,
                    &iface_decl.methods,
                    false,
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Implement(impl_block) => {
                lower_implement_method_default_inits(
                    impl_block, module_id, names, entities, ctx, map,
                );
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                lower_method_default_inits_in_decls(
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

/// Lower method default params for class/struct/interface type declarations.
#[allow(clippy::too_many_arguments)]
fn lower_type_decl_method_default_inits<'a>(
    type_name: Symbol,
    methods: &[FuncDecl],
    statics: Option<&StaticsBlock>,
    external_blocks: impl Iterator<Item = &'a ExternalBlock>,
    module_id: ModuleId,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    let Some(type_name_id) = names.name_id(module_id, &[type_name], ctx.interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };

    for method in methods {
        if !method.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(method.name) else {
                continue;
            };
            entities.find_method_on_type(type_def_id, method_name_id)
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &method.params, ctx, map);
    }

    if let Some(statics) = statics {
        lower_interface_method_decl_defaults(
            type_name,
            &statics.methods,
            true,
            module_id,
            names,
            entities,
            ctx,
            map,
        );
        for external in &statics.external_blocks {
            lower_external_method_decl_defaults(
                type_def_id,
                &external.functions,
                true,
                names,
                ctx,
                entities,
                map,
            );
        }
    }

    for external in external_blocks {
        lower_external_method_decl_defaults(
            type_def_id,
            &external.functions,
            false,
            names,
            ctx,
            entities,
            map,
        );
    }
}

/// Lower method default params for interface-method AST nodes.
#[allow(clippy::too_many_arguments)]
fn lower_interface_method_decl_defaults(
    type_name: Symbol,
    methods: &[InterfaceMethod],
    is_static: bool,
    module_id: ModuleId,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    let Some(type_name_id) = names.name_id(module_id, &[type_name], ctx.interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };
    for method in methods {
        if !method.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(method.name) else {
                continue;
            };
            if is_static {
                entities.find_static_method_on_type(type_def_id, method_name_id)
            } else {
                entities.find_method_on_type(type_def_id, method_name_id)
            }
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &method.params, ctx, map);
    }
}

/// Lower method default params for external-method AST nodes.
fn lower_external_method_decl_defaults(
    type_def_id: TypeDefId,
    funcs: &[ExternalFunc],
    is_static: bool,
    names: &NameTable,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    entities: &dyn LoweringEntityLookup,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    for func in funcs {
        if !func.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(func.vole_name) else {
                continue;
            };
            if is_static {
                entities.find_static_method_on_type(type_def_id, method_name_id)
            } else {
                entities.find_method_on_type(type_def_id, method_name_id)
            }
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &func.params, ctx, map);
    }
}

/// Lower method default params from an `implement` block.
fn lower_implement_method_default_inits(
    impl_block: &ImplementBlock,
    module_id: ModuleId,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    let Some(type_def_id) = resolve_implement_target_for_defaults(
        &impl_block.target_type,
        ctx.interner,
        names,
        entities,
        module_id,
    ) else {
        return;
    };

    for method in &impl_block.methods {
        if !method.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(method.name) else {
                continue;
            };
            entities.find_method_on_type(type_def_id, method_name_id)
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &method.params, ctx, map);
    }
    if let Some(external) = impl_block.external.as_ref() {
        lower_external_method_decl_defaults(
            type_def_id,
            &external.functions,
            false,
            names,
            ctx,
            entities,
            map,
        );
    }
    if let Some(statics) = impl_block.statics.as_ref() {
        for method in &statics.methods {
            if !method.type_params.is_empty() {
                continue;
            }
            let method_id = {
                let namer = NamerLookup::new(names, ctx.interner);
                let Some(method_name_id) = namer.method(method.name) else {
                    continue;
                };
                entities.find_static_method_on_type(type_def_id, method_name_id)
            };
            let Some(method_id) = method_id else {
                continue;
            };
            lower_method_default_params(method_id, &method.params, ctx, map);
        }
        for external in &statics.external_blocks {
            lower_external_method_decl_defaults(
                type_def_id,
                &external.functions,
                true,
                names,
                ctx,
                entities,
                map,
            );
        }
    }
}

/// Resolve the target type of an implement block to a `TypeDefId`.
fn resolve_implement_target_for_defaults(
    target_type: &TypeExpr,
    interner: &Interner,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    module_id: ModuleId,
) -> Option<TypeDefId> {
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
            let prim_name = match p {
                PrimitiveType::I8 => "i8",
                PrimitiveType::I16 => "i16",
                PrimitiveType::I32 => "i32",
                PrimitiveType::I64 => "i64",
                PrimitiveType::I128 => "i128",
                PrimitiveType::U8 => "u8",
                PrimitiveType::U16 => "u16",
                PrimitiveType::U32 => "u32",
                PrimitiveType::U64 => "u64",
                PrimitiveType::F32 => "f32",
                PrimitiveType::F64 => "f64",
                PrimitiveType::F128 => "f128",
                PrimitiveType::Bool => "bool",
                PrimitiveType::String => "string",
            };
            entities.type_by_short_name(prim_name, names)
        }
        TypeExprKind::Handle => entities.type_by_short_name("handle", names),
        TypeExprKind::Array(_) => entities
            .array_name_id()
            .and_then(|name_id| entities.type_by_name(name_id)),
        _ => None,
    }
}

/// Lower default parameter expressions for a single method identifier.
fn lower_method_default_params(
    method_id: MethodId,
    params: &[Param],
    ctx: &mut crate::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    use crate::vir_lower::expr::lower_expr;

    for (slot, param) in params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        let vir = lower_expr(default_expr, ctx);
        map.insert((method_id, slot), vir);
    }
}
