use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::analyzed_lowering_lookup::LoweringEntityLookup;
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{MethodId, ModuleId, NameTable, NamerLookup, TypeDefId};
use vole_sema::vir_lower::{lower_interface_method, lower_method};
use vole_sema::{NodeMap, TypeArena};
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

pub(crate) struct LowerImplementBlockMethodsArgs<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub module_id: ModuleId,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

pub(crate) struct LowerModuleImplementBlockMethodsArgs<'a> {
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub modules_with_errors: &'a HashSet<String>,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

pub(crate) struct LowerImplementDirectMethodsArgs<'a> {
    pub methods: &'a [vole_frontend::FuncDecl],
    pub type_def_id: TypeDefId,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

pub(crate) struct LowerImplementStaticMethodsArgs<'a> {
    pub statics: &'a vole_frontend::ast::StaticsBlock,
    pub type_def_id: TypeDefId,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

pub(crate) struct LowerImplementDefaultMethodsArgs<'a> {
    pub impl_block: &'a vole_frontend::ast::ImplementBlock,
    pub type_def_id: TypeDefId,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub program: &'a Program,
    pub module_programs: Option<&'a FxHashMap<String, (Program, Rc<Interner>)>>,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

struct LowerSingleImplementBlockArgs<'a> {
    impl_block: &'a vole_frontend::ast::ImplementBlock,
    interner: &'a mut Interner,
    names: &'a NameTable,
    entities: &'a dyn LoweringEntityLookup,
    type_arena: &'a TypeArena,
    node_map: &'a NodeMap,
    module_id: ModuleId,
    program: &'a Program,
    vir_functions: &'a mut Vec<VirFunction>,
    type_table: &'a mut VirTypeTable,
}

/// Lower implement block methods (direct + statics) to VIR.
///
/// Iterates `Decl::Implement` blocks in the main program, resolves each
/// method's `MethodId` from the entity registry, and lowers the body.
/// Default interface methods (not in the implement block AST) are handled
/// by `lower_implement_default_methods`.
pub(crate) fn lower_implement_block_methods(args: LowerImplementBlockMethodsArgs<'_>) {
    let LowerImplementBlockMethodsArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        vir_functions,
        type_table,
    } = args;

    for decl in &program.declarations {
        let Decl::Implement(impl_block) = decl else {
            continue;
        };
        lower_single_implement_block(LowerSingleImplementBlockArgs {
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
        });
    }
}

fn lower_single_implement_block(args: LowerSingleImplementBlockArgs<'_>) {
    let LowerSingleImplementBlockArgs {
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
    } = args;

    let Some(type_def_id) = resolve_implement_target(
        &impl_block.target_type,
        interner,
        names,
        entities,
        module_id,
    ) else {
        return;
    };

    lower_implement_direct_methods(LowerImplementDirectMethodsArgs {
        methods: &impl_block.methods,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        vir_functions,
        type_table,
    });

    if let Some(ref statics) = impl_block.statics {
        lower_implement_static_methods(LowerImplementStaticMethodsArgs {
            statics,
            type_def_id,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            vir_functions,
            type_table,
        });
    }

    lower_implement_default_methods(LowerImplementDefaultMethodsArgs {
        impl_block,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        program,
        module_programs: None,
        vir_functions,
        type_table,
    });
}

/// Resolve the target type of an implement block to a `TypeDefId`.
///
/// Handles `Named`, `Generic`, `Primitive`, `Handle`, and `Array` target types.
pub(crate) fn resolve_implement_target(
    target_type: &vole_frontend::TypeExpr,
    interner: &Interner,
    names: &NameTable,
    entities: &dyn LoweringEntityLookup,
    module_id: ModuleId,
) -> Option<TypeDefId> {
    use vole_frontend::TypeExprKind;
    match &target_type.kind {
        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
            if let Some(name_id) = names.name_id(module_id, &[*sym], interner)
                && let Some(tdef) = entities.type_by_name(name_id)
            {
                return Some(tdef);
            }
            let sym_str = interner.resolve(*sym);
            entities.type_by_short_name(sym_str, names)
        }
        TypeExprKind::Primitive(p) => {
            let prim_name = match p {
                vole_frontend::PrimitiveType::I8 => "i8",
                vole_frontend::PrimitiveType::I16 => "i16",
                vole_frontend::PrimitiveType::I32 => "i32",
                vole_frontend::PrimitiveType::I64 => "i64",
                vole_frontend::PrimitiveType::I128 => "i128",
                vole_frontend::PrimitiveType::U8 => "u8",
                vole_frontend::PrimitiveType::U16 => "u16",
                vole_frontend::PrimitiveType::U32 => "u32",
                vole_frontend::PrimitiveType::U64 => "u64",
                vole_frontend::PrimitiveType::F32 => "f32",
                vole_frontend::PrimitiveType::F64 => "f64",
                vole_frontend::PrimitiveType::F128 => "f128",
                vole_frontend::PrimitiveType::Bool => "bool",
                vole_frontend::PrimitiveType::String => "string",
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

/// Lower direct instance methods from an implement block to VIR.
pub(crate) fn lower_implement_direct_methods(args: LowerImplementDirectMethodsArgs<'_>) {
    let LowerImplementDirectMethodsArgs {
        methods,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        vir_functions,
        type_table,
    } = args;

    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    // Resolve methods first while interner is immutably borrowed by namer.
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        methods
            .iter()
            .filter_map(|method| {
                if !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let method_id = entities.find_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(method_id);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, method_id, method_def))
            })
            .collect()
    };

    for (method, method_id, method_def) in resolved {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|param| (param.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        let vir = lower_method(
            method,
            method_id,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        );
        vir_functions.push(vir);
    }
}

/// Lower static methods from an implement block's statics section to VIR.
pub(crate) fn lower_implement_static_methods(args: LowerImplementStaticMethodsArgs<'_>) {
    let LowerImplementStaticMethodsArgs {
        statics,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        vir_functions,
        type_table,
    } = args;

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
                let method_id = entities.find_static_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(method_id);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, method_id, method_def))
            })
            .collect()
    };

    for (method, method_id, method_def) in resolved {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|param| (param.name, vole_identity::TypeId::UNKNOWN))
            .collect();
        if let Some(vir) = lower_interface_method(
            method,
            method_id,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower interface default methods for an implement block.
///
/// Finds default methods from implemented interfaces that are not overridden
/// by the implement block's direct methods. For each such default method,
/// finds the interface AST body and lowers it with the implementing type's
/// `MethodId`.
pub(crate) fn lower_implement_default_methods(args: LowerImplementDefaultMethodsArgs<'_>) {
    let LowerImplementDefaultMethodsArgs {
        impl_block,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        program,
        module_programs,
        vir_functions,
        type_table,
    } = args;

    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    let direct_method_names: HashSet<String> = impl_block
        .methods
        .iter()
        .map(|method| interner.resolve(method.name).to_string())
        .collect();
    let default_methods =
        collect_default_method_ids(type_def_id, entities, names, &direct_method_names);

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
            .map(|param| (param.name, vole_identity::TypeId::UNKNOWN))
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
            entities.as_entity_registry(),
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
pub(crate) fn collect_default_method_ids(
    type_def_id: TypeDefId,
    entities: &dyn LoweringEntityLookup,
    names: &NameTable,
    direct_method_names: &HashSet<String>,
) -> Vec<(MethodId, String, TypeDefId)> {
    let mut results = Vec::new();
    for interface_tdef_id in entities.get_implemented_interfaces(type_def_id) {
        // Keep interfaces with abstract params; VIR bodies are shared and
        // substitutions are applied at compile time.
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

/// Find an interface method AST node by interface and method name.
///
/// Searches the main program and, when provided, imported module programs.
pub(crate) fn find_interface_method_ast<'a>(
    interface_name: &str,
    method_name: &str,
    program: &'a Program,
    interner: &Interner,
    module_programs: Option<&'a FxHashMap<String, (Program, Rc<Interner>)>>,
) -> Option<&'a vole_frontend::ast::InterfaceMethod> {
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
/// Two-pass behavior:
/// 1) lower direct instance + static methods
/// 2) lower inherited interface default methods
pub(crate) fn lower_module_implement_block_methods(args: LowerModuleImplementBlockMethodsArgs<'_>) {
    let LowerModuleImplementBlockMethodsArgs {
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions,
        type_table,
    } = args;

    struct ImplDefaultWork {
        module_path: String,
        impl_decl_index: usize,
        type_def_id: TypeDefId,
    }

    let mut default_work = Vec::new();

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

            lower_implement_direct_methods(LowerImplementDirectMethodsArgs {
                methods: &impl_block.methods,
                type_def_id,
                interner,
                names,
                entities,
                type_arena,
                node_map,
                vir_functions,
                type_table,
            });

            if let Some(ref statics) = impl_block.statics {
                lower_implement_static_methods(LowerImplementStaticMethodsArgs {
                    statics,
                    type_def_id,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    vir_functions,
                    type_table,
                });
            }

            default_work.push(ImplDefaultWork {
                module_path: module_path.clone(),
                impl_decl_index: decl_idx,
                type_def_id,
            });
        }
    }

    for work in default_work {
        let Some((program, module_interner_rc)) = module_programs.get(&work.module_path) else {
            continue;
        };
        let mut interner_clone = (**module_interner_rc).clone();
        let Decl::Implement(impl_block) = &program.declarations[work.impl_decl_index] else {
            continue;
        };

        lower_implement_default_methods(LowerImplementDefaultMethodsArgs {
            impl_block,
            type_def_id: work.type_def_id,
            interner: &mut interner_clone,
            names,
            entities,
            type_arena,
            node_map,
            program,
            module_programs: Some(module_programs),
            vir_functions,
            type_table,
        });
    }
}
