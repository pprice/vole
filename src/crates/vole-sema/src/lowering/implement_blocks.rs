use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::implement_registry::ImplementRegistry;
use crate::vir_lower::{CrossModuleCtx, lower_interface_method, lower_method};
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{MethodId, ModuleId, NameTable, NamerLookup, TypeDefId};
use vole_log::compile_timed;
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

pub struct LowerImplementBlockMethodsArgs<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub module_id: ModuleId,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
    pub cross_module: &'a CrossModuleCtx,
    pub implements: &'a ImplementRegistry,
}

pub struct LowerModuleImplementBlockMethodsArgs<'a> {
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub modules_with_errors: &'a HashSet<String>,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
    pub prelude_module_ids: &'a [ModuleId],
    pub implements: &'a ImplementRegistry,
}

pub struct LowerImplementDirectMethodsArgs<'a> {
    pub methods: &'a [vole_frontend::FuncDecl],
    pub type_def_id: TypeDefId,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
    pub module_id: ModuleId,
    pub cross_module: &'a CrossModuleCtx,
    pub implements: &'a ImplementRegistry,
}

pub struct LowerImplementStaticMethodsArgs<'a> {
    pub statics: &'a vole_frontend::ast::StaticsBlock,
    pub type_def_id: TypeDefId,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
    pub module_id: ModuleId,
    pub cross_module: &'a CrossModuleCtx,
    pub implements: &'a ImplementRegistry,
}

pub struct LowerImplementDefaultMethodsArgs<'a> {
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
    pub module_id: ModuleId,
    pub cross_module: &'a CrossModuleCtx,
    pub implements: &'a ImplementRegistry,
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
    cross_module: &'a CrossModuleCtx,
    implements: &'a ImplementRegistry,
}

/// Lower implement block methods (direct + statics) to VIR.
///
/// Iterates `Decl::Implement` blocks in the main program, resolves each
/// method's `MethodId` from the entity registry, and lowers the body.
/// Default interface methods (not in the implement block AST) are handled
/// by `lower_implement_default_methods`.
#[compile_timed(DEBUG)]
pub fn lower_implement_block_methods(args: LowerImplementBlockMethodsArgs<'_>) {
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
        cross_module,
        implements,
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
            cross_module,
            implements,
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
        cross_module,
        implements,
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
        module_id,
        cross_module,
        implements,
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
            module_id,
            cross_module,
            implements,
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
        module_id,
        cross_module,
        implements,
    });
}

/// Resolve the target type of an implement block to a `TypeDefId`.
///
/// Handles `Named`, `Generic`, `Primitive`, `Handle`, and `Array` target types.
pub fn resolve_implement_target(
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
pub fn lower_implement_direct_methods(args: LowerImplementDirectMethodsArgs<'_>) {
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
        module_id,
        cross_module,
        implements,
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
        // Unwrap function signature to get real param types and return type.
        let (param_types, return_type) = if let Some((sig_params, ret, _)) =
            type_arena.unwrap_function(method_def.signature_id)
        {
            let params: Vec<_> = method
                .params
                .iter()
                .zip(sig_params.iter())
                .map(|(p, &ty)| (p.name, ty))
                .collect();
            (params, ret)
        } else {
            let params: Vec<_> = method
                .params
                .iter()
                .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
                .collect();
            (params, method_def.signature_id)
        };

        let vir = lower_method(
            method,
            method_id,
            display_name,
            &param_types,
            return_type,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
            module_id,
            cross_module,
            implements,
        );
        vir_functions.push(vir);
    }
}

/// Lower static methods from an implement block's statics section to VIR.
pub fn lower_implement_static_methods(args: LowerImplementStaticMethodsArgs<'_>) {
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
        module_id,
        cross_module,
        implements,
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
            module_id,
            cross_module,
            implements,
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
pub fn lower_implement_default_methods(args: LowerImplementDefaultMethodsArgs<'_>) {
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
        module_id,
        cross_module,
        implements,
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
        let result = find_interface_method_ast(
            &iface_name_str,
            &method_name_str,
            program,
            interner,
            module_programs,
        );
        let Some(FoundInterfaceMethod {
            method: iface_method,
            foreign_interner,
        }) = result
        else {
            continue;
        };

        // When the method body comes from a foreign module (e.g. stdlib
        // prelude), its AST Symbol values are indices into that module's
        // interner.  For module-level lowering (this path), codegen will
        // also use the interface's interner, so we lower with the foreign
        // interner to keep VIR symbols consistent.
        // (The file-level path in lower_type_default_methods remaps symbols
        // to the user module's interner instead, since codegen uses that.)
        let mut foreign_clone;
        let lowering_interner: &mut Interner = if let Some(ref foreign) = foreign_interner {
            foreign_clone = (**foreign).clone();
            &mut foreign_clone
        } else {
            &mut *interner
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
            lowering_interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
            module_id,
            cross_module,
            implements,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Collect interface default method IDs for a type, skipping overridden ones.
///
/// Returns `(impl_method_id, method_name_str, interface_tdef_id)` tuples.
pub fn collect_default_method_ids(
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
/// When the method is found in a foreign module, `foreign_interner` is `Some`
/// with that module's `Rc<Interner>`.  Callers MUST use this interner
/// (via `Rc::make_mut`) when lowering the body — the AST symbols are indices
/// into that interner, not the current module's.
pub fn find_interface_method_ast<'a>(
    interface_name: &str,
    method_name: &str,
    program: &'a Program,
    interner: &Interner,
    module_programs: Option<&'a FxHashMap<String, (Program, Rc<Interner>)>>,
) -> Option<FoundInterfaceMethod<'a>> {
    for decl in &program.declarations {
        if let Decl::Interface(iface) = decl {
            if interner.resolve(iface.name) != interface_name {
                continue;
            }
            for method in &iface.methods {
                if interner.resolve(method.name) == method_name && method.body.is_some() {
                    return Some(FoundInterfaceMethod {
                        method,
                        foreign_interner: None,
                    });
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
                            return Some(FoundInterfaceMethod {
                                method,
                                foreign_interner: Some(Rc::clone(module_interner)),
                            });
                        }
                    }
                }
            }
        }
    }

    None
}

/// Result of [`find_interface_method_ast`].
pub struct FoundInterfaceMethod<'a> {
    pub method: &'a vole_frontend::ast::InterfaceMethod,
    /// When `Some`, the method body's AST symbols belong to this interner.
    /// Use `Rc::make_mut` to get `&mut Interner` for VIR lowering.
    pub foreign_interner: Option<Rc<Interner>>,
}

/// Lower implement block methods from imported modules to VIR.
///
/// Two-pass behavior:
/// 1) lower direct instance + static methods
/// 2) lower inherited interface default methods
pub fn lower_module_implement_block_methods(args: LowerModuleImplementBlockMethodsArgs<'_>) {
    let LowerModuleImplementBlockMethodsArgs {
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions,
        type_table,
        prelude_module_ids,
        implements,
    } = args;

    struct ImplDefaultWork {
        module_path: String,
        impl_decl_index: usize,
        type_def_id: TypeDefId,
        module_id: ModuleId,
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
        let module_bindings =
            super::functions::build_module_bindings(program, node_map, type_arena);
        let cross_module = CrossModuleCtx {
            module_bindings,
            prelude_module_ids: prelude_module_ids.to_vec(),
        };

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
                module_id,
                cross_module: &cross_module,
                implements,
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
                    module_id,
                    cross_module: &cross_module,
                    implements,
                });
            }

            default_work.push(ImplDefaultWork {
                module_path: module_path.clone(),
                impl_decl_index: decl_idx,
                type_def_id,
                module_id,
            });
        }
    }

    for work in default_work {
        let Some((program, module_interner_rc)) = module_programs.get(&work.module_path) else {
            continue;
        };
        let mut interner_clone = (**module_interner_rc).clone();
        let module_bindings =
            super::functions::build_module_bindings(program, node_map, type_arena);
        let cross_module = CrossModuleCtx {
            module_bindings,
            prelude_module_ids: prelude_module_ids.to_vec(),
        };
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
            module_id: work.module_id,
            cross_module: &cross_module,
            implements,
        });
    }
}
