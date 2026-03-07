use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::implement_blocks::{collect_default_method_ids, find_interface_method_ast};
use crate::LoweringEntityLookup;
use crate::vir_lower::{lower_interface_method, lower_method};
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program, Symbol};
use vole_identity::{MethodId, ModuleId, NameTable};
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

/// Lower non-generic class/struct instance methods and static methods to VIR.
///
/// Iterates the program's class and struct declarations, looks up each type's
/// methods in the entity registry, and lowers non-generic methods to VIR.
#[allow(clippy::too_many_arguments)]
pub fn lower_top_level_type_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        match decl {
            Decl::Class(class) => {
                if !class.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &class.methods,
                    class.statics.as_ref(),
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    vir_functions,
                    type_table,
                );
                // Also lower default methods from implemented interfaces
                let direct_method_names: HashSet<String> = class
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Struct(s) => {
                if !s.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &s.methods,
                    s.statics.as_ref(),
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    vir_functions,
                    type_table,
                );
                // Also lower default methods from implemented interfaces
                let direct_method_names: HashSet<String> = s
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            _ => {}
        }
    }
}

/// Lower instance methods and static methods for a single type declaration.
#[allow(clippy::too_many_arguments)]
pub fn lower_type_methods(
    methods: &[vole_frontend::FuncDecl],
    statics: Option<&vole_frontend::ast::StaticsBlock>,
    type_name: Symbol,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Resolve all name lookups first while interner is borrowed immutably
    let (type_def_id, resolved_methods, resolved_statics) = {
        let namer = vole_identity::NamerLookup::new(names, interner);
        let Some(type_name_id) = names.name_id(module_id, &[type_name], interner) else {
            return;
        };
        let Some(type_def_id) = entities.type_by_name(type_name_id) else {
            return;
        };

        let resolved_methods: Vec<_> = methods
            .iter()
            .filter_map(|method| {
                if !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect();

        let resolved_statics: Vec<_> = statics
            .map(|s| {
                s.methods
                    .iter()
                    .filter_map(|method| {
                        if method.body.is_none() || !method.type_params.is_empty() {
                            return None;
                        }
                        let method_name_id = namer.method(method.name)?;
                        let mid =
                            entities.find_static_method_on_type(type_def_id, method_name_id)?;
                        let method_def = entities.get_method(mid);
                        if !method_def.method_type_params.is_empty() {
                            return None;
                        }
                        Some((method, mid, method_def))
                    })
                    .collect()
            })
            .unwrap_or_default();

        (type_def_id, resolved_methods, resolved_statics)
    };

    // Now lower with &mut interner (namer is dropped, no immutable borrow)
    let _ = type_def_id;
    let type_name_str = interner.resolve(type_name).to_string();

    for (method, mid, method_def) in resolved_methods {
        lower_single_method(
            method,
            mid,
            method_def,
            &type_name_str,
            interner,
            names,
            node_map,
            type_arena,
            entities,
            vir_functions,
            type_table,
            module_id,
        );
    }

    for (method, mid, method_def) in resolved_statics {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();
        if let Some(vir) = lower_interface_method(
            method,
            mid,
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
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower default methods from implemented interfaces for a class or struct.
///
/// Finds interface default methods inherited by `type_name` and lowers them to VIR.
/// Direct methods (explicitly defined on the type) are skipped since they override
/// the default. This covers default methods from the type's own `implements` clause,
/// as opposed to `lower_implement_default_methods` which covers `extend T with I` blocks.
#[allow(clippy::too_many_arguments)]
pub fn lower_type_default_methods(
    direct_method_names: &HashSet<String>,
    type_name: Symbol,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    program: &Program,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Resolve type_def_id
    let Some(type_name_id) = names.name_id(module_id, &[type_name], interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };

    let type_name_str = interner.resolve(type_name).to_string();

    // Find default methods from implemented interfaces
    let default_methods =
        collect_default_method_ids(type_def_id, entities, names, direct_method_names);

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
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
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
            module_id,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower a single instance method to VIR and push it onto the functions vec.
#[allow(clippy::too_many_arguments)]
fn lower_single_method(
    method: &vole_frontend::FuncDecl,
    method_id: MethodId,
    method_def: &crate::MethodDef,
    type_name_str: &str,
    interner: &mut Interner,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
) {
    let arena_sig = method_def.signature_id;
    // We need the type arena to unwrap the signature, but we don't have it here.
    // Instead, use the AST param names + entity registry param types.
    // MethodDef doesn't store params_id directly, so we extract from signature.
    // Since we can't unwrap_function without the TypeArena, pass param names
    // paired with placeholder types (UNKNOWN). VIR lowering embeds types from
    // sema's NodeMap, so the placeholder types are not used for codegen.
    let method_name_str = interner.resolve(method.name);
    let display_name = format!("{}::{}", type_name_str, method_name_str);

    // Create placeholder entries matching the AST params.
    let param_types: Vec<_> = method
        .params
        .iter()
        .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
        .collect();

    let vir = lower_method(
        method,
        method_id,
        display_name,
        &param_types,
        arena_sig, // return_type from entity registry
        node_map,
        interner,
        type_arena,
        entities.as_entity_registry(),
        names,
        type_table,
        module_id,
    );
    vir_functions.push(vir);
}

/// Lower non-generic type methods from imported modules to VIR.
///
/// Two passes: first lowers direct instance + static methods, then lowers
/// default methods from implemented interfaces. The second pass needs
/// immutable access to `module_programs` for cross-module interface AST
/// lookup, so we collect per-type work items during the first (mutable) pass
/// and process them in a second (immutable) pass.
#[allow(clippy::too_many_arguments)]
pub fn lower_module_type_methods(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // --- Pass 1: lower direct + static methods (needs &mut interner) ---
    // Also collect (module_path, type_name, direct_method_names) for pass 2.
    struct DefaultMethodWork {
        module_path: String,
        type_name: Symbol,
        direct_method_names: HashSet<String>,
    }
    let mut default_method_work: Vec<DefaultMethodWork> = Vec::new();

    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    if !class.type_params.is_empty() {
                        continue;
                    }
                    lower_type_methods(
                        &class.methods,
                        class.statics.as_ref(),
                        class.name,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        module_id,
                        vir_functions,
                        type_table,
                    );
                    let direct_method_names: HashSet<String> = class
                        .methods
                        .iter()
                        .map(|m| interner.resolve(m.name).to_string())
                        .collect();
                    default_method_work.push(DefaultMethodWork {
                        module_path: module_path.clone(),
                        type_name: class.name,
                        direct_method_names,
                    });
                }
                Decl::Struct(s) => {
                    if !s.type_params.is_empty() {
                        continue;
                    }
                    lower_type_methods(
                        &s.methods,
                        s.statics.as_ref(),
                        s.name,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        module_id,
                        vir_functions,
                        type_table,
                    );
                    let direct_method_names: HashSet<String> = s
                        .methods
                        .iter()
                        .map(|m| interner.resolve(m.name).to_string())
                        .collect();
                    default_method_work.push(DefaultMethodWork {
                        module_path: module_path.clone(),
                        type_name: s.name,
                        direct_method_names,
                    });
                }
                _ => {}
            }
        }
    }

    // --- Pass 2: lower default methods from interfaces (needs shared module_programs) ---
    for work in default_method_work {
        let Some((program, module_interner)) = module_programs.get_mut(&work.module_path) else {
            continue;
        };
        let module_id = names
            .module_id_if_known(&work.module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        // For module types, pass only the module's own program for interface lookup.
        // Cross-module interface lookup is not available here (borrow limitation),
        // but module types typically implement interfaces defined in the same module
        // or in the stdlib (which is also in module_programs). The implement-block
        // lowering handles cross-module cases separately.
        lower_type_default_methods(
            &work.direct_method_names,
            work.type_name,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            None, // cross-module lookup not available in this pass
            vir_functions,
            type_table,
        );
    }
}
