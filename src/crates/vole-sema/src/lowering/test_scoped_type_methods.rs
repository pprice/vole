use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::implement_blocks::{
    LowerImplementDefaultMethodsArgs, LowerImplementDirectMethodsArgs,
    LowerImplementStaticMethodsArgs, lower_implement_default_methods,
    lower_implement_direct_methods, lower_implement_static_methods, resolve_implement_target,
};
use super::type_methods::{lower_type_default_methods, lower_type_methods};
use crate::LoweringEntityLookup;
use crate::vir_lower::lower_function;
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{ModuleId, NameTable, NamerLookup, Span};
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

/// Lower type methods for classes/structs declared inside test blocks.
///
/// Test blocks can contain `Decl::Class` and `Decl::Struct` declarations that
/// are scoped to a virtual module. This function recursively walks `Decl::Tests`
/// blocks and lowers their class/struct methods (direct + default) to VIR.
#[allow(clippy::too_many_arguments)]
pub fn lower_test_scoped_type_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_type_methods(
                tests_decl,
                program,
                interner,
                names,
                entities,
                type_arena,
                node_map,
                tests_virtual_modules,
                module_programs,
                module_id,
                vir_functions,
                type_table,
            );
        }
    }
}

/// Recursively lower type methods from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_type_methods(
    tests_decl: &vole_frontend::ast::TestsDecl,
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let virtual_module_id = tests_virtual_modules
        .get(&tests_decl.span)
        .copied()
        .unwrap_or_else(|| names.main_module());

    // Test-scoped functions are registered under the program's module_id (not the virtual
    // test module), so use the passed module_id for function name resolution. This must
    // match what codegen uses in compile_function (program_module = analyzed.module_id()).
    let main_module_id = module_id;

    for inner_decl in &tests_decl.decls {
        match inner_decl {
            Decl::Function(func) => {
                if !func.type_params.is_empty() {
                    continue;
                }
                // Resolve the function in the main module (test-scoped functions use
                // program_module for name resolution, same as top-level functions)
                let func_id_and_def = {
                    let namer = NamerLookup::new(names, interner);
                    let name_id = namer.function(main_module_id, func.name);
                    name_id.and_then(|nid| {
                        let fid = entities.function_by_name(nid)?;
                        let fdef = entities.get_function(fid);
                        if fdef.generic_info.is_some() {
                            return None;
                        }
                        Some((fid, fdef))
                    })
                };
                if let Some((func_id, func_def)) = func_id_and_def {
                    let param_types: Vec<_> = func
                        .params
                        .iter()
                        .zip(func_def.signature.params_id.iter())
                        .map(|(p, &ty)| (p.name, ty))
                        .collect();
                    let vir = lower_function(
                        func,
                        func_id,
                        interner.resolve(func.name).to_string(),
                        &param_types,
                        func_def.signature.return_type_id,
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
                    virtual_module_id,
                    vir_functions,
                    type_table,
                );
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
                    virtual_module_id,
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
                    virtual_module_id,
                    vir_functions,
                    type_table,
                );
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
                    virtual_module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Implement(impl_block) => {
                let type_def_id = resolve_implement_target(
                    &impl_block.target_type,
                    interner,
                    names,
                    entities,
                    virtual_module_id,
                );
                if let Some(type_def_id) = type_def_id {
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
                        module_programs,
                        vir_functions,
                        type_table,
                    });
                }
            }
            Decl::Tests(nested) => {
                lower_tests_decl_type_methods(
                    nested,
                    program,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    tests_virtual_modules,
                    module_programs,
                    module_id,
                    vir_functions,
                    type_table,
                );
            }
            _ => {}
        }
    }
}
