use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::vir_lower::lower_function;
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{ModuleId, NameTable, NamerLookup};
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

pub struct LowerTopLevelFunctionsArgs<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub module_id: ModuleId,
    pub type_table: &'a mut VirTypeTable,
}

pub struct LowerModuleFunctionsArgs<'a> {
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub modules_with_errors: &'a HashSet<String>,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

struct LowerModuleProgramFunctionsArgs<'a> {
    program: &'a Program,
    interner: &'a mut Interner,
    names: &'a NameTable,
    entities: &'a dyn LoweringEntityLookup,
    type_arena: &'a TypeArena,
    node_map: &'a NodeMap,
    module_id: ModuleId,
    vir_functions: &'a mut Vec<VirFunction>,
    type_table: &'a mut VirTypeTable,
}

/// Lower top-level non-generic functions to VIR.
///
/// Iterates the program's declarations, looks up each non-generic function
/// in the entity registry, and calls `lower_function()` to produce a
/// `VirFunction`. Generic functions and implicit generics are skipped
/// because they are monomorphized during codegen.
pub fn lower_top_level_functions(args: LowerTopLevelFunctionsArgs<'_>) -> Vec<VirFunction> {
    let LowerTopLevelFunctionsArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        type_table,
    } = args;

    // Collect (func_decl, func_id, func_def) tuples first while interner is
    // borrowed immutably by NamerLookup, then lower with &mut interner.
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        program
            .declarations
            .iter()
            .filter_map(|decl| {
                let Decl::Function(func) = decl else {
                    return None;
                };
                if !func.type_params.is_empty() {
                    return None;
                }
                let name_id = namer.function(module_id, func.name)?;
                let func_id = entities.function_by_name(name_id)?;
                let func_def = entities.get_function(func_id);
                if func_def.generic_info.is_some() {
                    return None;
                }
                Some((func, func_id, func_def))
            })
            .collect()
    };

    let mut vir_functions = Vec::new();
    for (func, func_id, func_def) in resolved {
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(func_def.signature.params_id.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();
        let display_name = interner.resolve(func.name).to_string();
        let vir = lower_function(
            func,
            func_id,
            display_name,
            &param_types,
            func_def.signature.return_type_id,
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

    vir_functions
}

/// Lower non-generic functions from imported modules to VIR.
///
/// Iterates each module's parsed program, resolves function identities through
/// the module's interner and module ID, and calls `lower_function()` for each
/// non-generic, non-implicitly-generic function. Modules with sema errors are
/// skipped to avoid INVALID type IDs.
pub fn lower_module_functions(args: LowerModuleFunctionsArgs<'_>) {
    let LowerModuleFunctionsArgs {
        module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions,
        type_table,
    } = args;

    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);
        lower_module_program_functions(LowerModuleProgramFunctionsArgs {
            program,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            vir_functions,
            type_table,
        });
    }
}

/// Lower non-generic functions from a single module program to VIR.
fn lower_module_program_functions(args: LowerModuleProgramFunctionsArgs<'_>) {
    let LowerModuleProgramFunctionsArgs {
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

    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        program
            .declarations
            .iter()
            .filter_map(|decl| {
                let Decl::Function(func) = decl else {
                    return None;
                };
                if !func.type_params.is_empty() {
                    return None;
                }
                let name_id = namer.function(module_id, func.name)?;
                let func_id = entities.function_by_name(name_id)?;
                let func_def = entities.get_function(func_id);
                if func_def.generic_info.is_some() {
                    return None;
                }
                Some((func, func_id, func_def))
            })
            .collect()
    };

    for (func, func_id, func_def) in resolved {
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(func_def.signature.params_id.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();
        let display_name = interner.resolve(func.name).to_string();
        let vir = lower_function(
            func,
            func_id,
            display_name,
            &param_types,
            func_def.signature.return_type_id,
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
}
