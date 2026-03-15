// lowering/vir_monomorph.rs
//
// VIR-level monomorphization helpers for facade.rs.

use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::LoweringEntityLookup;
use crate::TypeArena;
use vole_frontend::Interner;
use vole_identity::{NameId, NameTable};
use vole_vir::entity_metadata::VirEntityMetadata;
use vole_vir::implement_dispatch::VirImplementDispatch;
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirFunction, VirProgram};

/// Build generic VIR storage: index generic templates by NameId.
///
/// With the shared VirTypeTable, generic templates already use the same
/// VirTypeIds as the program's main table -- no remapping needed.
pub fn build_generic_vir_storage(
    pairs: Vec<(NameId, VirFunction)>,
) -> (Vec<VirFunction>, FxHashMap<NameId, usize>) {
    let mut map = FxHashMap::default();
    let mut functions = Vec::with_capacity(pairs.len());
    for (name_id, vir) in pairs {
        let idx = functions.len();
        map.insert(name_id, idx);
        functions.push(vir);
    }
    (functions, map)
}

/// Run VIR monomorphization for free-function generics.
///
/// Converts sema monomorph cache entries into VIR `MonomorphInstance` seeds,
/// builds a temporary `VirProgram`, runs VIR monomorphization with those
/// seeds, and merges the produced concrete functions back into the working
/// `vir_functions` vec and `type_table`.
///
/// Returns the instance index mapping `MonomorphInstance` to absolute function
/// index -- used later by `resolve_all_calls` to resolve `Unresolved`
/// calls to `VirDirect`.
#[expect(clippy::too_many_arguments)]
pub fn run_early_vir_monomorphize(
    vir_functions: &mut Vec<VirFunction>,
    generic_vir_functions: &[VirFunction],
    generic_vir_map: &FxHashMap<NameId, usize>,
    type_table: &mut VirTypeTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
) -> vole_vir::InstanceIndex {
    use crate::vir_lower::type_translate::translate_type_id;

    // Build seeds from the sema monomorph cache.
    let mut seeds: Vec<vole_vir::MonomorphInstance> = Vec::new();
    let mut seed_mangled_names: FxHashMap<vole_vir::MonomorphInstance, NameId> =
        FxHashMap::default();
    for sema_instance in entities.monomorph_instances() {
        let Some(func_id) = entities.function_by_name(sema_instance.original_name) else {
            continue;
        };
        // Find the generic VIR template to get the type param order.
        let template = generic_vir_functions.iter().find(|f| f.id == func_id);
        let Some(template) = template else {
            // No generic VIR template -- can't VIR-monomorphize this one.
            tracing::warn!(
                func_id = ?func_id,
                "VIR template not found for generic instance"
            );
            continue;
        };

        // Convert sema substitutions to ordered VIR type args.
        let mut type_args = Vec::with_capacity(template.type_params.len());
        let mut all_resolved = true;
        for &param_name in &template.type_params {
            if let Some(&sema_ty) = sema_instance.substitutions.get(&param_name) {
                let vir_ty = translate_type_id(type_table, sema_ty, type_arena);
                type_args.push(vir_ty);
            } else {
                // Substitution missing for this param -- skip this instance.
                all_resolved = false;
                break;
            }
        }
        if !all_resolved {
            continue;
        }

        let seed = vole_vir::MonomorphInstance {
            function_id: func_id,
            type_args,
        };
        seed_mangled_names.insert(seed.clone(), sema_instance.mangled_name);
        seeds.push(seed);
    }

    if seeds.is_empty() {
        return FxHashMap::default();
    }

    // Build a temporary VirProgram for VIR monomorphization.
    let mut temp_program = build_empty_vir_program(
        std::mem::take(type_table),
        std::mem::take(vir_functions),
        generic_vir_functions.to_vec(),
        generic_vir_map.clone(),
    );

    let mut result = vole_vir::monomorphize_with_seeds(&mut temp_program, seeds);

    for (instance, &rel_idx) in &result.instance_map {
        if let Some(&mangled_name_id) = seed_mangled_names.get(instance)
            && let Some(func) = result.functions.get_mut(rel_idx)
        {
            func.mangled_name_id = Some(mangled_name_id);
        }
    }

    let mut early_instance_index = vole_vir::InstanceIndex::default();

    if !result.functions.is_empty() {
        // Compute the base index where new functions will be appended.
        let base_index = temp_program.functions.len();
        temp_program.vir_monomorph_base = base_index;

        // Build the absolute instance index (base + relative offset).
        let abs_index: vole_vir::InstanceIndex = result
            .instance_map
            .into_iter()
            .map(|(instance, rel_idx)| (instance, base_index + rel_idx))
            .collect();

        // Append the monomorphized functions.
        temp_program.functions.extend(result.functions);

        // Resolve GenericCall -> VirDirect in all concrete functions.
        vole_vir::resolve_generic_calls(&mut temp_program.functions, &abs_index);

        // Preserve the instance index for the final resolve pass.
        early_instance_index = abs_index;
    }

    // Move the (possibly updated) type_table and functions back.
    *type_table = temp_program.type_table;
    *vir_functions = temp_program.functions;

    early_instance_index
}

/// Run the VIR monomorphization pass: discover generic calls in concrete
/// functions, instantiate generic templates, and resolve call targets.
///
/// This is the final VIR monomorph pass that runs on the fully assembled
/// VirProgram.  It catches any `GenericCall` sites in concrete functions
/// (including those produced by the early VIR monomorph pass) and resolves
/// them to `VirDirect` call targets.
pub fn run_vir_monomorphize(program: &mut VirProgram) {
    let result = vole_vir::monomorphize(program);

    // Build the instance index from this pass's results (may be empty).
    let abs_index: vole_vir::InstanceIndex = if result.functions.is_empty() {
        FxHashMap::default()
    } else {
        // Compute the base index where new functions will be appended.
        let base_index = program.functions.len();
        // Preserve the earliest VIR monomorph base if an earlier pass already
        // appended VIR monomorphized functions (e.g. early seeded monomorphize).
        if program.vir_monomorph_base == usize::MAX {
            program.vir_monomorph_base = base_index;
        }

        let index = result
            .instance_map
            .into_iter()
            .map(|(instance, rel_idx)| (instance, base_index + rel_idx))
            .collect();

        // Append the monomorphized functions to the program.
        program.functions.extend(result.functions);

        index
    };

    // Merge the early pass instance index with this pass's index.
    // This gives resolve_all_calls visibility into ALL VIR-monomorphized
    // functions, not just those from the final pass.
    let mut merged_index = std::mem::take(&mut program.vir_instance_index);
    merged_index.extend(abs_index);

    // Resolve GenericCall -> VirDirect and Unresolved (with monomorph key)
    // -> VirDirect in all concrete functions.  Only resolves Unresolved calls
    // whose targets are VIR-monomorphized (present in the instance index).
    vole_vir::resolve_all_calls(
        &mut program.functions,
        &merged_index,
        &program.entity_metadata,
    );

    // Store the merged index so test bodies can be resolved later (after the
    // program's real interner/name_table are set in the CLI pipeline).
    program.vir_instance_index = merged_index;
}

/// Build an empty VirProgram shell for temporary use during monomorphization.
fn build_empty_vir_program(
    type_table: VirTypeTable,
    functions: Vec<VirFunction>,
    generic_functions: Vec<VirFunction>,
    generic_map: FxHashMap<NameId, usize>,
) -> VirProgram {
    VirProgram {
        type_table,
        functions,
        monomorph_map: FxHashMap::default(),
        function_map: FxHashMap::default(),
        method_map: FxHashMap::default(),
        generic_functions,
        generic_map,
        tests: Vec::new(),
        global_inits: FxHashMap::default(),
        module_global_inits: FxHashMap::default(),
        function_default_inits: FxHashMap::default(),
        method_default_inits: FxHashMap::default(),
        lambda_default_inits: FxHashMap::default(),
        field_default_inits: FxHashMap::default(),
        annotation_inits: FxHashMap::default(),
        module_bindings: FxHashMap::default(),
        module_module_bindings: FxHashMap::default(),
        module_constants: FxHashMap::default(),
        module_exports: FxHashMap::default(),
        vir_monomorph_base: usize::MAX,
        vir_instance_index: FxHashMap::default(),
        entity_metadata: VirEntityMetadata::new(),
        implement_dispatch: VirImplementDispatch::new(),
        external_imports: Vec::new(),
        free_monomorphs: FxHashMap::default(),
        free_monomorphs_by_key: FxHashMap::default(),
        class_method_monomorphs: FxHashMap::default(),
        static_method_monomorphs: FxHashMap::default(),
        implement_method_monomorphs: FxHashMap::default(),
        module_interners: FxHashMap::default(),
        interner: Rc::new(Interner::new()),
        name_table: Rc::new(NameTable::new()),
        tests_virtual_modules: FxHashMap::default(),
        module_id: vole_identity::ModuleId::new(0),
        modules_with_errors: HashSet::new(),
        substitute_fallback: None,
    }
}
