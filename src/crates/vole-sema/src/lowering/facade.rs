use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::annotation_inits::lower_annotation_inits;
use super::entity_metadata::{
    PopulateImplementBlockEntriesArgs, build_entity_metadata, populate_implement_block_entries,
};
use super::field_default_inits::{
    LowerFieldDefaultInitsArgs, LowerModuleFieldDefaultInitsArgs, lower_field_default_inits,
    lower_module_field_default_inits,
};
use super::function_default_inits::{
    LowerFunctionDefaultInitsArgs, LowerModuleFunctionDefaultInitsArgs,
    lower_function_default_inits, lower_module_function_default_inits,
};
use super::functions::{
    LowerModuleFunctionsArgs, LowerTopLevelFunctionsArgs, lower_module_functions,
    lower_top_level_functions,
};
use super::global_inits::{lower_global_inits, lower_module_global_inits};
use super::implement_blocks::{
    LowerImplementBlockMethodsArgs, LowerModuleImplementBlockMethodsArgs,
    lower_implement_block_methods, lower_module_implement_block_methods,
};
use super::lambda_default_inits::{LowerLambdaDefaultInitsArgs, lower_lambda_default_inits};
use super::method_default_inits::{
    LowerMethodDefaultInitsArgs, LowerModuleMethodDefaultInitsArgs, lower_method_default_inits,
    lower_module_method_default_inits,
};
use super::module_bindings::{lower_module_bindings, lower_module_module_bindings};
use super::monomorph_functions::{
    LowerMonomorphizedInstancesArgs, build_generic_func_map, lower_monomorphized_instances,
};
use super::monomorph_info::populate_monomorph_info;
use super::test_scoped_type_methods::lower_test_scoped_type_methods;
use super::type_method_monomorph::{
    MethodMonomorphLoweringCtx, MethodMonomorphLoweringWork,
    lower_type_method_monomorphized_instances,
};
use super::type_methods::{lower_module_type_methods, lower_top_level_type_methods};
use crate::LoweringEntityLookup;
use crate::implement_registry::ImplementRegistry;
use crate::vir_lower::type_translate::sweep_unmapped_type_ids;
use crate::vir_lower::{lower_stmts, lower_test_body};
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{FunctionId, MethodId, ModuleId, NameId, NameTable, Span};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirFunction, VirProgram, VirTest};

pub struct LowerVirProgramArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a E,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    pub module_id: ModuleId,
    pub modules_with_errors: &'a HashSet<String>,
    pub generic_vir_functions: Vec<(NameId, VirFunction)>,
    /// Shared VIR type table pre-populated by sema analysis.
    ///
    /// Generic VIR templates already use VirTypeIds from this table, so no
    /// merge/remap is needed. Concrete VIR lowering continues interning into
    /// the same table.
    pub vir_type_table: VirTypeTable,
    pub implements: &'a ImplementRegistry,
}

pub struct LowerVirProgramOutput {
    pub vir_program: VirProgram,
}

/// Run the codegen-side VIR lowering orchestration and return assembled outputs.
pub fn lower_vir_program<E>(args: LowerVirProgramArgs<'_, E>) -> LowerVirProgramOutput
where
    E: LoweringEntityLookup,
{
    let LowerVirProgramArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        mut module_programs,
        module_id,
        modules_with_errors,
        generic_vir_functions,
        vir_type_table,
        implements,
    } = args;

    // Use the shared VIR type table from sema analysis.  Generic VIR
    // templates already use VirTypeIds from this table, so no merge/remap
    // is needed — concrete lowering continues interning into the same table.
    let mut type_table = vir_type_table;
    let mut vir_functions = lower_top_level_functions(LowerTopLevelFunctionsArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        type_table: &mut type_table,
    });
    lower_module_functions(LowerModuleFunctionsArgs {
        module_programs: &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions: &mut vir_functions,
        type_table: &mut type_table,
    });

    let (generic_vir_functions, generic_vir_map) = build_generic_vir_storage(generic_vir_functions);

    let vir_handled_function_ids = run_early_vir_monomorphize(
        &mut vir_functions,
        &generic_vir_functions,
        &generic_vir_map,
        &mut type_table,
        entities,
        type_arena,
    );

    let generic_func_asts = build_generic_func_map(
        program,
        interner,
        names,
        entities,
        tests_virtual_modules,
        module_id,
    );
    lower_monomorphized_instances(LowerMonomorphizedInstancesArgs {
        generic_func_asts: &generic_func_asts,
        module_programs: &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        interner,
        vir_functions: &mut vir_functions,
        type_table: &mut type_table,
        vir_handled_function_ids: &vir_handled_function_ids,
    });
    lower_top_level_type_methods(
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        Some(&module_programs),
        &mut vir_functions,
        &mut type_table,
    );
    lower_module_type_methods(
        &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        &mut vir_functions,
        &mut type_table,
    );
    lower_implement_block_methods(LowerImplementBlockMethodsArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        vir_functions: &mut vir_functions,
        type_table: &mut type_table,
    });
    lower_module_implement_block_methods(LowerModuleImplementBlockMethodsArgs {
        module_programs: &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions: &mut vir_functions,
        type_table: &mut type_table,
    });
    lower_test_scoped_type_methods(
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        Some(&module_programs),
        module_id,
        &mut vir_functions,
        &mut type_table,
    );
    let method_monomorph_ctx = MethodMonomorphLoweringCtx {
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
    };
    let mut method_monomorph_work = MethodMonomorphLoweringWork {
        program,
        interner,
        module_programs: &mut module_programs,
        tests_virtual_modules,
        module_id,
        vir_functions: &mut vir_functions,
        type_table: &mut type_table,
    };
    lower_type_method_monomorphized_instances(&mut method_monomorph_work, &method_monomorph_ctx);

    let vir_monomorph_map = build_vir_monomorph_map(&vir_functions);
    let vir_function_map = build_vir_function_map(&vir_functions);
    let vir_method_map = build_vir_method_map(&vir_functions);
    let vir_tests = lower_test_bodies(
        program,
        node_map,
        interner,
        type_arena,
        entities,
        names,
        &mut type_table,
    );
    let vir_global_inits = lower_global_inits(
        program,
        interner,
        node_map,
        type_arena,
        entities,
        names,
        &mut type_table,
    );
    let module_vir_global_inits = lower_module_global_inits(
        &mut module_programs,
        names,
        node_map,
        type_arena,
        entities,
        modules_with_errors,
        &mut type_table,
    );
    let vir_module_bindings = lower_module_bindings(
        program,
        node_map,
        type_arena,
        names,
        interner,
        &mut type_table,
    );
    let vir_module_module_bindings = lower_module_module_bindings(
        &mut module_programs,
        names,
        node_map,
        type_arena,
        modules_with_errors,
        &mut type_table,
    );
    let mut vir_function_default_inits =
        lower_function_default_inits(LowerFunctionDefaultInitsArgs {
            program,
            interner,
            module_id,
            tests_virtual_modules,
            names,
            entities,
            node_map,
            type_arena,
            type_table: &mut type_table,
        });
    let module_vir_function_default_inits =
        lower_module_function_default_inits(LowerModuleFunctionDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table: &mut type_table,
        });
    vir_function_default_inits.extend(module_vir_function_default_inits);

    let mut vir_method_default_inits = lower_method_default_inits(LowerMethodDefaultInitsArgs {
        program,
        interner,
        module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        type_table: &mut type_table,
    });
    let module_vir_method_default_inits =
        lower_module_method_default_inits(LowerModuleMethodDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table: &mut type_table,
        });
    vir_method_default_inits.extend(module_vir_method_default_inits);

    let vir_lambda_default_inits = lower_lambda_default_inits(LowerLambdaDefaultInitsArgs {
        program,
        interner,
        module_programs: &mut module_programs,
        main_module_id: module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        modules_with_errors,
        type_table: &mut type_table,
    });
    let mut vir_field_default_inits = lower_field_default_inits(LowerFieldDefaultInitsArgs {
        program,
        interner,
        module_id,
        tests_virtual_modules,
        names,
        entities,
        node_map,
        type_arena,
        type_table: &mut type_table,
    });
    let module_vir_field_default_inits =
        lower_module_field_default_inits(LowerModuleFieldDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table: &mut type_table,
        });
    vir_field_default_inits.extend(module_vir_field_default_inits);

    let monomorph_info = populate_monomorph_info(entities, type_arena, &mut type_table);
    let vir_annotation_inits = lower_annotation_inits(entities, interner, names);
    let mut entity_metadata =
        build_entity_metadata(entities, type_arena, &mut type_table, interner, names);
    populate_implement_block_entries(PopulateImplementBlockEntriesArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        module_id,
        module_programs: &module_programs,
        modules_with_errors,
        meta: &mut entity_metadata,
    });
    let implement_dispatch = build_implement_dispatch(implements);
    // Collect module interners from module_programs for VirProgram.
    let module_interners: FxHashMap<String, Rc<Interner>> = module_programs
        .iter()
        .map(|(path, (_program, interner))| (path.clone(), Rc::clone(interner)))
        .collect();
    // Populate module metadata for codegen (replaces arena().module_metadata
    // and arena().unwrap_module lookups).
    let (module_constants, module_exports) = collect_module_metadata(type_arena);
    let mut vir_program = VirProgram {
        type_table,
        functions: vir_functions,
        monomorph_map: vir_monomorph_map,
        function_map: vir_function_map,
        method_map: vir_method_map,
        generic_functions: generic_vir_functions,
        generic_map: generic_vir_map,
        tests: vir_tests,
        global_inits: vir_global_inits,
        module_global_inits: module_vir_global_inits,
        function_default_inits: vir_function_default_inits,
        method_default_inits: vir_method_default_inits,
        lambda_default_inits: vir_lambda_default_inits,
        field_default_inits: vir_field_default_inits,
        annotation_inits: vir_annotation_inits,
        module_bindings: vir_module_bindings,
        module_module_bindings: vir_module_module_bindings,
        module_constants,
        module_exports,
        vir_monomorph_base: usize::MAX,
        entity_metadata,
        implement_dispatch,
        free_monomorphs: monomorph_info.free_monomorphs,
        free_monomorphs_by_key: monomorph_info.free_monomorphs_by_key,
        class_method_monomorphs: monomorph_info.class_method_monomorphs,
        static_method_monomorphs: monomorph_info.static_method_monomorphs,
        module_interners,
        interner: Rc::new(Interner::new()),
        name_table: Rc::new(NameTable::new()),
    };
    run_vir_monomorphize(&mut vir_program);

    // Sweep all TypeIds in the arena and populate VirTypeId mappings for any
    // that were not encountered during on-demand lowering.  This catches the
    // monomorphized types created by sema's TypeArena::substitute() during
    // Pass 2 generic analysis (~1,900 types in typical programs).
    sweep_unmapped_type_ids(&mut vir_program.type_table, type_arena);

    LowerVirProgramOutput { vir_program }
}

/// Collect module metadata (constants and exports) from the type arena for
/// codegen to use without direct arena access.
type ModuleConstants = FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>;
type ModuleExports =
    FxHashMap<vole_identity::TypeId, (ModuleId, Vec<(NameId, vole_identity::TypeId)>)>;

fn collect_module_metadata(type_arena: &TypeArena) -> (ModuleConstants, ModuleExports) {
    let mut constants = FxHashMap::default();
    let mut exports = FxHashMap::default();

    // Collect per-module constants from arena's module_metadata.
    for (module_id, meta) in type_arena.all_module_metadata() {
        for (name_id, value) in &meta.constants {
            constants.insert((*module_id, *name_id), value.clone());
        }
    }

    // Collect module type exports from all interned Module types.
    for (type_id, module_info) in type_arena.all_module_types() {
        let export_vec: Vec<(NameId, vole_identity::TypeId)> =
            module_info.exports.iter().map(|&(n, t)| (n, t)).collect();
        exports.insert(type_id, (module_info.module_id, export_vec));
    }

    (constants, exports)
}

/// Build a lookup map from monomorphized mangled NameId to VirFunction index.
///
/// Only includes VIR functions that have a `mangled_name_id` set (i.e.,
/// monomorphized instances).  Non-generic functions are not indexed here
/// because they are compiled via the normal (non-monomorph) path.
fn build_vir_monomorph_map(vir_functions: &[VirFunction]) -> FxHashMap<NameId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(name_id) = vf.mangled_name_id {
            map.insert(name_id, idx);
        }
    }
    map
}

/// Build a lookup map from semantic FunctionId to VirFunction index.
///
/// Only includes non-monomorphized functions (those without a `mangled_name_id`).
/// Monomorphized instances are looked up via `vir_monomorph_map` instead.
fn build_vir_function_map(vir_functions: &[VirFunction]) -> FxHashMap<FunctionId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if vf.mangled_name_id.is_none() && vf.method_id.is_none() {
            map.insert(vf.id, idx);
        }
    }
    map
}

/// Build a lookup map from semantic MethodId to VirFunction index.
///
/// Only includes VIR functions that have a `method_id` set (class/struct
/// methods and static methods).
fn build_vir_method_map(vir_functions: &[VirFunction]) -> FxHashMap<MethodId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(method_id) = vf.method_id {
            map.insert(method_id, idx);
        }
    }
    map
}

/// Lower all test function bodies in the program to VIR.
///
/// Walks the program's `Decl::Tests` blocks (including nested ones) and
/// lowers each `TestCase.body` to a `VirBody`.  Returns a map keyed by
/// the `TestCase`'s `Span` for O(1) lookup during test compilation.
fn lower_test_bodies(
    program: &Program,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    type_table: &mut VirTypeTable,
) -> Vec<VirTest> {
    let mut tests = Vec::new();
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_bodies(
                tests_decl, node_map, interner, type_arena, entities, names, &mut tests, type_table,
            );
        }
    }
    tests
}

/// Recursively lower test bodies from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_bodies(
    tests_decl: &vole_frontend::ast::TestsDecl,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    tests: &mut Vec<VirTest>,
    type_table: &mut VirTypeTable,
) {
    let scoped_let_stmts: Vec<vole_frontend::Stmt> = tests_decl
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Let(let_stmt) => Some(vole_frontend::Stmt::Let(let_stmt.clone())),
            Decl::LetTuple(let_tuple) => Some(vole_frontend::Stmt::LetTuple(let_tuple.clone())),
            _ => None,
        })
        .collect();
    let scoped_let_vir_stmts = if scoped_let_stmts.is_empty() {
        Vec::new()
    } else {
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
        lower_stmts(&scoped_let_stmts, &mut ctx).stmts
    };

    for test in &tests_decl.tests {
        let mut vir_body = lower_test_body(
            &test.body,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        );
        if !scoped_let_vir_stmts.is_empty() {
            vir_body
                .stmts
                .splice(0..0, scoped_let_vir_stmts.iter().cloned());
        }
        tests.push(VirTest {
            name: test.name.clone(),
            body: vir_body,
            span: test.span,
        });
    }
    // Recurse into nested tests blocks
    for decl in &tests_decl.decls {
        if let Decl::Tests(nested) = decl {
            lower_tests_decl_bodies(
                nested, node_map, interner, type_arena, entities, names, tests, type_table,
            );
        }
    }
}

/// Build generic VIR storage: index generic templates by NameId.
///
/// With the shared VirTypeTable, generic templates already use the same
/// VirTypeIds as the program's main table — no remapping needed.
fn build_generic_vir_storage(
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
/// Returns the set of `FunctionId`s for generic functions that were
/// successfully monomorphized -- `lower_monomorphized_instances` should skip
/// all sema cache entries whose `original_name` resolves to one of these.
#[allow(clippy::too_many_arguments)]
fn run_early_vir_monomorphize(
    vir_functions: &mut Vec<VirFunction>,
    generic_vir_functions: &[VirFunction],
    generic_vir_map: &FxHashMap<NameId, usize>,
    type_table: &mut VirTypeTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
) -> HashSet<FunctionId> {
    use crate::vir_lower::type_translate::translate_type_id;

    let mut handled = HashSet::new();

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
            // No generic VIR template — can't VIR-monomorphize this one.
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
                // Substitution missing for this param — skip this instance.
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
        return handled;
    }

    // Build a temporary VirProgram for VIR monomorphization.
    let mut temp_program = VirProgram {
        type_table: std::mem::take(type_table),
        functions: std::mem::take(vir_functions),
        monomorph_map: FxHashMap::default(),
        function_map: FxHashMap::default(),
        method_map: FxHashMap::default(),
        generic_functions: generic_vir_functions.to_vec(),
        generic_map: generic_vir_map.clone(),
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
        entity_metadata: vole_vir::VirEntityMetadata::new(),
        implement_dispatch: vole_vir::VirImplementDispatch::new(),
        free_monomorphs: FxHashMap::default(),
        free_monomorphs_by_key: FxHashMap::default(),
        class_method_monomorphs: FxHashMap::default(),
        static_method_monomorphs: FxHashMap::default(),
        module_interners: FxHashMap::default(),
        interner: Rc::new(Interner::new()),
        name_table: Rc::new(NameTable::new()),
    };

    let mut result = vole_vir::monomorphize_with_seeds(&mut temp_program, seeds);

    for (instance, &rel_idx) in &result.instance_map {
        if let Some(&mangled_name_id) = seed_mangled_names.get(instance)
            && let Some(func) = result.functions.get_mut(rel_idx)
        {
            func.mangled_name_id = Some(mangled_name_id);
        }
    }

    if !result.functions.is_empty() {
        // Record which generic FunctionIds were handled.
        for instance in result.instance_map.keys() {
            handled.insert(instance.function_id);
        }

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
    }

    // Move the (possibly updated) type_table and functions back.
    *type_table = temp_program.type_table;
    *vir_functions = temp_program.functions;

    handled
}

/// Run the VIR monomorphization pass: discover generic calls in concrete
/// functions, instantiate generic templates, and resolve call targets.
///
/// This is the final VIR monomorph pass that runs on the fully assembled
/// VirProgram.  It catches any `GenericCall` sites in concrete functions
/// (including those produced by the early VIR monomorph pass) and resolves
/// them to `VirDirect` call targets.
fn run_vir_monomorphize(program: &mut VirProgram) {
    let result = vole_vir::monomorphize(program);
    if result.functions.is_empty() {
        return;
    }

    // Compute the base index where new functions will be appended.
    let base_index = program.functions.len();
    // Preserve the earliest VIR monomorph base if an earlier pass already
    // appended VIR monomorphized functions (e.g. early seeded monomorphize).
    if program.vir_monomorph_base == usize::MAX {
        program.vir_monomorph_base = base_index;
    }

    // Build the absolute instance index (base + relative offset).
    let abs_index: vole_vir::InstanceIndex = result
        .instance_map
        .into_iter()
        .map(|(instance, rel_idx)| (instance, base_index + rel_idx))
        .collect();

    // Append the monomorphized functions to the program.
    program.functions.extend(result.functions);

    // Resolve GenericCall -> VirDirect in all concrete functions.
    vole_vir::resolve_generic_calls(&mut program.functions, &abs_index);
}

/// Build VIR implement-dispatch metadata from sema's `ImplementRegistry`.
///
/// Converts all registry entries into VIR-native types, populating the
/// four lookup maps (external_funcs, generic_externals,
/// generic_external_methods, methods).
fn build_implement_dispatch(registry: &ImplementRegistry) -> vole_vir::VirImplementDispatch {
    use crate::implement_registry::ImplTypeId;
    use vole_vir::{
        VirExternalFuncInfo, VirFuncSignature, VirImplementDispatch, VirMethodImplInfo,
    };

    let mut dispatch = VirImplementDispatch::new();

    for (name, info) in registry.external_func_entries() {
        dispatch.insert_external_func(
            name.to_string(),
            VirExternalFuncInfo {
                module_path: info.module_path,
                native_name: info.native_name,
            },
        );
    }

    for (name, info) in registry.generic_external_entries() {
        dispatch.insert_generic_external(name.to_string(), convert_generic_info(info));
    }

    for (key, info) in registry.generic_external_method_entries() {
        dispatch.insert_generic_external_method(
            key.type_def_id,
            key.method_name,
            convert_generic_info(info),
        );
    }

    for (key, method_impl) in registry.method_entries() {
        let type_name_id = ImplTypeId::name_id(key.type_id);
        dispatch.insert_method(
            type_name_id,
            key.method_name,
            VirMethodImplInfo {
                func_sig: VirFuncSignature {
                    is_closure: method_impl.func_type.is_closure,
                    params: method_impl.func_type.params_id.to_vec(),
                    return_type: method_impl.func_type.return_type_id,
                },
                external_info: method_impl.external_info.map(|ei| VirExternalFuncInfo {
                    module_path: ei.module_path,
                    native_name: ei.native_name,
                }),
            },
        );
    }

    dispatch
}

/// Convert a sema `GenericExternalInfo` to VIR.
fn convert_generic_info(
    info: &crate::implement_registry::GenericExternalInfo,
) -> vole_vir::VirGenericExternalInfo {
    use vole_vir::{VirGenericExternalInfo, VirTypeMappingEntry, VirTypeMappingKind};

    VirGenericExternalInfo {
        module_path: info.module_path,
        type_mappings: info
            .type_mappings
            .iter()
            .map(|entry| VirTypeMappingEntry {
                kind: match &entry.kind {
                    crate::implement_registry::TypeMappingKind::Exact(type_id) => {
                        VirTypeMappingKind::Exact(*type_id)
                    }
                    crate::implement_registry::TypeMappingKind::Default => {
                        VirTypeMappingKind::Default
                    }
                },
                intrinsic_key: entry.intrinsic_key.clone(),
            })
            .collect(),
    }
}
