use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::analyzed_lower_annotation_inits::lower_annotation_inits;
use crate::analyzed_lower_entity_metadata::build_entity_metadata;
use crate::analyzed_lower_field_default_inits::{
    LowerFieldDefaultInitsArgs, LowerModuleFieldDefaultInitsArgs, lower_field_default_inits,
    lower_module_field_default_inits,
};
use crate::analyzed_lower_function_default_inits::{
    LowerFunctionDefaultInitsArgs, LowerModuleFunctionDefaultInitsArgs,
    lower_function_default_inits, lower_module_function_default_inits,
};
use crate::analyzed_lower_functions::{
    LowerModuleFunctionsArgs, LowerTopLevelFunctionsArgs, lower_module_functions,
    lower_top_level_functions,
};
use crate::analyzed_lower_global_inits::{lower_global_inits, lower_module_global_inits};
use crate::analyzed_lower_implement_blocks::{
    LowerImplementBlockMethodsArgs, LowerModuleImplementBlockMethodsArgs,
    lower_implement_block_methods, lower_module_implement_block_methods,
};
use crate::analyzed_lower_lambda_default_inits::{
    LowerLambdaDefaultInitsArgs, lower_lambda_default_inits,
};
use crate::analyzed_lower_method_default_inits::{
    LowerMethodDefaultInitsArgs, LowerModuleMethodDefaultInitsArgs, lower_method_default_inits,
    lower_module_method_default_inits,
};
use crate::analyzed_lower_monomorph_functions::{
    LowerMonomorphizedInstancesArgs, build_generic_func_map, lower_monomorphized_instances,
};
use crate::analyzed_lower_test_scoped_type_methods::lower_test_scoped_type_methods;
use crate::analyzed_lower_type_method_monomorph::{
    MethodMonomorphLoweringCtx, MethodMonomorphLoweringWork,
    lower_type_method_monomorphized_instances,
};
use crate::analyzed_lower_type_methods::{lower_module_type_methods, lower_top_level_type_methods};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{FunctionId, MethodId, ModuleId, NameId, NameTable, Span};
use vole_sema::LoweringEntityLookup;
use vole_sema::vir_lower::{lower_stmts, lower_test_body};
use vole_sema::{NodeMap, TypeArena};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirFunction, VirProgram, VirTest};

pub(crate) struct LowerVirProgramArgs<'a, E>
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
    pub generic_vir_type_table: VirTypeTable,
}

pub(crate) struct LowerVirProgramOutput {
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    pub vir_program: VirProgram,
}

/// Run the codegen-side VIR lowering orchestration and return assembled outputs.
pub(crate) fn lower_vir_program<E>(args: LowerVirProgramArgs<'_, E>) -> LowerVirProgramOutput
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
        generic_vir_type_table,
    } = args;

    let mut type_table = VirTypeTable::new();
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

    let generic_type_remap = type_table.merge_from(&generic_vir_type_table);
    let (generic_vir_functions, generic_vir_map) =
        build_generic_vir_storage_remapped(generic_vir_functions, &generic_type_remap);

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

    let vir_annotation_inits = lower_annotation_inits(entities, interner, names);
    let entity_metadata = build_entity_metadata(entities, type_arena, &type_table);
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
        vir_monomorph_base: usize::MAX,
        entity_metadata,
    };
    run_vir_monomorphize(&mut vir_program);

    LowerVirProgramOutput {
        module_programs,
        vir_program,
    }
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
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
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

/// Build generic VIR storage with VirTypeId remapping.
///
/// Like `build_generic_vir_storage` but applies a VirTypeId remapping to
/// each generic function template.  This is needed because generic templates
/// are lowered with their own type table (in sema Pass 2a) and their
/// VirTypeIds must be translated to the program's main type table.
fn build_generic_vir_storage_remapped(
    pairs: Vec<(NameId, VirFunction)>,
    type_remap: &FxHashMap<vole_identity::VirTypeId, vole_identity::VirTypeId>,
) -> (Vec<VirFunction>, FxHashMap<NameId, usize>) {
    let ctx = vole_vir::RewriteCtx::new(type_remap.clone());
    let mut map = FxHashMap::default();
    let mut functions = Vec::with_capacity(pairs.len());
    for (name_id, vir) in pairs {
        let idx = functions.len();
        map.insert(name_id, idx);
        functions.push(vole_vir::rewrite_function(&vir, &ctx));
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
    use vole_sema::vir_lower::type_translate::translate_type_id;

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
        vir_monomorph_base: usize::MAX,
        entity_metadata: vole_vir::VirEntityMetadata::new(),
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
