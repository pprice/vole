use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::analyzed::{
    build_generic_vir_storage_remapped, build_vir_function_map, build_vir_method_map,
    build_vir_monomorph_map, lower_test_bodies, run_early_vir_monomorphize, run_vir_monomorphize,
};
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
use crate::analyzed_lowering_lookup::LoweringEntityLookup;
use vole_frontend::{Interner, Program};
use vole_identity::{ModuleId, NameId, NameTable, Span};
use vole_sema::{NodeMap, TypeArena};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirFunction, VirProgram};

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
        vir_monomorph_base: usize::MAX,
    };
    run_vir_monomorphize(&mut vir_program);

    LowerVirProgramOutput {
        module_programs,
        vir_program,
    }
}
