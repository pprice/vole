// lowering/facade.rs
//
// VIR lowering orchestration — split into module-only and file-specific
// phases.  The module phase runs passes that depend only on imported modules
// and shared entity state; the file phase runs per-compilation passes that
// depend on the specific file being compiled.
//
// `lower_vir_program` is the single entry point: it calls `lower_module_vir`
// then `lower_file_vir` in sequence, with no behavior change vs the original
// monolithic function.

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
use super::test_bodies::lower_test_bodies;
use super::test_scoped_type_methods::lower_test_scoped_type_methods;
use super::type_method_monomorph::{
    MethodMonomorphLoweringCtx, MethodMonomorphLoweringWork,
    lower_type_method_monomorphized_instances,
};
use super::type_methods::{lower_module_type_methods, lower_top_level_type_methods};
use super::vir_monomorph::{
    build_generic_vir_storage, run_early_vir_monomorphize, run_vir_monomorphize,
};
use crate::LoweringEntityLookup;
use crate::TypeArena;
use crate::implement_registry::ImplementRegistry;
use crate::vir_lower::type_translate::sweep_unmapped_type_ids;
use vole_frontend::{Interner, Program};
use vole_identity::{FunctionId, MethodId, ModuleId, NameId, NameTable, Span};
use vole_vir::implement_dispatch::VirImplementDispatch;
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirFunction, VirProgram};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub struct LowerVirProgramArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a E,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a crate::NodeMap,
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
        module_programs,
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

    // Phase M: module-only passes (cacheable across test file compilations).
    //
    // These passes depend only on imported modules and shared entity state.
    // They do NOT touch the VirTypeTable, so they can run before function
    // lowering without affecting type interning order.
    let module_result = lower_module_vir(LowerModuleVirArgs {
        entities,
        type_arena,
        module_programs,
        implements,
    });

    // Phase F: file-specific passes (and type-table-dependent module passes).
    lower_file_vir(LowerFileVirArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        tests_virtual_modules,
        module_programs: module_result.module_programs,
        module_id,
        modules_with_errors,
        generic_vir_functions,
        type_table: &mut type_table,
        module_vir: module_result.output,
    })
}

// ---------------------------------------------------------------------------
// Module VIR output: all results from module-only (cacheable) passes
// ---------------------------------------------------------------------------

/// Output from module-only VIR lowering passes.
///
/// Contains VIR data produced by passes that only depend on imported modules
/// and shared entity state (not on the specific file being compiled, and not
/// on VirTypeTable ordering).  A future caching layer (vol-fe6d) can store
/// and reuse `ModuleVirOutput` across test file compilations.
///
/// Passes that depend on VirTypeTable (global inits, module bindings, default
/// inits, entity metadata, monomorph info) remain in the file phase to
/// preserve exact type interning order.  They are logically module-only and
/// will move here once the caching layer pre-populates the type table.
pub struct ModuleVirOutput {
    /// Implement-dispatch metadata from the implement registry.
    pub implement_dispatch: VirImplementDispatch,
    /// Per-module compile-time constant values.
    pub module_constants: FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>,
    /// Module type exports.
    pub module_exports:
        FxHashMap<vole_identity::TypeId, (ModuleId, Vec<(NameId, vole_identity::TypeId)>)>,
}

// ---------------------------------------------------------------------------
// Module VIR lowering args and result
// ---------------------------------------------------------------------------

/// Arguments for the module-only VIR lowering pass.
pub struct LowerModuleVirArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    pub entities: &'a E,
    pub type_arena: &'a TypeArena,
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    pub implements: &'a ImplementRegistry,
}

/// Result of the module-only VIR lowering pass, including the module_programs
/// that file passes still need.
pub struct LowerModuleVirResult {
    pub output: ModuleVirOutput,
    /// Returned so that file passes (and mixed passes) can still use them.
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
}

// ---------------------------------------------------------------------------
// File VIR lowering args
// ---------------------------------------------------------------------------

/// Arguments for the file-specific VIR lowering pass.
pub struct LowerFileVirArgs<'a, E>
where
    E: LoweringEntityLookup,
{
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub names: &'a NameTable,
    pub entities: &'a E,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a crate::NodeMap,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    pub module_id: ModuleId,
    pub modules_with_errors: &'a HashSet<String>,
    pub generic_vir_functions: Vec<(NameId, VirFunction)>,
    pub type_table: &'a mut VirTypeTable,
    pub module_vir: ModuleVirOutput,
}

// ---------------------------------------------------------------------------
// Phase M: module-only passes
// ---------------------------------------------------------------------------

/// Run module-only VIR lowering passes.
///
/// These passes depend only on imported modules and shared entity state, not
/// on the specific file being compiled.  Crucially, they do NOT use the
/// VirTypeTable, so they can safely run before function lowering without
/// affecting type interning order.
///
/// A future caching layer (vol-fe6d) can store and reuse `ModuleVirOutput`
/// across test file compilations.  Type-table-dependent module passes
/// (global inits, defaults, entity metadata, monomorph info) will move here
/// once the cache pre-populates the type table.
fn lower_module_vir<E>(args: LowerModuleVirArgs<'_, E>) -> LowerModuleVirResult
where
    E: LoweringEntityLookup,
{
    let LowerModuleVirArgs {
        entities: _,
        type_arena,
        module_programs,
        implements,
    } = args;

    // Build implement-dispatch metadata (reads ImplementRegistry only).
    let implement_dispatch = build_implement_dispatch(implements);

    // Collect module metadata: constants and exports (reads TypeArena only).
    let (module_constants, module_exports) = collect_module_metadata(type_arena);

    LowerModuleVirResult {
        output: ModuleVirOutput {
            implement_dispatch,
            module_constants,
            module_exports,
        },
        module_programs,
    }
}

// ---------------------------------------------------------------------------
// Phase F: file-specific passes (+ type-table-dependent module passes)
// ---------------------------------------------------------------------------

/// Run file-specific VIR lowering passes and assemble the final VirProgram.
///
/// Includes both file-specific passes (top-level functions, test bodies, etc.)
/// and type-table-dependent module passes (module global inits, module
/// defaults, entity metadata, monomorph info) that must run after function
/// lowering to preserve type interning order.
fn lower_file_vir<E>(args: LowerFileVirArgs<'_, E>) -> LowerVirProgramOutput
where
    E: LoweringEntityLookup,
{
    let LowerFileVirArgs {
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
        type_table,
        module_vir,
    } = args;

    // -----------------------------------------------------------------------
    // Function lowering (file + module, original interleaved order)
    // -----------------------------------------------------------------------

    let mut vir_functions = lower_top_level_functions(LowerTopLevelFunctionsArgs {
        program,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        type_table,
    });
    lower_module_functions(LowerModuleFunctionsArgs {
        module_programs: &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions: &mut vir_functions,
        type_table,
    });

    // -----------------------------------------------------------------------
    // Monomorphization (mixed pass)
    // -----------------------------------------------------------------------

    let (generic_vir_functions, generic_vir_map) = build_generic_vir_storage(generic_vir_functions);
    let vir_handled_function_ids = run_early_vir_monomorphize(
        &mut vir_functions,
        &generic_vir_functions,
        &generic_vir_map,
        type_table,
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
        type_table,
        vir_handled_function_ids: &vir_handled_function_ids,
    });

    // -----------------------------------------------------------------------
    // Type methods and implement-block methods (file + module)
    // -----------------------------------------------------------------------

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
        type_table,
    );
    lower_module_type_methods(
        &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        &mut vir_functions,
        type_table,
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
        type_table,
    });
    lower_module_implement_block_methods(LowerModuleImplementBlockMethodsArgs {
        module_programs: &mut module_programs,
        names,
        entities,
        type_arena,
        node_map,
        modules_with_errors,
        vir_functions: &mut vir_functions,
        type_table,
    });

    // -----------------------------------------------------------------------
    // Test-scoped type methods and method monomorphization
    // -----------------------------------------------------------------------

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
        type_table,
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
        type_table,
    };
    lower_type_method_monomorphized_instances(&mut method_monomorph_work, &method_monomorph_ctx);

    // -----------------------------------------------------------------------
    // Lookup maps
    // -----------------------------------------------------------------------

    let vir_monomorph_map = build_vir_monomorph_map(&vir_functions);
    let vir_function_map = build_vir_function_map(&vir_functions);
    let vir_method_map = build_vir_method_map(&vir_functions);

    // -----------------------------------------------------------------------
    // Test bodies, global inits, module bindings (file + module)
    // -----------------------------------------------------------------------

    let vir_tests = lower_test_bodies(
        program, node_map, interner, type_arena, entities, names, type_table,
    );
    let vir_global_inits = lower_global_inits(
        program, interner, node_map, type_arena, entities, names, type_table,
    );
    // Module global inits (type-table-dependent, logically module-only).
    let module_vir_global_inits = lower_module_global_inits(
        &mut module_programs,
        names,
        node_map,
        type_arena,
        entities,
        modules_with_errors,
        type_table,
    );
    let vir_module_bindings =
        lower_module_bindings(program, node_map, type_arena, names, interner, type_table);
    // Module-level module bindings (type-table-dependent, logically module-only).
    let vir_module_module_bindings = lower_module_module_bindings(
        &mut module_programs,
        names,
        node_map,
        type_arena,
        modules_with_errors,
        type_table,
    );

    // -----------------------------------------------------------------------
    // Default inits (file + module)
    // -----------------------------------------------------------------------

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
            type_table,
        });
    // Module function defaults (type-table-dependent, logically module-only).
    let module_vir_function_default_inits =
        lower_module_function_default_inits(LowerModuleFunctionDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table,
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
        type_table,
    });
    // Module method defaults (type-table-dependent, logically module-only).
    let module_vir_method_default_inits =
        lower_module_method_default_inits(LowerModuleMethodDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table,
        });
    vir_method_default_inits.extend(module_vir_method_default_inits);

    // Lambda default inits (mixed pass).
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
        type_table,
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
        type_table,
    });
    // Module field defaults (type-table-dependent, logically module-only).
    let module_vir_field_default_inits =
        lower_module_field_default_inits(LowerModuleFieldDefaultInitsArgs {
            module_programs: &mut module_programs,
            names,
            entities,
            node_map,
            type_arena,
            modules_with_errors,
            type_table,
        });
    vir_field_default_inits.extend(module_vir_field_default_inits);

    // -----------------------------------------------------------------------
    // Entity metadata and monomorph info (type-table-dependent, logically
    // module-only — will move to Phase M once caching pre-populates the
    // type table)
    // -----------------------------------------------------------------------

    let monomorph_info = populate_monomorph_info(entities, type_arena, type_table);
    let vir_annotation_inits = lower_annotation_inits(entities, interner, names);
    let mut entity_metadata =
        build_entity_metadata(entities, type_arena, type_table, interner, names);
    // Populate implement block entries (mixed pass: file + module portions).
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

    // Collect module interners from module_programs for VirProgram.
    let module_interners: FxHashMap<String, Rc<Interner>> = module_programs
        .iter()
        .map(|(path, (_program, interner))| (path.clone(), Rc::clone(interner)))
        .collect();

    // -----------------------------------------------------------------------
    // Assemble the final VirProgram
    // -----------------------------------------------------------------------

    let mut vir_program = VirProgram {
        type_table: std::mem::take(type_table),
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
        module_constants: module_vir.module_constants,
        module_exports: module_vir.module_exports,
        vir_monomorph_base: usize::MAX,
        entity_metadata,
        implement_dispatch: module_vir.implement_dispatch,
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
    // that were not encountered during on-demand lowering.
    sweep_unmapped_type_ids(&mut vir_program.type_table, type_arena);

    LowerVirProgramOutput { vir_program }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Collect module metadata (constants and exports) from the type arena for
/// codegen to use without direct arena access.
type ModuleConstants = FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>;
type ModuleExports =
    FxHashMap<vole_identity::TypeId, (ModuleId, Vec<(NameId, vole_identity::TypeId)>)>;

fn collect_module_metadata(type_arena: &TypeArena) -> (ModuleConstants, ModuleExports) {
    let mut constants = FxHashMap::default();
    let mut exports = FxHashMap::default();

    for (module_id, meta) in type_arena.all_module_metadata() {
        for (name_id, value) in &meta.constants {
            constants.insert((*module_id, *name_id), value.clone());
        }
    }

    for (type_id, module_info) in type_arena.all_module_types() {
        let export_vec: Vec<(NameId, vole_identity::TypeId)> =
            module_info.exports.iter().map(|&(n, t)| (n, t)).collect();
        exports.insert(type_id, (module_info.module_id, export_vec));
    }

    (constants, exports)
}

fn build_vir_monomorph_map(vir_functions: &[VirFunction]) -> FxHashMap<NameId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(name_id) = vf.mangled_name_id {
            map.insert(name_id, idx);
        }
    }
    map
}

fn build_vir_function_map(vir_functions: &[VirFunction]) -> FxHashMap<FunctionId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if vf.mangled_name_id.is_none() && vf.method_id.is_none() {
            map.insert(vf.id, idx);
        }
    }
    map
}

fn build_vir_method_map(vir_functions: &[VirFunction]) -> FxHashMap<MethodId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(method_id) = vf.method_id {
            map.insert(method_id, idx);
        }
    }
    map
}

/// Build VIR implement-dispatch metadata from sema's `ImplementRegistry`.
fn build_implement_dispatch(registry: &ImplementRegistry) -> VirImplementDispatch {
    use crate::implement_registry::ImplTypeId;
    use vole_vir::{VirExternalFuncInfo, VirFuncSignature, VirMethodImplInfo};

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
