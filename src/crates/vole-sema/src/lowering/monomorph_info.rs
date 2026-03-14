// lowering/monomorph_info.rs
//
// Populates the VIR-native monomorph info maps on VirProgram from sema's
// monomorph caches during VIR lowering.
//
// Three maps are populated:
// - free_monomorphs (vol-3on3)
// - class_method_monomorphs (vol-40jn)
// - static_method_monomorphs (vol-bklt)

use rustc_hash::FxHashMap;
use vole_identity::{
    ClassMethodMonomorphKey, MonomorphKey, NameId, StaticMethodMonomorphKey, VirTypeId,
};

use crate::LoweringEntityLookup;
use crate::TypeArena;
use crate::generic::{
    ClassMethodMonomorphInstance, MonomorphInstance, StaticMethodMonomorphInstance,
};
use crate::vir_lower::type_translate::translate_type_id;
use vole_vir::VirExternalMethodInfo;
use vole_vir::monomorph::instance::{
    VirClassMethodMonomorphInfo, VirMonomorphInfo, VirStaticMethodMonomorphInfo,
};
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::VirType;

/// Populate all three VIR monomorph info maps from sema's monomorph caches.
///
/// Translates sema `MonomorphInstance`, `ClassMethodMonomorphInstance`, and
/// `StaticMethodMonomorphInstance` into their VIR-native counterparts,
/// converting `TypeId` fields to `VirTypeId` via the type table.
pub fn populate_monomorph_info(
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> PopulatedMonomorphInfo {
    let (free, free_by_key) = populate_free_monomorphs(entities, type_arena, type_table);
    let class = populate_class_method_monomorphs(entities, type_arena, type_table);
    let static_ = populate_static_method_monomorphs(entities, type_arena, type_table);

    PopulatedMonomorphInfo {
        free_monomorphs: free,
        free_monomorphs_by_key: free_by_key,
        class_method_monomorphs: class,
        static_method_monomorphs: static_,
    }
}

/// Output of the monomorph info population pass.
#[derive(Clone)]
pub struct PopulatedMonomorphInfo {
    pub free_monomorphs: FxHashMap<NameId, VirMonomorphInfo>,
    pub free_monomorphs_by_key: FxHashMap<MonomorphKey, NameId>,
    pub class_method_monomorphs: FxHashMap<ClassMethodMonomorphKey, VirClassMethodMonomorphInfo>,
    pub static_method_monomorphs: FxHashMap<StaticMethodMonomorphKey, VirStaticMethodMonomorphInfo>,
}

// ============================================================================
// Free function monomorphs
// ============================================================================

fn populate_free_monomorphs(
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> (
    FxHashMap<NameId, VirMonomorphInfo>,
    FxHashMap<MonomorphKey, NameId>,
) {
    let keyed_instances = entities.monomorph_keyed_instances();
    let mut map = FxHashMap::default();
    let mut by_key = FxHashMap::default();
    for (key, instance) in keyed_instances {
        let info = translate_free_monomorph(&instance, type_arena, type_table);
        let translated_key = translate_monomorph_key(&key, type_arena, type_table);
        by_key.insert(translated_key, instance.mangled_name);
        map.insert(instance.mangled_name, info);
    }
    (map, by_key)
}

fn translate_free_monomorph(
    instance: &MonomorphInstance,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> VirMonomorphInfo {
    let vir_func_type = translate_function_type(
        &instance.func_type.params_id,
        instance.func_type.return_type_id,
        type_arena,
        type_table,
    );
    let vir_substitutions =
        translate_substitutions(&instance.substitutions, type_arena, type_table);

    VirMonomorphInfo {
        original_name: instance.original_name,
        mangled_name: instance.mangled_name,
        instance_id: instance.instance_id,
        func_type: instance.func_type.clone(),
        vir_func_type,
        substitutions: instance.substitutions.clone(),
        vir_substitutions,
    }
}

// ============================================================================
// Class method monomorphs
// ============================================================================

fn populate_class_method_monomorphs(
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> FxHashMap<ClassMethodMonomorphKey, VirClassMethodMonomorphInfo> {
    let keyed_instances = entities.class_method_monomorph_keyed_instances();
    let mut map = FxHashMap::default();
    for (key, instance) in keyed_instances {
        let info = translate_class_method_monomorph(&instance, type_arena, type_table);
        let translated_key = translate_class_method_monomorph_key(&key, type_arena, type_table);
        map.insert(translated_key, info);
    }
    map
}

fn translate_class_method_monomorph(
    instance: &ClassMethodMonomorphInstance,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> VirClassMethodMonomorphInfo {
    let vir_func_type = translate_function_type(
        &instance.func_type.params_id,
        instance.func_type.return_type_id,
        type_arena,
        type_table,
    );
    let vir_substitutions =
        translate_substitutions(&instance.substitutions, type_arena, type_table);
    let vir_self_type = translate_type_id(type_table, instance.self_type, type_arena);

    VirClassMethodMonomorphInfo {
        class_name: instance.class_name,
        method_name: instance.method_name,
        mangled_name: instance.mangled_name,
        instance_id: instance.instance_id,
        func_type: instance.func_type.clone(),
        vir_func_type,
        substitutions: instance.substitutions.clone(),
        vir_substitutions,
        external_info: instance.external_info.map(|ei| VirExternalMethodInfo {
            module_path: ei.module_path,
            native_name: ei.native_name,
        }),
        self_type: instance.self_type,
        vir_self_type,
    }
}

// ============================================================================
// Static method monomorphs
// ============================================================================

fn populate_static_method_monomorphs(
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> FxHashMap<StaticMethodMonomorphKey, VirStaticMethodMonomorphInfo> {
    let keyed_instances = entities.static_method_monomorph_keyed_instances();
    let mut map = FxHashMap::default();
    for (key, instance) in keyed_instances {
        let info = translate_static_method_monomorph(&instance, type_arena, type_table);
        let translated_key = translate_static_method_monomorph_key(&key, type_arena, type_table);
        map.insert(translated_key, info);
    }
    map
}

fn translate_static_method_monomorph(
    instance: &StaticMethodMonomorphInstance,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> VirStaticMethodMonomorphInfo {
    let vir_func_type = translate_function_type(
        &instance.func_type.params_id,
        instance.func_type.return_type_id,
        type_arena,
        type_table,
    );
    let vir_substitutions =
        translate_substitutions(&instance.substitutions, type_arena, type_table);

    VirStaticMethodMonomorphInfo {
        class_name: instance.class_name,
        method_name: instance.method_name,
        mangled_name: instance.mangled_name,
        instance_id: instance.instance_id,
        func_type: instance.func_type.clone(),
        vir_func_type,
        substitutions: instance.substitutions.clone(),
        vir_substitutions,
    }
}

// ============================================================================
// Key translation helpers
// ============================================================================

/// Translate a `MonomorphKey`'s raw-preserved `VirTypeId` type_keys into
/// proper VirTypeTable indices.
fn translate_monomorph_key(
    key: &MonomorphKey,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> MonomorphKey {
    MonomorphKey::new(
        key.func_name,
        translate_vir_type_keys(&key.type_keys, type_arena, type_table),
    )
}

/// Translate a `ClassMethodMonomorphKey`'s raw-preserved type_keys.
fn translate_class_method_monomorph_key(
    key: &ClassMethodMonomorphKey,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> ClassMethodMonomorphKey {
    ClassMethodMonomorphKey::new(
        key.class_name,
        key.method_name,
        translate_vir_type_keys(&key.type_keys, type_arena, type_table),
    )
}

/// Translate a `StaticMethodMonomorphKey`'s raw-preserved type_keys.
fn translate_static_method_monomorph_key(
    key: &StaticMethodMonomorphKey,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> StaticMethodMonomorphKey {
    StaticMethodMonomorphKey::new(
        key.class_name,
        key.method_name,
        translate_vir_type_keys(&key.class_type_keys, type_arena, type_table),
        translate_vir_type_keys(&key.method_type_keys, type_arena, type_table),
    )
}

/// Translate a slice of raw-preserved `VirTypeId`s (created via
/// `VirTypeId::from_type_id`) into proper VirTypeTable-indexed `VirTypeId`s.
fn translate_vir_type_keys(
    keys: &[VirTypeId],
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> Vec<VirTypeId> {
    keys.iter()
        .map(|&vir_ty| translate_type_id(type_table, vir_ty.to_type_id_raw(), type_arena))
        .collect()
}

// ============================================================================
// Shared helpers
// ============================================================================

/// Translate a sema `FunctionType`'s params and return type into a VIR
/// function `VirTypeId`.
///
/// Builds a `VirType::Function { params, ret }` and interns it. The layout
/// is `None` because function types are pointer-like and don't need
/// field-level layout information.
fn translate_function_type(
    params: &vole_identity::TypeIdVec,
    return_type: vole_identity::TypeId,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> VirTypeId {
    let vir_params: Vec<VirTypeId> = params
        .iter()
        .map(|&p| translate_type_id(type_table, p, type_arena))
        .collect();
    let vir_ret = translate_type_id(type_table, return_type, type_arena);
    let vir_type = VirType::Function {
        params: vir_params,
        ret: vir_ret,
    };
    type_table.intern(vir_type, None)
}

/// Translate a sema substitutions map from `TypeId` to `VirTypeId`.
fn translate_substitutions(
    subs: &FxHashMap<NameId, vole_identity::TypeId>,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> FxHashMap<NameId, VirTypeId> {
    subs.iter()
        .map(|(&name, &type_id)| {
            let vir_type_id = translate_type_id(type_table, type_id, type_arena);
            (name, vir_type_id)
        })
        .collect()
}
