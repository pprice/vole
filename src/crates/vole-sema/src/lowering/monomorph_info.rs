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
use vole_vir::remap::{
    remap_class_method_monomorph_info, remap_class_method_monomorph_key, remap_monomorph_key,
    remap_static_method_monomorph_info, remap_static_method_monomorph_key,
    remap_vir_monomorph_info,
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

/// Clone a `PopulatedMonomorphInfo` with all `VirTypeId` fields remapped.
///
/// Walks every monomorph info entry and key, replacing each `VirTypeId`
/// according to the provided mapping. Unmapped IDs are left unchanged
/// (identity fallback). Non-`VirTypeId` fields (NameIds, sema TypeIds,
/// instance_ids, FunctionTypes, etc.) are cloned verbatim.
pub fn remap_monomorph_info(
    info: &PopulatedMonomorphInfo,
    mapping: &FxHashMap<VirTypeId, VirTypeId>,
) -> PopulatedMonomorphInfo {
    // Free monomorphs: values contain VirTypeId fields, keys are NameId (no remap needed).
    let free_monomorphs = info
        .free_monomorphs
        .iter()
        .map(|(&name, entry)| (name, remap_vir_monomorph_info(entry, mapping)))
        .collect();

    // Free monomorphs by key: keys contain VirTypeId type_keys, values are NameId.
    let free_monomorphs_by_key = info
        .free_monomorphs_by_key
        .iter()
        .map(|(key, &name)| (remap_monomorph_key(key, mapping), name))
        .collect();

    // Class method monomorphs: both keys and values contain VirTypeId fields.
    let class_method_monomorphs = info
        .class_method_monomorphs
        .iter()
        .map(|(key, entry)| {
            (
                remap_class_method_monomorph_key(key, mapping),
                remap_class_method_monomorph_info(entry, mapping),
            )
        })
        .collect();

    // Static method monomorphs: both keys and values contain VirTypeId fields.
    let static_method_monomorphs = info
        .static_method_monomorphs
        .iter()
        .map(|(key, entry)| {
            (
                remap_static_method_monomorph_key(key, mapping),
                remap_static_method_monomorph_info(entry, mapping),
            )
        })
        .collect();

    PopulatedMonomorphInfo {
        free_monomorphs,
        free_monomorphs_by_key,
        class_method_monomorphs,
        static_method_monomorphs,
    }
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

// ============================================================================
// Unit tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use vole_identity::{FunctionType, TypeId, TypeIdVec};

    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    fn test_mapping() -> FxHashMap<VirTypeId, VirTypeId> {
        let mut m = FxHashMap::default();
        m.insert(VirTypeId::I64, VirTypeId::STRING);
        m.insert(VirTypeId::STRING, VirTypeId::I64);
        m.insert(VirTypeId::BOOL, VirTypeId::F64);
        m
    }

    fn dummy_func_type() -> FunctionType {
        FunctionType {
            is_closure: false,
            params_id: TypeIdVec::new(),
            return_type_id: TypeId::from_raw(0),
        }
    }

    #[test]
    fn remap_monomorph_info_free_monomorphs() {
        let mut free = FxHashMap::default();
        free.insert(
            name(1),
            VirMonomorphInfo {
                original_name: name(10),
                mangled_name: name(1),
                instance_id: 0,
                func_type: dummy_func_type(),
                vir_func_type: VirTypeId::I64,
                substitutions: FxHashMap::default(),
                vir_substitutions: [(name(20), VirTypeId::BOOL)].into_iter().collect(),
            },
        );

        let info = PopulatedMonomorphInfo {
            free_monomorphs: free,
            free_monomorphs_by_key: FxHashMap::default(),
            class_method_monomorphs: FxHashMap::default(),
            static_method_monomorphs: FxHashMap::default(),
        };

        let remapped = remap_monomorph_info(&info, &test_mapping());
        let entry = &remapped.free_monomorphs[&name(1)];
        assert_eq!(entry.vir_func_type, VirTypeId::STRING);
        assert_eq!(entry.vir_substitutions[&name(20)], VirTypeId::F64);
        // sema fields unchanged
        assert_eq!(entry.original_name, name(10));
    }

    #[test]
    fn remap_monomorph_info_free_by_key() {
        let key = MonomorphKey::new(name(1), vec![VirTypeId::I64, VirTypeId::BOOL]);
        let mut by_key = FxHashMap::default();
        by_key.insert(key, name(100));

        let info = PopulatedMonomorphInfo {
            free_monomorphs: FxHashMap::default(),
            free_monomorphs_by_key: by_key,
            class_method_monomorphs: FxHashMap::default(),
            static_method_monomorphs: FxHashMap::default(),
        };

        let remapped = remap_monomorph_info(&info, &test_mapping());
        let expected_key = MonomorphKey::new(name(1), vec![VirTypeId::STRING, VirTypeId::F64]);
        assert_eq!(remapped.free_monomorphs_by_key[&expected_key], name(100));
        assert_eq!(remapped.free_monomorphs_by_key.len(), 1);
    }

    #[test]
    fn remap_monomorph_info_class_methods() {
        let key = ClassMethodMonomorphKey::new(name(1), name(2), vec![VirTypeId::I64]);
        let mut class = FxHashMap::default();
        class.insert(
            key,
            VirClassMethodMonomorphInfo {
                class_name: name(1),
                method_name: name(2),
                mangled_name: name(3),
                instance_id: 0,
                func_type: dummy_func_type(),
                vir_func_type: VirTypeId::BOOL,
                substitutions: FxHashMap::default(),
                vir_substitutions: FxHashMap::default(),
                external_info: None,
                self_type: TypeId::from_raw(0),
                vir_self_type: VirTypeId::STRING,
            },
        );

        let info = PopulatedMonomorphInfo {
            free_monomorphs: FxHashMap::default(),
            free_monomorphs_by_key: FxHashMap::default(),
            class_method_monomorphs: class,
            static_method_monomorphs: FxHashMap::default(),
        };

        let remapped = remap_monomorph_info(&info, &test_mapping());
        let expected_key = ClassMethodMonomorphKey::new(name(1), name(2), vec![VirTypeId::STRING]);
        let entry = &remapped.class_method_monomorphs[&expected_key];
        assert_eq!(entry.vir_func_type, VirTypeId::F64);
        assert_eq!(entry.vir_self_type, VirTypeId::I64);
    }

    #[test]
    fn remap_monomorph_info_static_methods() {
        let key = StaticMethodMonomorphKey::new(
            name(1),
            name(2),
            vec![VirTypeId::STRING],
            vec![VirTypeId::BOOL],
        );
        let mut static_ = FxHashMap::default();
        static_.insert(
            key,
            VirStaticMethodMonomorphInfo {
                class_name: name(1),
                method_name: name(2),
                mangled_name: name(3),
                instance_id: 0,
                func_type: dummy_func_type(),
                vir_func_type: VirTypeId::I64,
                substitutions: FxHashMap::default(),
                vir_substitutions: [(name(30), VirTypeId::STRING)].into_iter().collect(),
            },
        );

        let info = PopulatedMonomorphInfo {
            free_monomorphs: FxHashMap::default(),
            free_monomorphs_by_key: FxHashMap::default(),
            class_method_monomorphs: FxHashMap::default(),
            static_method_monomorphs: static_,
        };

        let remapped = remap_monomorph_info(&info, &test_mapping());
        let expected_key = StaticMethodMonomorphKey::new(
            name(1),
            name(2),
            vec![VirTypeId::I64],
            vec![VirTypeId::F64],
        );
        let entry = &remapped.static_method_monomorphs[&expected_key];
        assert_eq!(entry.vir_func_type, VirTypeId::STRING);
        assert_eq!(entry.vir_substitutions[&name(30)], VirTypeId::I64);
    }

    #[test]
    fn remap_monomorph_info_empty_is_identity() {
        let info = PopulatedMonomorphInfo {
            free_monomorphs: FxHashMap::default(),
            free_monomorphs_by_key: FxHashMap::default(),
            class_method_monomorphs: FxHashMap::default(),
            static_method_monomorphs: FxHashMap::default(),
        };

        let empty: FxHashMap<VirTypeId, VirTypeId> = FxHashMap::default();
        let remapped = remap_monomorph_info(&info, &empty);
        assert!(remapped.free_monomorphs.is_empty());
        assert!(remapped.free_monomorphs_by_key.is_empty());
        assert!(remapped.class_method_monomorphs.is_empty());
        assert!(remapped.static_method_monomorphs.is_empty());
    }
}
