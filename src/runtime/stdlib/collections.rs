// src/runtime/stdlib/collections.rs
//! Native module for Map<K,V> and Set<T> collections.

use crate::runtime::collections;
use crate::runtime::native_registry::{NativeModule, NativeSignature, NativeType};

/// Create the std:collections native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // ==========================================================================
    // Map<K, V> functions
    // ==========================================================================

    // map_new: () -> Map
    m.register(
        "map_new",
        collections::map_new as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::I64, // Pointer to map
        },
    );

    // map_with_capacity: (i64) -> Map
    m.register(
        "map_with_capacity",
        collections::map_with_capacity as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // map_get: (Map, key, key_hash) -> value
    m.register(
        "map_get",
        collections::map_get as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // map_has: (Map, key, key_hash) -> bool
    m.register(
        "map_has",
        collections::map_has as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // map_set: (Map, key, key_hash, value) -> void
    m.register(
        "map_set",
        collections::map_set as *const u8,
        NativeSignature {
            params: vec![
                NativeType::I64,
                NativeType::I64,
                NativeType::I64,
                NativeType::I64,
            ],
            return_type: NativeType::Nil,
        },
    );

    // map_remove: (Map, key, key_hash) -> value
    m.register(
        "map_remove",
        collections::map_remove as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // map_contains_key: (Map, key, key_hash) -> bool
    m.register(
        "map_contains_key",
        collections::map_contains_key as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // map_len: (Map) -> i64
    m.register(
        "map_len",
        collections::map_len as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // map_clear: (Map) -> void
    m.register(
        "map_clear",
        collections::map_clear as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // map_keys_iter: (Map) -> Iterator
    m.register(
        "map_keys_iter",
        collections::map_keys_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // map_values_iter: (Map) -> Iterator
    m.register(
        "map_values_iter",
        collections::map_values_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // map_entries_iter: (Map) -> Iterator
    m.register(
        "map_entries_iter",
        collections::map_entries_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // ==========================================================================
    // Set<T> functions
    // ==========================================================================

    // set_new: () -> Set
    m.register(
        "set_new",
        collections::set_new as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::I64,
        },
    );

    // set_with_capacity: (i64) -> Set
    m.register(
        "set_with_capacity",
        collections::set_with_capacity as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_add: (Set, value, hash) -> bool
    m.register(
        "set_add",
        collections::set_add as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // set_remove: (Set, value, hash) -> bool
    m.register(
        "set_remove",
        collections::set_remove as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // set_contains: (Set, value, hash) -> bool
    m.register(
        "set_contains",
        collections::set_contains as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // set_len: (Set) -> i64
    m.register(
        "set_len",
        collections::set_len as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_clear: (Set) -> void
    m.register(
        "set_clear",
        collections::set_clear as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // set_iter: (Set) -> Iterator
    m.register(
        "set_iter",
        collections::set_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_union: (Set, Set) -> Set
    m.register(
        "set_union",
        collections::set_union as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_intersection: (Set, Set) -> Set
    m.register(
        "set_intersection",
        collections::set_intersection as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_difference: (Set, Set) -> Set
    m.register(
        "set_difference",
        collections::set_difference as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_symmetric_difference: (Set, Set) -> Set
    m.register(
        "set_symmetric_difference",
        collections::set_symmetric_difference as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set_is_subset: (Set, Set) -> bool
    m.register(
        "set_is_subset",
        collections::set_is_subset as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // set_is_superset: (Set, Set) -> bool
    m.register(
        "set_is_superset",
        collections::set_is_superset as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // set_is_disjoint: (Set, Set) -> bool
    m.register(
        "set_is_disjoint",
        collections::set_is_disjoint as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    m
}
