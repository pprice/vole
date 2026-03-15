// substitute.rs
//
// Type substitution for VIR monomorphization. Given a source VirTypeTable with
// Param entries and a substitution map (NameId -> VirTypeId), produces a mapping
// from old VirTypeId to new VirTypeId with all Param entries replaced by
// concrete types.

use rustc_hash::FxHashMap;
use vole_identity::{NameId, VirTypeId};

use crate::type_table::VirTypeTable;
use crate::types::{StorageClass, VirPrimitiveKind, VirType, VirTypeLayout};

/// Substitution map from type parameter name to concrete type.
pub type TypeSubstitution = FxHashMap<NameId, VirTypeId>;

/// Apply type substitution to a `VirTypeTable`, returning a mapping from old
/// `VirTypeId` to new `VirTypeId`.
///
/// For each type in `source_table`:
/// - `Param { name }` entries are replaced with the concrete type from `substitution`.
/// - Compound types containing `VirTypeId` references are recursively substituted.
/// - Simple types (primitives, Void, etc.) are interned as-is into `target_table`.
///
/// Layouts are computed for newly created concrete types.
pub fn substitute_types(
    source_table: &VirTypeTable,
    target_table: &mut VirTypeTable,
    substitution: &TypeSubstitution,
) -> FxHashMap<VirTypeId, VirTypeId> {
    let mut mapping: FxHashMap<VirTypeId, VirTypeId> = FxHashMap::default();

    for i in 0..source_table.len() as u32 {
        let old_id = VirTypeId::from_raw(i);
        let new_id = substitute_one(
            old_id,
            source_table,
            target_table,
            substitution,
            &mut mapping,
        );
        mapping.insert(old_id, new_id);
    }

    mapping
}

/// Substitute a single type, using memoization to avoid reprocessing.
fn substitute_one(
    old_id: VirTypeId,
    source: &VirTypeTable,
    target: &mut VirTypeTable,
    subs: &TypeSubstitution,
    memo: &mut FxHashMap<VirTypeId, VirTypeId>,
) -> VirTypeId {
    if let Some(&already) = memo.get(&old_id) {
        return already;
    }

    let old_type = source.get(old_id);
    let new_id = match old_type {
        VirType::Param { name } => {
            if let Some(&concrete) = subs.get(name) {
                concrete
            } else {
                // Param not in substitution map -- keep as-is.
                target.intern(old_type.clone(), None)
            }
        }

        // Compound types: recursively substitute inner VirTypeIds.
        VirType::Array { elem } => {
            let new_elem = substitute_one(*elem, source, target, subs, memo);
            let ty = VirType::Array { elem: new_elem };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::FixedArray { elem, len } => {
            let new_elem = substitute_one(*elem, source, target, subs, memo);
            let ty = VirType::FixedArray {
                elem: new_elem,
                len: *len,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Tuple { elems } => {
            let new_elems = substitute_vec(elems, source, target, subs, memo);
            let ty = VirType::Tuple { elems: new_elems };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Union { variants } => {
            let mut new_variants = substitute_vec(variants, source, target, subs, memo);
            // Re-sort variants by union_sort_key (descending) to match sema's
            // canonical order.  After substitution, type parameters are replaced
            // with concrete types whose sort category may differ from the
            // parameter's original category.  Without re-sorting, the variant
            // order would reflect the generic template's order, causing tag
            // mismatches with unions constructed from sema's concrete ordering.
            new_variants.sort_by_key(|v| std::cmp::Reverse(target.union_sort_key(*v)));
            let ty = VirType::Union {
                variants: new_variants,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Optional { inner, .. } => {
            let new_inner = substitute_one(*inner, source, target, subs, memo);
            // Compute variant order using whichever table contains the
            // concrete inner type.  After substitution, new_inner may be a
            // source-table VirTypeId (direct Param substitution) or a
            // target-table VirTypeId (recursively interned compound type).
            let new_variants = if (new_inner.raw() as usize) < target.len() {
                target.compute_optional_variants(new_inner)
            } else {
                source.compute_optional_variants(new_inner)
            };
            let ty = VirType::Optional {
                inner: new_inner,
                variants: new_variants,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Fallible { success, errors } => {
            let new_success = substitute_one(*success, source, target, subs, memo);
            let new_errors = substitute_vec(errors, source, target, subs, memo);
            let ty = VirType::Fallible {
                success: new_success,
                errors: new_errors,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Function { params, ret } => {
            let new_params = substitute_vec(params, source, target, subs, memo);
            let new_ret = substitute_one(*ret, source, target, subs, memo);
            let ty = VirType::Function {
                params: new_params,
                ret: new_ret,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Class { def, type_args } => {
            let new_args = substitute_vec(type_args, source, target, subs, memo);
            let ty = VirType::Class {
                def: *def,
                type_args: new_args,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::Struct { def, type_args } => {
            let new_args = substitute_vec(type_args, source, target, subs, memo);
            let ty = VirType::Struct {
                def: *def,
                type_args: new_args,
            };
            let is_sentinel = source.is_sentinel(old_id);
            let layout = if is_sentinel {
                Some(sentinel_layout())
            } else {
                compute_layout(&ty, target)
            };
            let new_id = target.intern(ty, layout);
            if is_sentinel {
                target.mark_sentinel(new_id);
            }
            new_id
        }
        VirType::Interface { def, type_args } => {
            let new_args = substitute_vec(type_args, source, target, subs, memo);
            let ty = VirType::Interface {
                def: *def,
                type_args: new_args,
            };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }
        VirType::RuntimeIterator { elem } => {
            let new_elem = substitute_one(*elem, source, target, subs, memo);
            let ty = VirType::RuntimeIterator { elem: new_elem };
            let layout = compute_layout(&ty, target);
            target.intern(ty, layout)
        }

        // Leaf types: no VirTypeIds inside, intern as-is.
        VirType::Primitive(_)
        | VirType::Error { .. }
        | VirType::Void
        | VirType::Never
        | VirType::Range
        | VirType::MetaType
        | VirType::Unknown => {
            let layout = compute_layout(old_type, target);
            target.intern(old_type.clone(), layout)
        }
    };

    memo.insert(old_id, new_id);
    new_id
}

/// Substitute a vector of VirTypeIds.
fn substitute_vec(
    ids: &[VirTypeId],
    source: &VirTypeTable,
    target: &mut VirTypeTable,
    subs: &TypeSubstitution,
    memo: &mut FxHashMap<VirTypeId, VirTypeId>,
) -> Vec<VirTypeId> {
    ids.iter()
        .map(|id| substitute_one(*id, source, target, subs, memo))
        .collect()
}

// ---------------------------------------------------------------------------
// Layout computation from VirType (no sema/TypeArena dependency)
// ---------------------------------------------------------------------------

/// Compute the physical layout for a concrete VirType.
///
/// Returns `None` for `Param` types (still generic). All other types produce
/// a layout based on their structural category.
fn compute_layout(ty: &VirType, _table: &VirTypeTable) -> Option<VirTypeLayout> {
    match ty {
        VirType::Param { .. } => None,

        VirType::Primitive(kind) => Some(primitive_layout(*kind)),

        // RC heap-allocated types.
        VirType::Class { .. }
        | VirType::Array { .. }
        | VirType::FixedArray { .. }
        | VirType::RuntimeIterator { .. }
        | VirType::Interface { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Value-type struct: single word slot.
        VirType::Struct { .. } => Some(VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Word,
        }),

        // Error types are heap-allocated, RC.
        VirType::Error { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Tuples are heap-allocated, RC.
        VirType::Tuple { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Unions are heap-allocated, RC.
        VirType::Union { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Optional: heap-allocated, RC.
        VirType::Optional { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Fallible: heap-allocated, RC.
        VirType::Fallible { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Function (closure): heap-allocated, RC.
        VirType::Function { .. } => Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Zero-sized types.
        VirType::Void | VirType::Never => Some(VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 0,
            storage: StorageClass::Void,
        }),

        // Range: two i64 values (start + end), wide.
        VirType::Range => Some(VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: true,
            slot_count: 2,
            storage: StorageClass::Wide,
        }),

        // MetaType: heap pointer, not RC.
        VirType::MetaType => Some(VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),

        // Unknown: boxed TaggedValue, heap pointer.
        VirType::Unknown => Some(VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        }),
    }
}

/// Layout for a primitive scalar type.
fn primitive_layout(kind: VirPrimitiveKind) -> VirTypeLayout {
    match kind {
        VirPrimitiveKind::I8
        | VirPrimitiveKind::I16
        | VirPrimitiveKind::I32
        | VirPrimitiveKind::I64
        | VirPrimitiveKind::U8
        | VirPrimitiveKind::U16
        | VirPrimitiveKind::U32
        | VirPrimitiveKind::U64
        | VirPrimitiveKind::Bool => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Word,
        },

        VirPrimitiveKind::I128 | VirPrimitiveKind::F128 => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: true,
            slot_count: 2,
            storage: StorageClass::Wide,
        },

        VirPrimitiveKind::F32 | VirPrimitiveKind::F64 => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Float,
        },

        VirPrimitiveKind::String => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        VirPrimitiveKind::Handle => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },
    }
}

/// Zero-sized layout for sentinel types.
fn sentinel_layout() -> VirTypeLayout {
    VirTypeLayout {
        is_rc: false,
        is_heap: false,
        is_wide: false,
        slot_count: 0,
        storage: StorageClass::Void,
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_table::VirTypeTable;
    use vole_identity::{NameId, TypeDefId, VirTypeId};

    /// Helper: create a NameId for testing.
    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    #[test]
    fn simple_param_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        assert_eq!(mapping[&param_id], VirTypeId::I64);
    }

    #[test]
    fn compound_array_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let array_id = source.intern(VirType::Array { elem: param_id }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        // The array should now be Array { elem: I64 }.
        let new_array_id = mapping[&array_id];
        let new_array = target.get(new_array_id);
        assert_eq!(
            *new_array,
            VirType::Array {
                elem: VirTypeId::I64
            }
        );
    }

    #[test]
    fn nested_optional_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(200);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let opt_id = source.intern_optional(param_id, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::STRING);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_opt = target.get(mapping[&opt_id]);
        assert!(
            matches!(new_opt, VirType::Optional { inner, .. } if *inner == VirTypeId::STRING),
            "expected Optional<String>, got {new_opt:?}"
        );
    }

    #[test]
    fn no_params_identity() {
        let mut source = VirTypeTable::new();
        let arr_id = source.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let subs = TypeSubstitution::default();

        let mapping = substitute_types(&source, &mut target, &subs);

        // The array of I64 should remain structurally identical.
        let new_arr = target.get(mapping[&arr_id]);
        assert_eq!(
            *new_arr,
            VirType::Array {
                elem: VirTypeId::I64
            }
        );
    }

    #[test]
    fn multiple_params() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let u_name = name(200);
        let t_id = source.intern(VirType::Param { name: t_name }, None);
        let u_id = source.intern(VirType::Param { name: u_name }, None);
        let tuple_id = source.intern(
            VirType::Tuple {
                elems: vec![t_id, u_id],
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        subs.insert(u_name, VirTypeId::STRING);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_tuple = target.get(mapping[&tuple_id]);
        assert_eq!(
            *new_tuple,
            VirType::Tuple {
                elems: vec![VirTypeId::I64, VirTypeId::STRING]
            }
        );
    }

    #[test]
    fn class_type_args_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let def = TypeDefId::new(42);
        let class_id = source.intern(
            VirType::Class {
                def,
                type_args: vec![param_id],
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_class = target.get(mapping[&class_id]);
        assert_eq!(
            *new_class,
            VirType::Class {
                def,
                type_args: vec![VirTypeId::I64]
            }
        );
    }

    #[test]
    fn function_type_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let func_id = source.intern(
            VirType::Function {
                params: vec![param_id, VirTypeId::BOOL],
                ret: param_id,
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::F64);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_func = target.get(mapping[&func_id]);
        assert_eq!(
            *new_func,
            VirType::Function {
                params: vec![VirTypeId::F64, VirTypeId::BOOL],
                ret: VirTypeId::F64,
            }
        );
    }

    #[test]
    fn fallible_type_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let err_def = TypeDefId::new(99);
        let err_id = source.intern(VirType::Error { def: err_def }, None);
        let fallible_id = source.intern(
            VirType::Fallible {
                success: param_id,
                errors: vec![err_id],
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::STRING);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_fallible = target.get(mapping[&fallible_id]);
        let new_err_id = mapping[&err_id];
        assert_eq!(
            *new_fallible,
            VirType::Fallible {
                success: VirTypeId::STRING,
                errors: vec![new_err_id],
            }
        );
    }

    #[test]
    fn union_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let union_id = source.intern(
            VirType::Union {
                variants: vec![param_id, VirTypeId::NIL],
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_union = target.get(mapping[&union_id]);
        assert_eq!(
            *new_union,
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::NIL]
            }
        );
    }

    #[test]
    fn struct_type_args_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let def = TypeDefId::new(10);
        let struct_id = source.intern(
            VirType::Struct {
                def,
                type_args: vec![param_id],
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::BOOL);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_struct = target.get(mapping[&struct_id]);
        assert_eq!(
            *new_struct,
            VirType::Struct {
                def,
                type_args: vec![VirTypeId::BOOL]
            }
        );
    }

    #[test]
    fn interface_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let def = TypeDefId::new(55);
        let iface_id = source.intern(
            VirType::Interface {
                def,
                type_args: vec![param_id],
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I32);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_iface = target.get(mapping[&iface_id]);
        assert_eq!(
            *new_iface,
            VirType::Interface {
                def,
                type_args: vec![VirTypeId::I32]
            }
        );
    }

    #[test]
    fn runtime_iterator_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let iter_id = source.intern(VirType::RuntimeIterator { elem: param_id }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::F64);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_iter = target.get(mapping[&iter_id]);
        assert_eq!(
            *new_iter,
            VirType::RuntimeIterator {
                elem: VirTypeId::F64
            }
        );
    }

    #[test]
    fn fixed_array_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let fixed_id = source.intern(
            VirType::FixedArray {
                elem: param_id,
                len: 4,
            },
            None,
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::U8);

        let mapping = substitute_types(&source, &mut target, &subs);

        let new_fixed = target.get(mapping[&fixed_id]);
        assert_eq!(
            *new_fixed,
            VirType::FixedArray {
                elem: VirTypeId::U8,
                len: 4
            }
        );
    }

    #[test]
    fn layout_computed_after_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let array_id = source.intern(VirType::Array { elem: param_id }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        // The new array type should have a layout (RC pointer).
        let new_array_id = mapping[&array_id];
        let layout = target
            .get_layout(new_array_id)
            .expect("array should have layout");
        assert!(layout.is_rc);
        assert!(layout.is_heap);
        assert_eq!(layout.storage, StorageClass::Pointer);
    }

    #[test]
    fn param_without_substitution_preserved() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        // Empty substitution: param T is not mapped.
        let subs = TypeSubstitution::default();

        let mapping = substitute_types(&source, &mut target, &subs);

        // Should still be a Param in the target.
        let new_param = target.get(mapping[&param_id]);
        assert_eq!(*new_param, VirType::Param { name: t_name });
        // No layout for unresolved params.
        assert!(target.get_layout(mapping[&param_id]).is_none());
    }

    #[test]
    fn reserved_primitives_map_to_themselves() {
        let source = VirTypeTable::new();
        let mut target = VirTypeTable::new();
        let subs = TypeSubstitution::default();

        let mapping = substitute_types(&source, &mut target, &subs);

        // All reserved entries should map to the same VirTypeId in the target
        // (target also has the same reserved entries).
        assert_eq!(mapping[&VirTypeId::I64], VirTypeId::I64);
        assert_eq!(mapping[&VirTypeId::STRING], VirTypeId::STRING);
        assert_eq!(mapping[&VirTypeId::BOOL], VirTypeId::BOOL);
        assert_eq!(mapping[&VirTypeId::VOID], VirTypeId::VOID);
        assert_eq!(mapping[&VirTypeId::NEVER], VirTypeId::NEVER);
        assert_eq!(mapping[&VirTypeId::RANGE], VirTypeId::RANGE);
    }

    #[test]
    fn deeply_nested_substitution() {
        // Array { elem: Optional { inner: Param(T) } } -> Array { elem: Optional { inner: I64 } }
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let opt_id = source.intern_optional(param_id, None);
        let array_id = source.intern(VirType::Array { elem: opt_id }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        // Check the inner optional.
        let new_opt = target.get(mapping[&opt_id]);
        assert!(
            matches!(new_opt, VirType::Optional { inner, .. } if *inner == VirTypeId::I64),
            "expected Optional<i64>, got {new_opt:?}"
        );

        // Check the outer array.
        let new_array = target.get(mapping[&array_id]);
        let expected_opt_id = mapping[&opt_id];
        assert_eq!(
            *new_array,
            VirType::Array {
                elem: expected_opt_id
            }
        );
    }

    #[test]
    fn deduplication_across_substitution() {
        // Two different params both mapping to I64 should result in the same VirTypeId.
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let u_name = name(200);
        let _t_id = source.intern(VirType::Param { name: t_name }, None);
        let _u_id = source.intern(VirType::Param { name: u_name }, None);

        let t_arr_id = source.intern(VirType::Array { elem: _t_id }, None);
        let u_arr_id = source.intern(VirType::Array { elem: _u_id }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        subs.insert(u_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        // Both Array<T> and Array<U> become Array<I64>, same VirTypeId.
        assert_eq!(mapping[&t_arr_id], mapping[&u_arr_id]);
    }

    #[test]
    fn layout_for_primitive_substitution() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I128);

        let mapping = substitute_types(&source, &mut target, &subs);

        // i128 -> wide layout.
        let layout = target
            .get_layout(mapping[&param_id])
            .expect("i128 should have layout");
        assert!(layout.is_wide);
        assert_eq!(layout.slot_count, 2);
        assert_eq!(layout.storage, StorageClass::Wide);
    }

    /// After substitution, every non-Param type in the target table must have a layout.
    #[test]
    fn all_substituted_types_have_layouts() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        // Build a variety of compound types containing the param.
        let array_id = source.intern(VirType::Array { elem: param_id }, None);
        let opt_id = source.intern_optional(param_id, None);
        let tuple_id = source.intern(
            VirType::Tuple {
                elems: vec![param_id, VirTypeId::I64],
            },
            None,
        );
        let union_id = source.intern(
            VirType::Union {
                variants: vec![param_id, VirTypeId::STRING],
            },
            None,
        );
        let func_id = source.intern(
            VirType::Function {
                params: vec![param_id],
                ret: param_id,
            },
            None,
        );
        let def = TypeDefId::new(42);
        let class_id = source.intern(
            VirType::Class {
                def,
                type_args: vec![param_id],
            },
            None,
        );
        let struct_id = source.intern(
            VirType::Struct {
                def,
                type_args: vec![param_id],
            },
            None,
        );
        let iface_id = source.intern(
            VirType::Interface {
                def,
                type_args: vec![param_id],
            },
            None,
        );
        let fallible_id = source.intern(
            VirType::Fallible {
                success: param_id,
                errors: vec![],
            },
            None,
        );
        let iter_id = source.intern(VirType::RuntimeIterator { elem: param_id }, None);
        let fixed_id = source.intern(
            VirType::FixedArray {
                elem: param_id,
                len: 3,
            },
            None,
        );
        // Deeply nested: Array<Optional<T>>
        let nested_id = source.intern(VirType::Array { elem: opt_id }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&source, &mut target, &subs);

        // Every substituted compound type must have a layout.
        let ids_to_check = [
            ("Array<T>", array_id),
            ("Optional<T>", opt_id),
            ("Tuple<T,i64>", tuple_id),
            ("Union<T,String>", union_id),
            ("Function(T)->T", func_id),
            ("Class<T>", class_id),
            ("Struct<T>", struct_id),
            ("Interface<T>", iface_id),
            ("Fallible<T>", fallible_id),
            ("RuntimeIterator<T>", iter_id),
            ("FixedArray<T,3>", fixed_id),
            ("Array<Optional<T>>", nested_id),
        ];

        for (label, old_id) in ids_to_check {
            let new_id = mapping[&old_id];
            assert!(
                target.get_layout(new_id).is_some(),
                "{label}: substituted type at {new_id:?} should have a layout"
            );
        }

        // The param itself maps to I64, which has a reserved layout.
        let new_param = mapping[&param_id];
        assert_eq!(new_param, VirTypeId::I64);
        assert!(
            target.get_layout(new_param).is_some(),
            "substituted param (now I64) should have a layout"
        );
    }

    /// When source == target (simulating the monomorphize_one clone pattern),
    /// all pre-existing types retain their layouts.
    #[test]
    fn clone_target_preserves_existing_layouts() {
        let mut program_table = VirTypeTable::new();
        let arr_id = program_table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            Some(VirTypeLayout {
                is_rc: true,
                is_heap: true,
                is_wide: false,
                slot_count: 1,
                storage: StorageClass::Pointer,
            }),
        );

        let t_name = name(100);
        let _param_id = program_table.intern(VirType::Param { name: t_name }, None);

        // Clone to simulate fixpoint.rs monomorphize_one pattern.
        let mut target = program_table.clone();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);

        let mapping = substitute_types(&program_table, &mut target, &subs);

        // Pre-existing Array<I64> should retain its layout.
        let mapped_arr = mapping[&arr_id];
        let layout = target
            .get_layout(mapped_arr)
            .expect("pre-existing Array<I64> should retain layout");
        assert!(layout.is_rc);
        assert_eq!(layout.storage, StorageClass::Pointer);
    }

    /// Substitution with a non-reserved concrete type (e.g., Array<String>)
    /// produces correct layouts for compound types wrapping that type.
    #[test]
    fn substitution_with_non_reserved_concrete_type() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);
        let opt_of_param = source.intern_optional(param_id, None);

        // The concrete type is Array<String> (not a reserved VirTypeId).
        let concrete_arr = source.intern(
            VirType::Array {
                elem: VirTypeId::STRING,
            },
            Some(VirTypeLayout {
                is_rc: true,
                is_heap: true,
                is_wide: false,
                slot_count: 1,
                storage: StorageClass::Pointer,
            }),
        );

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, concrete_arr);

        let mapping = substitute_types(&source, &mut target, &subs);

        // Optional<Array<String>> should have a layout.
        let new_opt = mapping[&opt_of_param];
        let layout = target
            .get_layout(new_opt)
            .expect("Optional<Array<String>> should have a layout");
        assert!(layout.is_rc);
        assert!(layout.is_heap);

        // The concrete Array<String> itself should have a layout in the target.
        let new_arr = mapping[&concrete_arr];
        let arr_layout = target
            .get_layout(new_arr)
            .expect("Array<String> should have a layout in target");
        assert!(arr_layout.is_rc);
    }
}
