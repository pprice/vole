// vir_lower/type_translate.rs
//
// Translation from sema TypeId to VIR VirTypeId.
//
// These are free functions (not methods on VirTypeTable) because they need
// access to sema's TypeArena, which lives in vole-sema -- a dependency that
// vole-vir intentionally does not have.
//
// Wired into the lowering pipeline: LoweringCtx::translate() calls
// translate_type_id() for every VIR node that carries a VirTypeId.

use crate::PrimitiveType;
use crate::type_arena::{SemaType, TypeArena};
use vole_identity::{TypeId, VirTypeId};
use vole_log::compile_timed;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{StorageClass, VirPrimitiveKind, VirType, VirTypeLayout};

/// Translate a sema `TypeId` into a `VirTypeId`, interning the result.
///
/// This is intentionally stateless with respect to sema `TypeId`s: `VirTypeId`
/// deduplication is handled by `VirTypeTable::intern`.
pub fn translate_type_id(
    table: &mut VirTypeTable,
    type_id: TypeId,
    arena: &TypeArena,
) -> VirTypeId {
    // Fast path: return cached mapping if this TypeId was already translated.
    // This is the first check because it's the common case -- most calls are
    // for types that have already been translated. Sentinel rebinding (below)
    // is idempotent and only needs to fire once, so returning a cached
    // sentinel VirTypeId is safe.
    if let Some(cached) = table.lookup_type_id(type_id) {
        return cached;
    }

    // Keep f128 on its reserved VIR slot (VirTypeId::F128). Mapping it through
    // `VirPrimitiveKind::F64` loses identity for composite/container lookups in
    // mixed sema/VIR bridge paths.
    if type_id == TypeId::F128 {
        table.record_type_id(type_id, VirTypeId::F128);
        return VirTypeId::F128;
    }

    // Sentinel types (nil, Done, user-defined zero-field structs) are
    // special: they have reserved VirTypeId slots and zero-size layout.
    // Check before SemaType match since sentinels may be SemaType::Struct
    // internally after prelude rebinding.  rebind_sentinel is idempotent,
    // so the cache check above safely short-circuits repeat calls.
    if arena.is_sentinel(type_id) {
        let vir_id = translate_sentinel(table, type_id, arena);
        table.record_type_id(type_id, vir_id);
        return vir_id;
    }

    let vir_type = translate_sema_type(table, type_id, arena);
    let layout = translate_layout(type_id, arena);
    let vir_id = table.intern(vir_type, layout);
    table.record_type_id(type_id, vir_id);

    // Track closure flag as side-band metadata (does not affect type identity).
    if let SemaType::Function {
        is_closure: true, ..
    } = arena.get(type_id)
    {
        table.mark_closure(vir_id);
    }

    // For Iterator<T> interface types, also pre-intern the VirType::RuntimeIterator
    // entry so codegen can find it via lookup_runtime_iterator_v(). The primary
    // VirTypeId remains Interface (needed for vtable generation during boxing);
    // RuntimeIterator is a secondary entry for the runtime dispatch path.
    if let Some(elem_sema) = arena.unwrap_iterator_interface_elem(type_id) {
        let elem_vir = translate_type_id(table, elem_sema, arena);
        let rt_layout = Some(VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        });
        let rt_vir = table.intern(VirType::RuntimeIterator { elem: elem_vir }, rt_layout);
        // Record reverse mapping only (VirTypeId → sema TypeId) so that
        // lookup_runtime_iterator_sema returns the Iterator<T> sema TypeId.
        // We must NOT overwrite the forward mapping (sema TypeId → VirTypeId)
        // which should remain Interface (needed for vtable generation).
        table.record_reverse_type_id(rt_vir, type_id);
    }

    vir_id
}

/// Translate sentinel types to their reserved VirTypeId.
///
/// Built-in sentinels (nil, Done) are mapped to their reserved VirTypeId
/// slots.  When the sema type has been rebound to a Struct (normal after
/// prelude loading), the reserved slot is rebound to carry the correct
/// TypeDefId.  User-defined sentinels are interned as normal VirType::Struct
/// entries and marked in the sentinel_ids set.
fn translate_sentinel(table: &mut VirTypeTable, type_id: TypeId, arena: &TypeArena) -> VirTypeId {
    // Built-in sentinels: always return the reserved VirTypeId.
    // Rebind the VirType::Struct at the reserved slot if we know the TypeDefId.
    if type_id == arena.nil() {
        if let SemaType::Struct { type_def_id, .. } = arena.get(type_id) {
            table.rebind_sentinel(VirTypeId::NIL, *type_def_id);
        }
        return VirTypeId::NIL;
    }
    if type_id == arena.done() {
        if let SemaType::Struct { type_def_id, .. } = arena.get(type_id) {
            table.rebind_sentinel(VirTypeId::DONE, *type_def_id);
        }
        return VirTypeId::DONE;
    }

    // User-defined sentinels: intern as Struct and mark as sentinel.
    if let SemaType::Struct { type_def_id, .. } = arena.get(type_id) {
        let layout = Some(sentinel_layout());
        let vir_id = table.intern(
            VirType::Struct {
                def: *type_def_id,
                type_args: vec![],
            },
            layout,
        );
        table.mark_sentinel(vir_id);
        vir_id
    } else {
        // Non-struct sentinel fallback (shouldn't happen in practice).
        VirTypeId::NIL
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

/// Map a `SemaType` variant to the corresponding `VirType`.
///
/// Compound types are translated recursively via `translate_type_id`.
fn translate_sema_type(table: &mut VirTypeTable, type_id: TypeId, arena: &TypeArena) -> VirType {
    match arena.get(type_id) {
        SemaType::Primitive(prim) => VirType::Primitive(translate_primitive(*prim)),

        SemaType::Handle => VirType::Primitive(VirPrimitiveKind::Handle),
        SemaType::Void => VirType::Void,
        SemaType::Range => VirType::Range,
        SemaType::MetaType => VirType::MetaType,
        SemaType::Never => VirType::Never,
        SemaType::Unknown => VirType::Unknown,

        SemaType::Array(elem) => {
            let elem_vir = translate_type_id(table, *elem, arena);
            VirType::Array { elem: elem_vir }
        }

        SemaType::FixedArray { element, size } => {
            let elem_vir = translate_type_id(table, *element, arena);
            VirType::FixedArray {
                elem: elem_vir,
                len: *size as u32,
            }
        }

        SemaType::Union(variants) => translate_union(table, variants, arena),

        SemaType::Tuple(elems) => {
            let vir_elems: Vec<VirTypeId> = elems
                .iter()
                .map(|&e| translate_type_id(table, e, arena))
                .collect();
            VirType::Tuple { elems: vir_elems }
        }

        SemaType::Function {
            params,
            ret,
            is_closure: _,
        } => {
            let vir_params: Vec<VirTypeId> = params
                .iter()
                .map(|&p| translate_type_id(table, p, arena))
                .collect();
            let vir_ret = translate_type_id(table, *ret, arena);
            VirType::Function {
                params: vir_params,
                ret: vir_ret,
            }
        }

        SemaType::Class {
            type_def_id,
            type_args,
        } => {
            let vir_args: Vec<VirTypeId> = type_args
                .iter()
                .map(|&a| translate_type_id(table, a, arena))
                .collect();
            VirType::Class {
                def: *type_def_id,
                type_args: vir_args,
            }
        }

        SemaType::Struct {
            type_def_id,
            type_args,
        } => {
            let vir_args: Vec<VirTypeId> = type_args
                .iter()
                .map(|&a| translate_type_id(table, a, arena))
                .collect();
            VirType::Struct {
                def: *type_def_id,
                type_args: vir_args,
            }
        }

        SemaType::Interface {
            type_def_id,
            type_args,
        } => {
            let vir_args: Vec<VirTypeId> = type_args
                .iter()
                .map(|&a| translate_type_id(table, a, arena))
                .collect();
            VirType::Interface {
                def: *type_def_id,
                type_args: vir_args,
            }
        }

        SemaType::Error { type_def_id } => VirType::Error { def: *type_def_id },

        SemaType::Fallible { success, error } => {
            let success_vir = translate_type_id(table, *success, arena);
            let errors_vir = translate_fallible_errors(table, *error, arena);
            VirType::Fallible {
                success: success_vir,
                errors: errors_vir,
            }
        }

        SemaType::TypeParam(name_id) => VirType::Param { name: *name_id },

        // TypeParamRef: look through to the underlying param name.
        // Post-monomorphization these should not appear, but if they do
        // we map them to Param to preserve the information.
        SemaType::TypeParamRef(_) => VirType::Unknown,

        // Module, Structural, Placeholder, Invalid: should not appear in
        // lowered code. Map to Unknown as a safe fallback.
        SemaType::Module(_)
        | SemaType::Structural(_)
        | SemaType::Placeholder(_)
        | SemaType::Invalid { .. } => VirType::Unknown,
    }
}

/// Translate the error part of a fallible type to a list of VirTypeId error variants.
///
/// In sema, `Fallible { success, error }` has `error` as either a single
/// `SemaType::Error` or a `SemaType::Union` of error types.
fn translate_fallible_errors(
    table: &mut VirTypeTable,
    error_type_id: TypeId,
    arena: &TypeArena,
) -> Vec<VirTypeId> {
    match arena.get(error_type_id) {
        SemaType::Union(variants) => variants
            .iter()
            .map(|&v| translate_type_id(table, v, arena))
            .collect(),
        _ => vec![translate_type_id(table, error_type_id, arena)],
    }
}

/// Translate a sema union to VirType, detecting optional patterns.
///
/// If the union is `T | nil` (exactly two variants, one of which is nil),
/// emit `VirType::Optional { inner }` instead of a full union.
fn translate_union(table: &mut VirTypeTable, variants: &[TypeId], arena: &TypeArena) -> VirType {
    let nil_id = arena.nil();
    let has_nil = variants.contains(&nil_id);
    let non_nil: Vec<TypeId> = variants.iter().copied().filter(|&v| v != nil_id).collect();

    if has_nil && non_nil.len() == 1 {
        let inner = translate_type_id(table, non_nil[0], arena);
        // Preserve sema's canonical variant ordering directly rather than
        // recomputing via VIR sort keys.  The `variants` parameter carries
        // sema's authoritative order which may differ from the VIR-level
        // sort after sentinel rebinding.
        let vir_variants: [VirTypeId; 2] = {
            let translated: Vec<VirTypeId> = variants
                .iter()
                .map(|&v| translate_type_id(table, v, arena))
                .collect();
            [translated[0], translated[1]]
        };
        return VirType::Optional {
            inner,
            variants: vir_variants,
        };
    }

    let vir_variants: Vec<VirTypeId> = variants
        .iter()
        .map(|&v| translate_type_id(table, v, arena))
        .collect();
    VirType::Union {
        variants: vir_variants,
    }
}

/// Map a sema `PrimitiveType` to a `VirPrimitiveKind`.
fn translate_primitive(prim: PrimitiveType) -> VirPrimitiveKind {
    match prim {
        PrimitiveType::I8 => VirPrimitiveKind::I8,
        PrimitiveType::I16 => VirPrimitiveKind::I16,
        PrimitiveType::I32 => VirPrimitiveKind::I32,
        PrimitiveType::I64 => VirPrimitiveKind::I64,
        PrimitiveType::I128 => VirPrimitiveKind::I128,
        PrimitiveType::U8 => VirPrimitiveKind::U8,
        PrimitiveType::U16 => VirPrimitiveKind::U16,
        PrimitiveType::U32 => VirPrimitiveKind::U32,
        PrimitiveType::U64 => VirPrimitiveKind::U64,
        PrimitiveType::F32 => VirPrimitiveKind::F32,
        PrimitiveType::F64 => VirPrimitiveKind::F64,
        PrimitiveType::F128 => VirPrimitiveKind::F64, // Defensive fallback; direct F128 is handled in translate_type_id.
        PrimitiveType::Bool => VirPrimitiveKind::Bool,
        PrimitiveType::String => VirPrimitiveKind::String,
    }
}

// ---------------------------------------------------------------------------
// Layout translation
// ---------------------------------------------------------------------------

/// Compute the physical layout for a sema type.
///
/// Returns `None` for type parameters (layout unknown until monomorphized)
/// and for invalid/placeholder types.
pub fn translate_layout(type_id: TypeId, arena: &TypeArena) -> Option<VirTypeLayout> {
    if type_id.is_invalid() {
        return None;
    }

    // Sentinels are zero-sized.
    if arena.is_sentinel(type_id) {
        return Some(VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 0,
            storage: StorageClass::Void,
        });
    }

    Some(match arena.get(type_id) {
        SemaType::Primitive(prim) => primitive_layout(*prim),

        SemaType::Handle => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        SemaType::Void => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 0,
            storage: StorageClass::Void,
        },

        SemaType::Never => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 0,
            storage: StorageClass::Void,
        },

        SemaType::Range => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: true,
            slot_count: 2,
            storage: StorageClass::Wide,
        },

        SemaType::MetaType => VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // RC heap types: class, string (handled by primitive), array, function
        SemaType::Class { .. } | SemaType::Array(_) => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Functions/closures are RC heap objects
        SemaType::Function { .. } => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Interfaces are fat pointers to RC implementors
        SemaType::Interface { .. } => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Error types are heap-allocated
        SemaType::Error { .. } => VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Struct: stack-allocated value type, NOT RC
        SemaType::Struct { .. } => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Union: pointer-sized (tag+payload on heap or stack)
        SemaType::Union(_) => VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Fallible: similar to union (tag+payload)
        SemaType::Fallible { .. } => VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Tuple: stack-allocated composite
        SemaType::Tuple(_) => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // FixedArray: stack-allocated
        SemaType::FixedArray { .. } => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Unknown: boxed TaggedValue
        SemaType::Unknown => VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },

        // Type parameters: layout unknown until monomorphization.
        SemaType::TypeParam(_) | SemaType::TypeParamRef(_) => return None,

        // Sema-internal types: should not reach codegen, use pointer fallback.
        SemaType::Module(_)
        | SemaType::Structural(_)
        | SemaType::Placeholder(_)
        | SemaType::Invalid { .. } => VirTypeLayout {
            is_rc: false,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },
    })
}

/// Compute layout for a primitive type.
fn primitive_layout(prim: PrimitiveType) -> VirTypeLayout {
    match prim {
        PrimitiveType::I8
        | PrimitiveType::U8
        | PrimitiveType::Bool
        | PrimitiveType::I16
        | PrimitiveType::U16
        | PrimitiveType::I32
        | PrimitiveType::U32
        | PrimitiveType::I64
        | PrimitiveType::U64 => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Word,
        },

        PrimitiveType::I128 | PrimitiveType::F128 => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: true,
            slot_count: 2,
            storage: StorageClass::Wide,
        },

        PrimitiveType::F32 | PrimitiveType::F64 => VirTypeLayout {
            is_rc: false,
            is_heap: false,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Float,
        },

        PrimitiveType::String => VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        },
    }
}

// ---------------------------------------------------------------------------
// Post-lowering sweep
// ---------------------------------------------------------------------------

/// Sweep all TypeIds in the arena and ensure each has a VirTypeId mapping.
///
/// During VIR lowering, `translate_type_id()` is called on-demand for types
/// that appear in lowered nodes.  However, sema's `TypeArena::substitute()`
/// creates ~1,900 monomorphized types during Pass 2 generic analysis that may
/// never be directly referenced by a VIR node.  This sweep catches those
/// unmapped types so that codegen can resolve any sema TypeId via
/// `VirTypeTable::lookup_type_id()` without falling back to the TypeArena.
///
/// Uses full recursive `translate_type_id()` to ensure all compound types
/// and their children are properly registered with correct VirTypeIds.
/// This eliminates the need for compat-encoded fallback VirTypeIds in
/// codegen — every type flowing through codegen will have a real
/// VirTypeTable entry.
#[compile_timed(DEBUG)]
pub fn sweep_unmapped_type_ids(table: &mut VirTypeTable, arena: &TypeArena) {
    let count = arena.type_count();

    // Pass 1: Collect TypeIds that need (re)translation.
    // This includes both unmapped types AND types erroneously mapped to
    // VirTypeId::UNKNOWN (from earlier non-recursive processing where
    // children were unmapped at the time).
    let needs_translate: Vec<TypeId> = (0..count)
        .map(TypeId::from_raw)
        .filter(|&type_id| {
            if is_sema_internal(type_id, arena) {
                return false;
            }
            match table.lookup_type_id(type_id) {
                None => true,
                Some(vir_ty) if vir_ty == VirTypeId::UNKNOWN && type_id != TypeId::UNKNOWN => true,
                _ => false,
            }
        })
        .collect();

    // Pass 2: Recursively translate each type. `translate_type_id` is
    // idempotent (deduplicates via `intern`) and records the TypeId mapping.
    for type_id in needs_translate {
        translate_type_id(table, type_id, arena);
    }
}

/// Check if a TypeId refers to a sema-internal type that should not be
/// translated to VIR (Module, Structural, Placeholder, Invalid, TypeParamRef).
fn is_sema_internal(type_id: TypeId, arena: &TypeArena) -> bool {
    if type_id == TypeId::UNKNOWN {
        return false;
    }
    matches!(
        arena.get(type_id),
        SemaType::Module(_)
            | SemaType::Structural(_)
            | SemaType::Placeholder(_)
            | SemaType::Invalid { .. }
            | SemaType::TypeParamRef(_)
    )
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_arena::TypeArena;
    use smallvec::smallvec;

    /// Create a fresh TypeArena for testing.
    fn test_arena() -> TypeArena {
        TypeArena::new()
    }

    // -----------------------------------------------------------------------
    // Primitive type translation
    // -----------------------------------------------------------------------

    #[test]
    fn translate_i64() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::I64, &arena);
        assert_eq!(vir_id, VirTypeId::I64);
        assert_eq!(
            *table.get(vir_id),
            VirType::Primitive(VirPrimitiveKind::I64)
        );
    }

    #[test]
    fn translate_i128_is_wide() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::I128, &arena);
        assert_eq!(vir_id, VirTypeId::I128);
        let layout = table.get_layout(vir_id).expect("i128 should have layout");
        assert!(layout.is_wide);
        assert_eq!(layout.slot_count, 2);
    }

    #[test]
    fn translate_string_is_rc() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::STRING, &arena);
        assert_eq!(vir_id, VirTypeId::STRING);
        let layout = table.get_layout(vir_id).expect("string should have layout");
        assert!(layout.is_rc);
        assert!(layout.is_heap);
    }

    #[test]
    fn translate_bool() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::BOOL, &arena);
        assert_eq!(vir_id, VirTypeId::BOOL);
    }

    #[test]
    fn translate_void() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::VOID, &arena);
        assert_eq!(vir_id, VirTypeId::VOID);
        let layout = table.get_layout(vir_id).expect("void should have layout");
        assert_eq!(layout.slot_count, 0);
    }

    #[test]
    fn translate_never() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::NEVER, &arena);
        assert_eq!(vir_id, VirTypeId::NEVER);
    }

    #[test]
    fn translate_unknown() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::UNKNOWN, &arena);
        assert_eq!(vir_id, VirTypeId::UNKNOWN);
    }

    #[test]
    fn translate_range() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::RANGE, &arena);
        assert_eq!(vir_id, VirTypeId::RANGE);
    }

    #[test]
    fn translate_handle() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, TypeId::HANDLE, &arena);
        assert_eq!(vir_id, VirTypeId::HANDLE);
    }

    #[test]
    fn translate_all_int_types() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();

        for (sema_id, vir_id) in [
            (TypeId::I8, VirTypeId::I8),
            (TypeId::I16, VirTypeId::I16),
            (TypeId::I32, VirTypeId::I32),
            (TypeId::I64, VirTypeId::I64),
            (TypeId::I128, VirTypeId::I128),
            (TypeId::U8, VirTypeId::U8),
            (TypeId::U16, VirTypeId::U16),
            (TypeId::U32, VirTypeId::U32),
            (TypeId::U64, VirTypeId::U64),
        ] {
            let result = translate_type_id(&mut table, sema_id, &arena);
            assert_eq!(result, vir_id, "mismatch for TypeId {:?}", sema_id);
        }
    }

    #[test]
    fn translate_float_types() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();

        let f32_id = translate_type_id(&mut table, TypeId::F32, &arena);
        assert_eq!(f32_id, VirTypeId::F32);

        let f64_id = translate_type_id(&mut table, TypeId::F64, &arena);
        assert_eq!(f64_id, VirTypeId::F64);
    }

    // -----------------------------------------------------------------------
    // Compound type translation
    // -----------------------------------------------------------------------

    #[test]
    fn translate_array_of_i64() {
        let mut arena = test_arena();
        let array_id = arena.array(TypeId::I64);

        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, array_id, &arena);
        assert_eq!(
            *table.get(vir_id),
            VirType::Array {
                elem: VirTypeId::I64
            }
        );
        let layout = table.get_layout(vir_id).expect("array should have layout");
        assert!(layout.is_rc);
        assert!(layout.is_heap);
    }

    #[test]
    fn translate_tuple() {
        let mut arena = test_arena();
        let tuple_id = arena.tuple(smallvec![TypeId::I64, TypeId::STRING]);

        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, tuple_id, &arena);
        match table.get(vir_id) {
            VirType::Tuple { elems } => {
                assert_eq!(elems.len(), 2);
                assert_eq!(elems[0], VirTypeId::I64);
                assert_eq!(elems[1], VirTypeId::STRING);
            }
            other => panic!("expected Tuple, got {other:?}"),
        }
    }

    #[test]
    fn translate_function_type() {
        let mut arena = test_arena();
        let fn_id = arena.function(smallvec![TypeId::I64], TypeId::STRING, false);

        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, fn_id, &arena);
        match table.get(vir_id) {
            VirType::Function { params, ret } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], VirTypeId::I64);
                assert_eq!(*ret, VirTypeId::STRING);
            }
            other => panic!("expected Function, got {other:?}"),
        }
    }

    #[test]
    fn translate_optional_union() {
        let mut arena = test_arena();
        // i64 | nil => Optional<i64>
        let union_id = arena.optional(TypeId::I64);

        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, union_id, &arena);
        match table.get(vir_id) {
            VirType::Optional { inner, .. } => {
                assert_eq!(*inner, VirTypeId::I64);
            }
            other => panic!("expected Optional, got {other:?}"),
        }
    }

    #[test]
    fn translate_non_optional_union() {
        let mut arena = test_arena();
        // i64 | string => Union (not optional)
        let union_id = arena.union(smallvec![TypeId::I64, TypeId::STRING]);

        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, union_id, &arena);
        match table.get(vir_id) {
            VirType::Union { variants } => {
                assert_eq!(variants.len(), 2);
            }
            other => panic!("expected Union, got {other:?}"),
        }
    }

    #[test]
    fn translate_fixed_array() {
        let mut arena = test_arena();
        let fa_id = arena.fixed_array(TypeId::I64, 3);

        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, fa_id, &arena);
        match table.get(vir_id) {
            VirType::FixedArray { elem, len } => {
                assert_eq!(*elem, VirTypeId::I64);
                assert_eq!(*len, 3);
            }
            other => panic!("expected FixedArray, got {other:?}"),
        }
    }

    #[test]
    fn translate_runtime_iterator() {
        let mut arena = test_arena();
        // Set up a fake Iterator TypeDefId so runtime_iterator() works.
        let fake_iterator_tdef = vole_identity::TypeDefId::new(999);
        arena.set_well_known_iterator_type_def_id(fake_iterator_tdef);
        let iter_id = arena.runtime_iterator(TypeId::STRING);

        // After iter-3, runtime_iterator() creates SemaType::Interface { Iterator, [STRING] },
        // which translates to VirType::Interface (not VirType::RuntimeIterator).
        // The normalize_iterator_return pass converts it to RuntimeIterator where needed.
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, iter_id, &arena);
        match table.get(vir_id) {
            VirType::Interface { def, type_args } => {
                assert_eq!(*def, fake_iterator_tdef);
                assert_eq!(type_args.len(), 1);
                assert_eq!(type_args[0], VirTypeId::STRING);
            }
            other => panic!("expected Interface (Iterator<string>), got {other:?}"),
        }
        let layout = table
            .get_layout(vir_id)
            .expect("iterator should have layout");
        assert!(layout.is_rc);
    }

    // -----------------------------------------------------------------------
    // Deduplication
    // -----------------------------------------------------------------------

    #[test]
    fn translate_caches_result() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();

        let id1 = translate_type_id(&mut table, TypeId::I64, &arena);
        let id2 = translate_type_id(&mut table, TypeId::I64, &arena);
        assert_eq!(id1, id2);
    }

    #[test]
    fn translate_deduplicates_compound() {
        let mut arena = test_arena();
        let arr1 = arena.array(TypeId::I64);
        // Intern the same array type again -- should get same TypeId from arena
        let arr2 = arena.array(TypeId::I64);
        assert_eq!(arr1, arr2); // Sema deduplicates

        let mut table = VirTypeTable::new();
        let vir1 = translate_type_id(&mut table, arr1, &arena);
        let vir2 = translate_type_id(&mut table, arr2, &arena);
        assert_eq!(vir1, vir2);
    }

    // -----------------------------------------------------------------------
    // Layout translation
    // -----------------------------------------------------------------------

    #[test]
    fn layout_primitives() {
        let layout = primitive_layout(PrimitiveType::I64);
        assert_eq!(layout.storage, StorageClass::Word);
        assert!(!layout.is_rc);
        assert_eq!(layout.slot_count, 1);

        let layout = primitive_layout(PrimitiveType::I128);
        assert!(layout.is_wide);
        assert_eq!(layout.slot_count, 2);
        assert_eq!(layout.storage, StorageClass::Wide);

        let layout = primitive_layout(PrimitiveType::F64);
        assert_eq!(layout.storage, StorageClass::Float);

        let layout = primitive_layout(PrimitiveType::String);
        assert!(layout.is_rc);
        assert!(layout.is_heap);
    }

    #[test]
    fn layout_type_param_is_none() {
        let mut arena = test_arena();
        let param_id = arena.type_param(vole_identity::NameId::new_for_test(42));
        assert!(translate_layout(param_id, &arena).is_none());
    }

    #[test]
    fn layout_invalid_is_none() {
        let arena = test_arena();
        assert!(translate_layout(TypeId::INVALID, &arena).is_none());
    }

    // -----------------------------------------------------------------------
    // Sentinel translation
    // -----------------------------------------------------------------------

    #[test]
    fn translate_nil_sentinel() {
        let mut arena = test_arena();
        // In a real compilation, nil/done are marked as sentinels during
        // prelude loading. Simulate that here.
        arena.mark_sentinel(arena.nil());
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, arena.nil(), &arena);
        assert_eq!(vir_id, VirTypeId::NIL);
    }

    #[test]
    fn translate_done_sentinel() {
        let mut arena = test_arena();
        arena.mark_sentinel(arena.done());
        let mut table = VirTypeTable::new();
        let vir_id = translate_type_id(&mut table, arena.done(), &arena);
        assert_eq!(vir_id, VirTypeId::DONE);
    }

    // -----------------------------------------------------------------------
    // Edge cases: sema-internal types
    // -----------------------------------------------------------------------

    #[test]
    fn translate_invalid_type() {
        let arena = test_arena();
        let mut table = VirTypeTable::new();
        // TypeId::INVALID maps to SemaType::Invalid, which maps to VirType::Unknown
        let vir_id = translate_type_id(&mut table, TypeId::INVALID, &arena);
        assert_eq!(*table.get(vir_id), VirType::Unknown);
    }
}
