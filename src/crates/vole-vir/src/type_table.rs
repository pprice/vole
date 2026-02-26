// type_table.rs
//
// VirTypeTable: interned table of VirType entries with optional layout metadata.
//
// Lives in vole-vir (no sema dependency). Translation from sema TypeId to
// VirTypeId happens in vole-codegen::vir_lower::type_translate.

use rustc_hash::{FxHashMap, FxHashSet};
use vole_identity::{TypeId, VirTypeId};

use crate::types::{StorageClass, VirPrimitiveKind, VirType, VirTypeLayout};

/// Interned type table for the VIR.
///
/// Owns all [`VirType`] entries and their optional [`VirTypeLayout`] metadata.
/// Pre-populated with reserved primitive slots matching [`VirTypeId`] constants
/// so that codegen can match on well-known types without a table lookup.
///
/// The `sema_map` caches `TypeId -> VirTypeId` translations so each sema type
/// is translated at most once.
#[derive(Clone)]
pub struct VirTypeTable {
    /// Interned types, indexed by VirTypeId.
    types: Vec<VirType>,
    /// Per-type layout metadata (computed lazily, may be None for generics).
    layouts: Vec<Option<VirTypeLayout>>,
    /// Deduplication: VirType -> VirTypeId.
    intern_map: FxHashMap<VirType, VirTypeId>,
    /// Cache: sema TypeId -> VirTypeId (avoids re-translating the same type).
    sema_map: FxHashMap<TypeId, VirTypeId>,
}

impl VirTypeTable {
    /// Create a new table pre-populated with reserved primitive entries.
    ///
    /// The reserved entries match the [`VirTypeId`] constants (I8, I16, ...,
    /// UNKNOWN) so that `table.get(VirTypeId::I64)` returns
    /// `VirType::Primitive(VirPrimitiveKind::I64)`.
    pub fn new() -> Self {
        let mut table = Self {
            types: Vec::new(),
            layouts: Vec::new(),
            intern_map: FxHashMap::default(),
            sema_map: FxHashMap::default(),
        };
        table.populate_reserved();
        table
    }

    /// Intern a type, returning an existing `VirTypeId` if the same `VirType`
    /// was already interned, or inserting a new entry.
    pub fn intern(&mut self, ty: VirType, layout: Option<VirTypeLayout>) -> VirTypeId {
        if let Some(&existing) = self.intern_map.get(&ty) {
            // If a layout is provided and the existing entry has none, fill it in.
            if layout.is_some() && self.layouts[existing.raw() as usize].is_none() {
                self.layouts[existing.raw() as usize] = layout;
            }
            return existing;
        }
        let id = VirTypeId::from_raw(self.types.len() as u32);
        self.intern_map.insert(ty.clone(), id);
        self.types.push(ty);
        self.layouts.push(layout);
        id
    }

    /// Get the `VirType` for a `VirTypeId`.
    ///
    /// # Panics
    ///
    /// Panics if `id` is out of range.
    pub fn get(&self, id: VirTypeId) -> &VirType {
        &self.types[id.raw() as usize]
    }

    /// Get the layout for a `VirTypeId`, if computed.
    pub fn get_layout(&self, id: VirTypeId) -> Option<&VirTypeLayout> {
        self.layouts[id.raw() as usize].as_ref()
    }

    /// Set or replace the layout for an existing `VirTypeId`.
    ///
    /// # Panics
    ///
    /// Panics if `id` is out of range.
    pub fn set_layout(&mut self, id: VirTypeId, layout: VirTypeLayout) {
        self.layouts[id.raw() as usize] = Some(layout);
    }

    /// Look up a cached sema `TypeId -> VirTypeId` mapping.
    pub fn lookup_sema(&self, type_id: TypeId) -> Option<VirTypeId> {
        self.sema_map.get(&type_id).copied()
    }

    /// Record a sema `TypeId -> VirTypeId` mapping in the cache.
    pub fn insert_sema_mapping(&mut self, type_id: TypeId, vir_id: VirTypeId) {
        self.sema_map.insert(type_id, vir_id);
    }

    /// Merge all non-reserved types from `other` into `self`.
    ///
    /// Returns a mapping from `other`'s VirTypeIds to `self`'s VirTypeIds.
    /// Reserved entries (indices < FIRST_DYNAMIC) map to themselves.
    /// Non-reserved types from `other` are interned into `self`, producing
    /// either an existing ID (if the same type was already in `self`) or a
    /// new ID.
    ///
    /// This is used to merge the generic VIR type table into the program's
    /// main type table so that VIR monomorphization can operate on a single
    /// unified type table.
    pub fn merge_from(&mut self, other: &VirTypeTable) -> FxHashMap<VirTypeId, VirTypeId> {
        let mut mapping = FxHashMap::default();
        let mut in_progress = FxHashSet::default();

        // Reserved entries map to themselves (both tables have identical
        // reserved entries at the same indices).
        for i in 0..VirTypeId::FIRST_DYNAMIC {
            let id = VirTypeId::from_raw(i);
            mapping.insert(id, id);
        }

        // Non-reserved entries: recursively merge each type from `other`.
        // This handles forward references where a type at index N refers to
        // type IDs that appear later in `other`.
        for i in VirTypeId::FIRST_DYNAMIC..other.types.len() as u32 {
            let old_id = VirTypeId::from_raw(i);
            merge_one(old_id, other, self, &mut mapping, &mut in_progress);
        }

        mapping
    }

    /// Number of interned types (including reserved entries).
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// Whether the table is empty (it never is after `new()`).
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }
}

/// Remap VirTypeId references inside a VirType using a mapping.
///
/// Compound types (Array, Tuple, etc.) contain inner VirTypeIds that must
/// be remapped when moving types between type tables.
fn remap_type_ids_in_type(ty: &VirType, mapping: &FxHashMap<VirTypeId, VirTypeId>) -> VirType {
    let remap = |id: &VirTypeId| mapping.get(id).copied().unwrap_or(*id);
    let remap_vec = |ids: &[VirTypeId]| ids.iter().map(&remap).collect();

    match ty {
        // Leaf types: no inner VirTypeIds.
        VirType::Primitive(_)
        | VirType::Void
        | VirType::Nil
        | VirType::Done
        | VirType::Never
        | VirType::Range
        | VirType::MetaType
        | VirType::Unknown => ty.clone(),

        // Param: no inner VirTypeIds (name is a NameId, not VirTypeId).
        VirType::Param { .. } => ty.clone(),

        // Error: no inner VirTypeIds (def is a TypeDefId).
        VirType::Error { .. } => ty.clone(),

        // Compound types with inner VirTypeIds.
        VirType::Array { elem } => VirType::Array { elem: remap(elem) },
        VirType::FixedArray { elem, len } => VirType::FixedArray {
            elem: remap(elem),
            len: *len,
        },
        VirType::Tuple { elems } => VirType::Tuple {
            elems: remap_vec(elems),
        },
        VirType::Union { variants } => VirType::Union {
            variants: remap_vec(variants),
        },
        VirType::Optional { inner } => VirType::Optional {
            inner: remap(inner),
        },
        VirType::Fallible { success, errors } => VirType::Fallible {
            success: remap(success),
            errors: remap_vec(errors),
        },
        VirType::Function { params, ret } => VirType::Function {
            params: remap_vec(params),
            ret: remap(ret),
        },
        VirType::Class { def, type_args } => VirType::Class {
            def: *def,
            type_args: remap_vec(type_args),
        },
        VirType::Struct { def, type_args } => VirType::Struct {
            def: *def,
            type_args: remap_vec(type_args),
        },
        VirType::Interface { def, type_args } => VirType::Interface {
            def: *def,
            type_args: remap_vec(type_args),
        },
        VirType::RuntimeIterator { elem } => VirType::RuntimeIterator { elem: remap(elem) },
    }
}

/// Recursively merge one type ID from `other` into `this`, memoizing in `mapping`.
fn merge_one(
    old_id: VirTypeId,
    other: &VirTypeTable,
    this: &mut VirTypeTable,
    mapping: &mut FxHashMap<VirTypeId, VirTypeId>,
    in_progress: &mut FxHashSet<VirTypeId>,
) -> VirTypeId {
    if let Some(&mapped) = mapping.get(&old_id) {
        return mapped;
    }

    // Defensive cycle guard; recursive type cycles are not expected here.
    if !in_progress.insert(old_id) {
        return old_id;
    }

    let ty = &other.types[old_id.raw() as usize];
    match ty {
        VirType::Array { elem } => {
            merge_one(*elem, other, this, mapping, in_progress);
        }
        VirType::FixedArray { elem, .. } => {
            merge_one(*elem, other, this, mapping, in_progress);
        }
        VirType::Tuple { elems }
        | VirType::Union { variants: elems }
        | VirType::Class {
            type_args: elems, ..
        }
        | VirType::Struct {
            type_args: elems, ..
        }
        | VirType::Interface {
            type_args: elems, ..
        } => {
            for &id in elems {
                merge_one(id, other, this, mapping, in_progress);
            }
        }
        VirType::Optional { inner } | VirType::RuntimeIterator { elem: inner } => {
            merge_one(*inner, other, this, mapping, in_progress);
        }
        VirType::Fallible { success, errors } => {
            merge_one(*success, other, this, mapping, in_progress);
            for &id in errors {
                merge_one(id, other, this, mapping, in_progress);
            }
        }
        VirType::Function { params, ret } => {
            for &id in params {
                merge_one(id, other, this, mapping, in_progress);
            }
            merge_one(*ret, other, this, mapping, in_progress);
        }
        VirType::Primitive(_)
        | VirType::Void
        | VirType::Nil
        | VirType::Done
        | VirType::Never
        | VirType::Range
        | VirType::MetaType
        | VirType::Unknown
        | VirType::Param { .. }
        | VirType::Error { .. } => {}
    }

    let remapped_ty = remap_type_ids_in_type(ty, mapping);
    let layout = other.layouts[old_id.raw() as usize];
    let new_id = this.intern(remapped_ty, layout);
    mapping.insert(old_id, new_id);
    in_progress.remove(&old_id);
    new_id
}

impl Default for VirTypeTable {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Reserved entry population
// ---------------------------------------------------------------------------

/// Convenience constructors for common layout patterns.
const fn word_layout() -> VirTypeLayout {
    VirTypeLayout {
        is_rc: false,
        is_heap: false,
        is_wide: false,
        slot_count: 1,
        storage: StorageClass::Word,
    }
}

const fn float_layout() -> VirTypeLayout {
    VirTypeLayout {
        is_rc: false,
        is_heap: false,
        is_wide: false,
        slot_count: 1,
        storage: StorageClass::Float,
    }
}

const fn void_layout() -> VirTypeLayout {
    VirTypeLayout {
        is_rc: false,
        is_heap: false,
        is_wide: false,
        slot_count: 0,
        storage: StorageClass::Void,
    }
}

const fn wide_layout() -> VirTypeLayout {
    VirTypeLayout {
        is_rc: false,
        is_heap: false,
        is_wide: true,
        slot_count: 2,
        storage: StorageClass::Wide,
    }
}

const fn pointer_layout(rc: bool) -> VirTypeLayout {
    VirTypeLayout {
        is_rc: rc,
        is_heap: true,
        is_wide: false,
        slot_count: 1,
        storage: StorageClass::Pointer,
    }
}

impl VirTypeTable {
    /// Push a reserved entry without deduplication.
    ///
    /// Reserved entries may share the same `VirType` (e.g., `Unknown` is used
    /// for INVALID, F128, and UNKNOWN), so we bypass the intern map.  The
    /// intern map is populated only for unique entries so that later `intern()`
    /// calls still deduplicate against the *last* reserved slot for a given
    /// `VirType` (i.e., UNKNOWN at index 22, not INVALID at index 0).
    fn push_reserved(&mut self, ty: VirType, layout: VirTypeLayout, expected: VirTypeId) {
        let id = VirTypeId::from_raw(self.types.len() as u32);
        debug_assert_eq!(
            id,
            expected,
            "VirTypeTable: reserved entry mismatch at index {}",
            expected.raw()
        );
        // Always overwrite: last writer wins for shared VirType values.
        self.intern_map.insert(ty.clone(), id);
        self.types.push(ty);
        self.layouts.push(Some(layout));
    }

    /// Populate all reserved primitive and special type entries.
    ///
    /// Order MUST match the `VirTypeId` constants (INVALID=0, I8=1, ... UNKNOWN=22).
    fn populate_reserved(&mut self) {
        use VirPrimitiveKind as P;

        // 0: INVALID — treated as Unknown with pointer layout
        self.push_reserved(VirType::Unknown, pointer_layout(false), VirTypeId::INVALID);

        // 1-5: Signed integers
        self.push_reserved(VirType::Primitive(P::I8), word_layout(), VirTypeId::I8);
        self.push_reserved(VirType::Primitive(P::I16), word_layout(), VirTypeId::I16);
        self.push_reserved(VirType::Primitive(P::I32), word_layout(), VirTypeId::I32);
        self.push_reserved(VirType::Primitive(P::I64), word_layout(), VirTypeId::I64);
        self.push_reserved(VirType::Primitive(P::I128), wide_layout(), VirTypeId::I128);

        // 6-9: Unsigned integers
        self.push_reserved(VirType::Primitive(P::U8), word_layout(), VirTypeId::U8);
        self.push_reserved(VirType::Primitive(P::U16), word_layout(), VirTypeId::U16);
        self.push_reserved(VirType::Primitive(P::U32), word_layout(), VirTypeId::U32);
        self.push_reserved(VirType::Primitive(P::U64), word_layout(), VirTypeId::U64);

        // 10-12: Floating point
        self.push_reserved(VirType::Primitive(P::F32), float_layout(), VirTypeId::F32);
        self.push_reserved(VirType::Primitive(P::F64), float_layout(), VirTypeId::F64);
        // F128: no VirPrimitiveKind::F128 yet, use Unknown as placeholder
        self.push_reserved(VirType::Unknown, wide_layout(), VirTypeId::F128);

        // 13-14: Bool, String
        self.push_reserved(VirType::Primitive(P::Bool), word_layout(), VirTypeId::BOOL);
        self.push_reserved(
            VirType::Primitive(P::String),
            pointer_layout(true),
            VirTypeId::STRING,
        );

        // 15: Handle — RC pointer
        self.push_reserved(
            VirType::Primitive(P::Handle),
            pointer_layout(true),
            VirTypeId::HANDLE,
        );

        // 16: Void
        self.push_reserved(VirType::Void, void_layout(), VirTypeId::VOID);

        // 17-18: Nil, Done — sentinel structs, zero-sized
        self.push_reserved(VirType::Nil, void_layout(), VirTypeId::NIL);
        self.push_reserved(VirType::Done, void_layout(), VirTypeId::DONE);

        // 19: Range — 16 bytes (start + end), treated as wide
        self.push_reserved(VirType::Range, wide_layout(), VirTypeId::RANGE);

        // 20: MetaType — heap pointer, not RC
        self.push_reserved(
            VirType::MetaType,
            pointer_layout(false),
            VirTypeId::METATYPE,
        );

        // 21: Never — bottom type, no storage
        self.push_reserved(VirType::Never, void_layout(), VirTypeId::NEVER);

        // 22: Unknown — boxed TaggedValue, heap pointer.
        // This overwrites the intern_map entry for VirType::Unknown from INVALID/F128,
        // so future `intern(VirType::Unknown)` returns UNKNOWN (index 22).
        self.push_reserved(VirType::Unknown, pointer_layout(false), VirTypeId::UNKNOWN);

        debug_assert_eq!(
            self.types.len() as u32,
            VirTypeId::FIRST_DYNAMIC,
            "VirTypeTable: reserved count mismatch"
        );
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_table_has_reserved_entries() {
        let table = VirTypeTable::new();
        assert_eq!(table.len(), VirTypeId::FIRST_DYNAMIC as usize);
    }

    #[test]
    fn get_reserved_primitives() {
        let table = VirTypeTable::new();

        assert_eq!(
            *table.get(VirTypeId::I64),
            VirType::Primitive(VirPrimitiveKind::I64)
        );
        assert_eq!(
            *table.get(VirTypeId::STRING),
            VirType::Primitive(VirPrimitiveKind::String)
        );
        assert_eq!(
            *table.get(VirTypeId::BOOL),
            VirType::Primitive(VirPrimitiveKind::Bool)
        );
        assert_eq!(*table.get(VirTypeId::VOID), VirType::Void);
        assert_eq!(*table.get(VirTypeId::NEVER), VirType::Never);
        assert_eq!(*table.get(VirTypeId::UNKNOWN), VirType::Unknown);
        assert_eq!(*table.get(VirTypeId::RANGE), VirType::Range);
        assert_eq!(*table.get(VirTypeId::NIL), VirType::Nil);
        assert_eq!(*table.get(VirTypeId::DONE), VirType::Done);
        assert_eq!(*table.get(VirTypeId::METATYPE), VirType::MetaType);
    }

    #[test]
    fn intern_deduplicates() {
        let mut table = VirTypeTable::new();
        let ty = VirType::Array {
            elem: VirTypeId::I64,
        };
        let id1 = table.intern(ty.clone(), None);
        let id2 = table.intern(ty, None);
        assert_eq!(id1, id2);
        // Only one new entry beyond the reserved entries.
        assert_eq!(table.len(), VirTypeId::FIRST_DYNAMIC as usize + 1);
    }

    #[test]
    fn intern_distinct_types_get_distinct_ids() {
        let mut table = VirTypeTable::new();
        let arr_i64 = VirType::Array {
            elem: VirTypeId::I64,
        };
        let arr_string = VirType::Array {
            elem: VirTypeId::STRING,
        };
        let id1 = table.intern(arr_i64, None);
        let id2 = table.intern(arr_string, None);
        assert_ne!(id1, id2);
    }

    #[test]
    fn get_layout_for_reserved() {
        let table = VirTypeTable::new();
        let layout = table
            .get_layout(VirTypeId::I64)
            .expect("i64 should have layout");
        assert!(!layout.is_rc);
        assert!(!layout.is_heap);
        assert!(!layout.is_wide);
        assert_eq!(layout.slot_count, 1);
        assert_eq!(layout.storage, StorageClass::Word);

        let layout = table
            .get_layout(VirTypeId::I128)
            .expect("i128 should have layout");
        assert!(layout.is_wide);
        assert_eq!(layout.slot_count, 2);

        let layout = table
            .get_layout(VirTypeId::STRING)
            .expect("string should have layout");
        assert!(layout.is_rc);
        assert!(layout.is_heap);
    }

    #[test]
    fn set_layout_fills_none() {
        let mut table = VirTypeTable::new();
        let ty = VirType::Array {
            elem: VirTypeId::I64,
        };
        let id = table.intern(ty, None);
        assert!(table.get_layout(id).is_none());

        let layout = VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        };
        table.set_layout(id, layout);
        assert!(table.get_layout(id).is_some());
        assert!(table.get_layout(id).unwrap().is_rc);
    }

    #[test]
    fn intern_fills_layout_on_existing() {
        let mut table = VirTypeTable::new();
        let ty = VirType::Array {
            elem: VirTypeId::I64,
        };
        let id1 = table.intern(ty.clone(), None);
        assert!(table.get_layout(id1).is_none());

        let layout = VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        };
        let id2 = table.intern(ty, Some(layout));
        assert_eq!(id1, id2);
        assert!(table.get_layout(id1).is_some());
    }

    #[test]
    fn sema_mapping_round_trip() {
        let mut table = VirTypeTable::new();
        let sema_id = TypeId::from_raw(100);
        assert!(table.lookup_sema(sema_id).is_none());

        table.insert_sema_mapping(sema_id, VirTypeId::I64);
        assert_eq!(table.lookup_sema(sema_id), Some(VirTypeId::I64));
    }

    #[test]
    fn reserved_sema_primitives_not_auto_mapped() {
        // The table does NOT auto-populate sema_map; that is the job of
        // translate_type_id in vole-codegen.
        let table = VirTypeTable::new();
        assert!(table.lookup_sema(TypeId::I64).is_none());
    }

    #[test]
    fn is_empty_false_after_new() {
        let table = VirTypeTable::new();
        assert!(!table.is_empty());
    }

    #[test]
    fn reserved_primitives_all_have_layouts() {
        let table = VirTypeTable::new();
        for i in 0..VirTypeId::FIRST_DYNAMIC {
            let id = VirTypeId::from_raw(i);
            assert!(
                table.get_layout(id).is_some(),
                "reserved entry {} should have a layout",
                i
            );
        }
    }

    #[test]
    fn void_layout_has_zero_slots() {
        let table = VirTypeTable::new();
        let layout = table.get_layout(VirTypeId::VOID).unwrap();
        assert_eq!(layout.slot_count, 0);
        assert_eq!(layout.storage, StorageClass::Void);
    }

    #[test]
    fn handle_is_rc_pointer() {
        let table = VirTypeTable::new();
        let layout = table.get_layout(VirTypeId::HANDLE).unwrap();
        assert!(layout.is_rc);
        assert!(layout.is_heap);
        assert_eq!(layout.storage, StorageClass::Pointer);
    }

    #[test]
    fn float_layouts() {
        let table = VirTypeTable::new();
        let f32_layout = table.get_layout(VirTypeId::F32).unwrap();
        assert_eq!(f32_layout.storage, StorageClass::Float);
        assert!(!f32_layout.is_rc);

        let f64_layout = table.get_layout(VirTypeId::F64).unwrap();
        assert_eq!(f64_layout.storage, StorageClass::Float);
    }
}
