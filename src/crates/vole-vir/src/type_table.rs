// type_table.rs
//
// VirTypeTable: interned table of VirType entries with optional layout metadata.
//
// Lives in vole-vir (no sema dependency). It stores VIR-native type identities
// only (`VirTypeId`).

use rustc_hash::{FxHashMap, FxHashSet};
use vole_identity::{NameId, TypeDefId, TypeId, VirTypeId};

use crate::types::{StorageClass, VirPrimitiveKind, VirType, VirTypeLayout};

/// Interned type table for the VIR.
///
/// Owns all [`VirType`] entries and their optional [`VirTypeLayout`] metadata.
/// Pre-populated with reserved primitive slots matching [`VirTypeId`] constants
/// so that codegen can match on well-known types without a table lookup.
///
#[derive(Clone)]
pub struct VirTypeTable {
    /// Interned types, indexed by VirTypeId.
    types: Vec<VirType>,
    /// Per-type layout metadata (computed lazily, may be None for generics).
    layouts: Vec<Option<VirTypeLayout>>,
    /// Deduplication: VirType -> VirTypeId.
    intern_map: FxHashMap<VirType, VirTypeId>,
    /// Reverse mapping from sema `TypeId` to `VirTypeId`.
    ///
    /// Populated by `translate_type_id()` during VIR lowering so that codegen
    /// can resolve any sema TypeId to its VirTypeId without falling back to the
    /// TypeArena.  Pre-populated with the reserved primitive/special constants
    /// that are identity-mapped between the two ID spaces.
    ///
    /// Uses a direct-indexed Vec (keyed by TypeId raw index) instead of a
    /// HashMap for O(1) lookup on the hot path.  Grows lazily as new TypeIds
    /// are recorded.
    type_id_to_vir: Vec<Option<VirTypeId>>,
    /// Reverse mapping from `VirTypeId` to sema `TypeId`.
    ///
    /// Populated alongside `type_id_to_vir` in `record_type_id()` and
    /// `populate_reserved_type_id_map()`.  When multiple sema `TypeId`s map to
    /// the same `VirTypeId` (structurally identical internings) the first
    /// recorded TypeId wins — any of them is correct since they represent the
    /// same type.
    vir_to_type_id: FxHashMap<VirTypeId, TypeId>,
    /// VirTypeIds that represent sentinel types (zero-field structs like nil, Done,
    /// and user-defined sentinels).  Populated during reserved slot init and
    /// type translation.
    sentinel_ids: FxHashSet<VirTypeId>,
    /// VirTypeIds that represent closure types (as opposed to plain function types).
    ///
    /// This is side-band metadata: closures and functions with the same
    /// signature share a single `VirType::Function` entry (same VirTypeId).
    /// Whether the *original sema type* was a closure is tracked here so
    /// codegen can distinguish them (e.g. for vtable keys and display names).
    closure_ids: FxHashSet<VirTypeId>,
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
            type_id_to_vir: Vec::new(),
            vir_to_type_id: FxHashMap::default(),
            sentinel_ids: FxHashSet::default(),
            closure_ids: FxHashSet::default(),
        };
        table.populate_reserved();
        table.populate_reserved_type_id_map();
        table
    }

    /// Look up an existing `VirTypeId` for a `VirType` without interning.
    ///
    /// Returns `Some(id)` if the type was already interned, `None` otherwise.
    /// Unlike `intern()`, this never grows the table.
    pub fn lookup(&self, ty: &VirType) -> Option<VirTypeId> {
        self.intern_map.get(ty).copied()
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

        // Merge the TypeId→VirTypeId mapping, remapping VirTypeIds through the
        // merge mapping so they reference `self`'s ID space.
        for (raw, slot) in other.type_id_to_vir.iter().enumerate() {
            if let Some(old_vir_id) = *slot {
                let type_id = TypeId::from_raw(raw as u32);
                let new_vir_id = mapping.get(&old_vir_id).copied().unwrap_or(old_vir_id);
                let idx = raw;
                if idx >= self.type_id_to_vir.len() {
                    self.type_id_to_vir.resize(idx + 1, None);
                }
                self.type_id_to_vir[idx] = Some(new_vir_id);
                // merge_from overwrites, so also overwrite the reverse map
                self.vir_to_type_id.insert(new_vir_id, type_id);
            }
        }

        // Merge sentinel_ids, remapping through the merge mapping.
        for &old_sentinel in &other.sentinel_ids {
            let new_sentinel = mapping.get(&old_sentinel).copied().unwrap_or(old_sentinel);
            self.sentinel_ids.insert(new_sentinel);
        }

        mapping
    }

    /// Merge types from `other` into `self`, preserving existing TypeId
    /// mappings.
    ///
    /// Like `merge_from`, but does NOT overwrite existing `type_id_to_vir`
    /// entries in `self`.  This is used for module VIR cache merging: the
    /// cached type table may contain TypeId mappings from a different file's
    /// sema analysis, and we don't want those to overwrite the current file's
    /// mappings.
    ///
    /// Returns a mapping from `other`'s VirTypeIds to `self`'s VirTypeIds.
    pub fn merge_from_additive(&mut self, other: &VirTypeTable) -> FxHashMap<VirTypeId, VirTypeId> {
        let mut mapping = FxHashMap::default();
        let mut in_progress = FxHashSet::default();

        for i in 0..VirTypeId::FIRST_DYNAMIC {
            let id = VirTypeId::from_raw(i);
            mapping.insert(id, id);
        }

        for i in VirTypeId::FIRST_DYNAMIC..other.types.len() as u32 {
            let old_id = VirTypeId::from_raw(i);
            merge_one(old_id, other, self, &mut mapping, &mut in_progress);
        }

        // Additive: only insert TypeId→VirTypeId entries that don't already
        // exist in `self`.
        for (raw, slot) in other.type_id_to_vir.iter().enumerate() {
            if let Some(old_vir_id) = *slot {
                let new_vir_id = mapping.get(&old_vir_id).copied().unwrap_or(old_vir_id);
                let idx = raw;
                if idx >= self.type_id_to_vir.len() {
                    self.type_id_to_vir.resize(idx + 1, None);
                }
                if self.type_id_to_vir[idx].is_none() {
                    self.type_id_to_vir[idx] = Some(new_vir_id);
                }
            }
        }
        for (&old_vir_id, &type_id) in &other.vir_to_type_id {
            let new_vir_id = mapping.get(&old_vir_id).copied().unwrap_or(old_vir_id);
            self.vir_to_type_id.entry(new_vir_id).or_insert(type_id);
        }

        // Merge sentinel_ids and closure_ids.
        for &old_sentinel in &other.sentinel_ids {
            let new_sentinel = mapping.get(&old_sentinel).copied().unwrap_or(old_sentinel);
            self.sentinel_ids.insert(new_sentinel);
        }
        for &old_closure in &other.closure_ids {
            let new_closure = mapping.get(&old_closure).copied().unwrap_or(old_closure);
            self.closure_ids.insert(new_closure);
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

// ---------------------------------------------------------------------------
// Type decomposition methods
// ---------------------------------------------------------------------------

impl VirTypeTable {
    // -- Unwrap methods (extract structural data from compound types) --------

    /// Extract the variant list from a `Union` type.
    pub fn unwrap_union(&self, id: VirTypeId) -> Option<&[VirTypeId]> {
        match self.get(id) {
            VirType::Union { variants } => Some(variants),
            _ => None,
        }
    }

    /// Extract `(params, return_type)` from a `Function` type.
    pub fn unwrap_function(&self, id: VirTypeId) -> Option<(&[VirTypeId], VirTypeId)> {
        match self.get(id) {
            VirType::Function { params, ret } => Some((params, *ret)),
            _ => None,
        }
    }

    /// Extract the inner type from an `Optional` type.
    pub fn unwrap_optional(&self, id: VirTypeId) -> Option<VirTypeId> {
        match self.get(id) {
            VirType::Optional { inner } => Some(*inner),
            _ => None,
        }
    }

    /// Extract the element type from an `Array` type.
    pub fn unwrap_array(&self, id: VirTypeId) -> Option<VirTypeId> {
        match self.get(id) {
            VirType::Array { elem } => Some(*elem),
            _ => None,
        }
    }

    /// Extract `(elem, len)` from a `FixedArray` type.
    pub fn unwrap_fixed_array(&self, id: VirTypeId) -> Option<(VirTypeId, u32)> {
        match self.get(id) {
            VirType::FixedArray { elem, len } => Some((*elem, *len)),
            _ => None,
        }
    }

    /// Extract the element list from a `Tuple` type.
    pub fn unwrap_tuple(&self, id: VirTypeId) -> Option<&[VirTypeId]> {
        match self.get(id) {
            VirType::Tuple { elems } => Some(elems),
            _ => None,
        }
    }

    /// Extract `(success, errors)` from a `Fallible` type.
    pub fn unwrap_fallible(&self, id: VirTypeId) -> Option<(VirTypeId, &[VirTypeId])> {
        match self.get(id) {
            VirType::Fallible { success, errors } => Some((*success, errors)),
            _ => None,
        }
    }

    /// Extract `(def, type_args)` from a `Class` type.
    pub fn unwrap_class(&self, id: VirTypeId) -> Option<(TypeDefId, &[VirTypeId])> {
        match self.get(id) {
            VirType::Class { def, type_args } => Some((*def, type_args)),
            _ => None,
        }
    }

    /// Extract `(def, type_args)` from a `Struct` type.
    pub fn unwrap_struct(&self, id: VirTypeId) -> Option<(TypeDefId, &[VirTypeId])> {
        match self.get(id) {
            VirType::Struct { def, type_args } => Some((*def, type_args)),
            _ => None,
        }
    }

    /// Extract `(def, type_args)` from an `Interface` type.
    pub fn unwrap_interface(&self, id: VirTypeId) -> Option<(TypeDefId, &[VirTypeId])> {
        match self.get(id) {
            VirType::Interface { def, type_args } => Some((*def, type_args)),
            _ => None,
        }
    }

    /// Extract the element type from a `RuntimeIterator` type.
    pub fn unwrap_runtime_iterator(&self, id: VirTypeId) -> Option<VirTypeId> {
        match self.get(id) {
            VirType::RuntimeIterator { elem } => Some(*elem),
            _ => None,
        }
    }

    // -- Type identity predicates -------------------------------------------

    /// Whether this is a `Union` type.
    pub fn is_union(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Union { .. })
    }

    /// Whether this is a `Function` type.
    pub fn is_function(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Function { .. })
    }

    /// Whether this is an `Optional` type.
    pub fn is_optional(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Optional { .. })
    }

    /// Whether this is an `Array` type.
    pub fn is_array(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Array { .. })
    }

    /// Whether this is a `Class` type.
    pub fn is_class(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Class { .. })
    }

    /// Whether this is a `Struct` type.
    pub fn is_struct(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Struct { .. })
    }

    /// Whether this is an `Interface` type.
    pub fn is_interface(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Interface { .. })
    }

    /// Whether this is a `Primitive(String)` type.
    pub fn is_string(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Primitive(VirPrimitiveKind::String))
    }

    /// Whether this is the `Void` type.
    pub fn is_void(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Void)
    }

    /// Whether this is the `Never` type.
    pub fn is_never(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Never)
    }

    /// Whether this is the `Unknown` type.
    pub fn is_unknown(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Unknown)
    }

    /// Whether this is a sentinel type (nil, Done, or user-defined).
    pub fn is_sentinel(&self, id: VirTypeId) -> bool {
        self.sentinel_ids.contains(&id)
    }

    /// Whether this function type originated from a closure (as opposed to a
    /// plain function).  Returns `false` for non-function types.
    pub fn is_closure(&self, id: VirTypeId) -> bool {
        self.closure_ids.contains(&id)
    }

    /// Mark a function `VirTypeId` as representing a closure.
    ///
    /// Called during VIR lowering when translating `SemaType::Function { is_closure: true }`.
    pub fn mark_closure(&mut self, id: VirTypeId) {
        self.closure_ids.insert(id);
    }

    /// Whether this is the `Range` type.
    pub fn is_range(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Range)
    }

    /// Whether this is an `Error` type.
    pub fn is_error(&self, id: VirTypeId) -> bool {
        matches!(self.get(id), VirType::Error { .. })
    }

    /// Extract the `TypeDefId` from an `Error` type.
    pub fn unwrap_error(&self, id: VirTypeId) -> Option<TypeDefId> {
        match self.get(id) {
            VirType::Error { def } => Some(*def),
            _ => None,
        }
    }

    // -- Layout predicates --------------------------------------------------

    /// Whether this type is reference-counted (from layout). Returns `false`
    /// if no layout is available.
    pub fn is_rc(&self, id: VirTypeId) -> bool {
        self.get_layout(id).is_some_and(|l| l.is_rc)
    }

    /// Whether this type requires two register slots (from layout). Returns
    /// `false` if no layout is available.
    pub fn is_wide(&self, id: VirTypeId) -> bool {
        self.get_layout(id).is_some_and(|l| l.is_wide)
    }

    /// Whether this type lives on the heap (from layout). Returns `false`
    /// if no layout is available.
    pub fn is_heap(&self, id: VirTypeId) -> bool {
        self.get_layout(id).is_some_and(|l| l.is_heap)
    }

    /// Number of register slots for this type (from layout). Returns `0`
    /// if no layout is available.
    pub fn slot_count(&self, id: VirTypeId) -> u8 {
        self.get_layout(id).map_or(0, |l| l.slot_count)
    }

    /// The storage class for this type (from layout). Returns `None` if
    /// no layout is available.
    pub fn storage_class(&self, id: VirTypeId) -> Option<StorageClass> {
        self.get_layout(id).map(|l| l.storage)
    }

    // -- Union variant ordering -----------------------------------------------

    /// Compute the sort key for a type used as a union variant.
    ///
    /// Mirrors the sema arena's `union_sort_key` so that Optional expansion
    /// produces the same `[inner, NIL]` or `[NIL, inner]` order that sema
    /// used when creating the original union type.
    ///
    /// Sort is descending by `(category, tiebreaker)`.
    pub fn union_sort_key(&self, id: VirTypeId) -> (u32, u64) {
        match self.get(id) {
            VirType::Primitive(_) => (100, id.raw() as u64),
            VirType::Array { .. } | VirType::FixedArray { .. } => (90, id.raw() as u64),
            VirType::Tuple { .. } => (85, id.raw() as u64),
            VirType::Function { .. } => (80, id.raw() as u64),
            VirType::Fallible { .. } => (75, id.raw() as u64),
            VirType::RuntimeIterator { .. } => (70, id.raw() as u64),
            VirType::Class { def, .. }
            | VirType::Struct { def, .. }
            | VirType::Interface { def, .. }
            | VirType::Error { def } => (50, def.index() as u64),
            VirType::Param { .. } => (40, id.raw() as u64),
            VirType::Optional { .. } | VirType::Union { .. } => (30, id.raw() as u64),
            VirType::Void => (20, id.raw() as u64),
            VirType::Never => (15, id.raw() as u64),
            VirType::Range => (10, id.raw() as u64),
            VirType::MetaType => (10, id.raw() as u64),
            VirType::Unknown => (5, id.raw() as u64),
        }
    }

    /// Expand an Optional type into its union variant order.
    ///
    /// Returns the two-element variant list `[inner, NIL]` or `[NIL, inner]`
    /// matching the sema arena's sort order.
    pub fn expand_optional_variants(&self, inner: VirTypeId) -> Vec<VirTypeId> {
        let inner_key = self.union_sort_key(inner);
        let nil_key = self.union_sort_key(VirTypeId::NIL);
        // Descending sort: higher key comes first.
        if inner_key >= nil_key {
            vec![inner, VirTypeId::NIL]
        } else {
            vec![VirTypeId::NIL, inner]
        }
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

        // 17-18: Nil, Done — sentinel structs, zero-sized.
        // Use placeholder TypeDefIds (u32::MAX - 1, u32::MAX) that will be
        // rebound to the real TypeDefIds during VIR type translation when the
        // prelude-defined sentinels are encountered.
        self.push_reserved(
            VirType::Struct {
                def: TypeDefId::new(u32::MAX - 1),
                type_args: vec![],
            },
            void_layout(),
            VirTypeId::NIL,
        );
        self.push_reserved(
            VirType::Struct {
                def: TypeDefId::new(u32::MAX),
                type_args: vec![],
            },
            void_layout(),
            VirTypeId::DONE,
        );
        self.sentinel_ids.insert(VirTypeId::NIL);
        self.sentinel_ids.insert(VirTypeId::DONE);

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

    /// Pre-populate the `type_id_to_vir` mapping for reserved
    /// primitive/special constants that are identity-mapped between
    /// `TypeId` and `VirTypeId`.
    ///
    /// NIL and DONE are intentionally excluded: their reserved VirType slots
    /// contain placeholder `TypeDefId`s that must be rebound via
    /// `rebind_sentinel()` during VIR type translation.  Excluding them from
    /// the pre-populated cache ensures `translate_type_id()` falls through to
    /// the sentinel path on first use, performs the rebinding, and then caches
    /// the result via `record_type_id()`.
    fn populate_reserved_type_id_map(&mut self) {
        self.type_id_to_vir
            .resize(VirTypeId::FIRST_DYNAMIC as usize, None);
        for raw in 0..VirTypeId::FIRST_DYNAMIC {
            // Skip NIL/DONE so they go through the sentinel rebinding path
            // before being cached.
            if raw == VirTypeId::NIL.raw() || raw == VirTypeId::DONE.raw() {
                continue;
            }
            let type_id = TypeId::from_raw(raw);
            let vir_id = VirTypeId::from_raw(raw);
            self.type_id_to_vir[raw as usize] = Some(vir_id);
            self.vir_to_type_id.insert(vir_id, type_id);
        }
    }
}

// ---------------------------------------------------------------------------
// type_id_to_vir accessors
// ---------------------------------------------------------------------------

impl VirTypeTable {
    /// Record a `TypeId → VirTypeId` mapping.
    ///
    /// Called by `translate_type_id()` during VIR lowering so that codegen can
    /// later resolve any sema TypeId without falling back to the TypeArena.
    pub fn record_type_id(&mut self, type_id: TypeId, vir_type_id: VirTypeId) {
        let idx = type_id.raw() as usize;
        if idx >= self.type_id_to_vir.len() {
            self.type_id_to_vir.resize(idx + 1, None);
        }
        self.type_id_to_vir[idx] = Some(vir_type_id);
        // First-wins: don't overwrite an existing reverse entry so that the
        // earliest (most canonical) sema TypeId is preserved.
        self.vir_to_type_id.entry(vir_type_id).or_insert(type_id);
    }

    /// Look up the `VirTypeId` for a sema `TypeId`, if one was recorded.
    #[inline]
    pub fn lookup_type_id(&self, type_id: TypeId) -> Option<VirTypeId> {
        let idx = type_id.raw() as usize;
        if idx < self.type_id_to_vir.len() {
            self.type_id_to_vir[idx]
        } else {
            None
        }
    }

    /// Look up the sema `TypeId` for a `VirTypeId`, if one was recorded.
    ///
    /// Returns the first TypeId that was recorded for this VirTypeId.
    pub fn lookup_vir_type_id(&self, vir_type_id: VirTypeId) -> Option<TypeId> {
        self.vir_to_type_id.get(&vir_type_id).copied()
    }

    /// Resolve a `VirTypeId` to its sema `TypeId`.
    ///
    /// First consults the reverse lookup table, then falls back to the
    /// builtin identity mapping for well-known types (raw index < FIRST_DYNAMIC).
    /// Returns `TypeId::UNKNOWN` if no mapping exists.
    ///
    /// This replaces the old `lookup_vir_type_id(v).unwrap_or_else(|| v.to_type_id_lossy())`
    /// pattern without requiring compat-encoded VirTypeIds.
    #[inline]
    pub fn vir_to_type_id(&self, vir_ty: VirTypeId) -> TypeId {
        if let Some(tid) = self.vir_to_type_id.get(&vir_ty).copied() {
            return tid;
        }
        // Builtin types (I64, F64, BOOL, etc.) share raw indices with TypeId.
        let raw = vir_ty.raw();
        if raw < TypeId::FIRST_DYNAMIC {
            TypeId::from_raw(raw)
        } else {
            TypeId::UNKNOWN
        }
    }
}

// ---------------------------------------------------------------------------
// Sentinel management
// ---------------------------------------------------------------------------

impl VirTypeTable {
    /// Mark a `VirTypeId` as a sentinel type.
    ///
    /// Called during VIR type translation for user-defined sentinels so that
    /// `is_sentinel()` returns `true` for them.
    pub fn mark_sentinel(&mut self, id: VirTypeId) {
        self.sentinel_ids.insert(id);
    }

    /// Replace the `VirType` at a reserved sentinel slot with the real
    /// `VirType::Struct` once the `TypeDefId` is known.
    ///
    /// During `populate_reserved()`, NIL and DONE are created with placeholder
    /// `TypeDefId` values.  When VIR type translation encounters the actual
    /// prelude-defined sentinel, this method updates the stored `VirType` and
    /// the intern map to use the correct `TypeDefId`.
    pub fn rebind_sentinel(&mut self, id: VirTypeId, def: TypeDefId) {
        let idx = id.raw() as usize;
        debug_assert!(idx < self.types.len(), "rebind_sentinel: id out of range");
        debug_assert!(
            self.sentinel_ids.contains(&id),
            "rebind_sentinel: id is not a sentinel"
        );

        let old_type = self.types[idx].clone();
        self.intern_map.remove(&old_type);

        let new_type = VirType::Struct {
            def,
            type_args: vec![],
        };
        self.intern_map.insert(new_type.clone(), id);
        self.types[idx] = new_type;
    }
}

// ---------------------------------------------------------------------------
// Type-construction lookups (find an interned compound type by its parts)
// ---------------------------------------------------------------------------

impl VirTypeTable {
    /// Look up an array type by its element `VirTypeId`.
    ///
    /// Returns `Some(id)` if `Array { elem }` was already interned, `None`
    /// otherwise.
    pub fn lookup_array_v(&self, elem: VirTypeId) -> Option<VirTypeId> {
        self.lookup(&VirType::Array { elem })
    }

    /// Look up a runtime iterator type by its element `VirTypeId`.
    ///
    /// Returns `Some(id)` if `RuntimeIterator { elem }` was already interned,
    /// `None` otherwise.
    pub fn lookup_runtime_iterator_v(&self, elem: VirTypeId) -> Option<VirTypeId> {
        self.lookup(&VirType::RuntimeIterator { elem })
    }

    /// Look up a fixed-array type by element and length.
    ///
    /// Returns `Some(id)` if `FixedArray { elem, len }` was already interned,
    /// `None` otherwise.
    pub fn lookup_fixed_array_v(&self, elem: VirTypeId, len: u32) -> Option<VirTypeId> {
        self.lookup(&VirType::FixedArray { elem, len })
    }

    /// Look up an interface type by `TypeDefId` and type arguments.
    ///
    /// Returns `Some(id)` if `Interface { def, type_args }` was already interned,
    /// `None` otherwise.
    pub fn lookup_interface_v(
        &self,
        def: TypeDefId,
        type_args: Vec<VirTypeId>,
    ) -> Option<VirTypeId> {
        self.lookup(&VirType::Interface { def, type_args })
    }

    /// Look up a union type by its variant `VirTypeId`s.
    ///
    /// Returns `Some(id)` if `Union { variants }` was already interned,
    /// `None` otherwise.
    pub fn lookup_union_v(&self, variants: Vec<VirTypeId>) -> Option<VirTypeId> {
        self.lookup(&VirType::Union { variants })
    }

    // -- sema TypeId convenience wrappers ------------------------------------
    //
    // These convert TypeId→VirTypeId, do the lookup, then convert back.
    // They are transitional helpers for codegen callers that still operate
    // on sema `TypeId` values.

    /// Look up an array type by element `TypeId`.
    pub fn lookup_array_sema(&self, elem: TypeId) -> Option<TypeId> {
        let elem_vir = self.lookup_type_id(elem)?;
        let arr = self.lookup_array_v(elem_vir)?;
        self.lookup_vir_type_id(arr)
    }

    /// Look up a runtime iterator type by element `TypeId`.
    pub fn lookup_runtime_iterator_sema(&self, elem: TypeId) -> Option<TypeId> {
        let elem_vir = self.lookup_type_id(elem)?;
        let iter = self.lookup_runtime_iterator_v(elem_vir)?;
        self.lookup_vir_type_id(iter)
    }

    /// Look up a fixed-array type by element `TypeId` and length.
    pub fn lookup_fixed_array_sema(&self, elem: TypeId, len: usize) -> Option<TypeId> {
        let elem_vir = self.lookup_type_id(elem)?;
        let fa = self.lookup_fixed_array_v(elem_vir, len as u32)?;
        self.lookup_vir_type_id(fa)
    }

    /// Look up an interface type by `TypeDefId` and sema type args.
    pub fn lookup_interface_sema(&self, def: TypeDefId, type_args: &[TypeId]) -> Option<TypeId> {
        let vir_args: Vec<VirTypeId> = type_args
            .iter()
            .map(|&a| self.lookup_type_id(a))
            .collect::<Option<Vec<_>>>()?;
        let iface = self.lookup_interface_v(def, vir_args)?;
        self.lookup_vir_type_id(iface)
    }

    /// Look up an optional type (`T?`) by its inner element `VirTypeId`.
    ///
    /// Checks both `Optional { inner }` and `Union { [inner, NIL] }` since
    /// some paths intern optionals as explicit Optional while others use the
    /// general Union representation.
    pub fn lookup_optional_v(&self, inner: VirTypeId) -> Option<VirTypeId> {
        self.lookup(&VirType::Optional { inner }).or_else(|| {
            // Fall back to Union representation (sorted by raw ID)
            let mut variants = vec![inner, VirTypeId::NIL];
            variants.sort_by_key(|v| v.raw());
            self.lookup(&VirType::Union { variants })
        })
    }

    /// Look up an optional type (`T?`) by its inner element `TypeId`.
    pub fn lookup_optional_sema(&self, inner: TypeId) -> Option<TypeId> {
        let inner_vir = self.lookup_type_id(inner)?;
        let opt = self.lookup_optional_v(inner_vir)?;
        self.lookup_vir_type_id(opt)
    }

    /// Look up a union type by variant `TypeId`s.
    pub fn lookup_union_sema(&self, variants: &[TypeId]) -> Option<TypeId> {
        let vir_variants: Vec<VirTypeId> = variants
            .iter()
            .map(|&v| self.lookup_type_id(v))
            .collect::<Option<Vec<_>>>()?;
        let union = self.lookup_union_v(vir_variants)?;
        self.lookup_vir_type_id(union)
    }

    // -- bulk queries ---------------------------------------------------------

    /// Return all concrete element types for which a `RuntimeIterator` exists.
    ///
    /// Skips abstract `Param` elements (type parameters).  Returns sema
    /// `TypeId` values so callers that still traffic in `TypeId` can use the
    /// result directly.
    pub fn all_concrete_runtime_iterator_elem_types_sema(&self) -> Vec<TypeId> {
        self.types
            .iter()
            .filter_map(|ty| {
                if let VirType::RuntimeIterator { elem } = ty {
                    // Skip abstract TypeParam elements
                    if matches!(self.types[elem.raw() as usize], VirType::Param { .. }) {
                        None
                    } else {
                        self.lookup_vir_type_id(*elem)
                    }
                } else {
                    None
                }
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Type substitution (replaces arena-based substitution for codegen)
// ---------------------------------------------------------------------------

impl VirTypeTable {
    /// Substitute type parameters in a type, returning the concrete `TypeId`.
    ///
    /// Walks the VIR type structure rooted at `ty`, replacing
    /// `VirType::Param { name }` entries with their concrete counterparts from
    /// `subs`.  The resulting compound `VirType` is looked up in the intern map
    /// — if the concrete type was already interned, the corresponding sema
    /// `TypeId` is returned via the reverse map.
    ///
    /// Returns `None` when:
    /// - `ty` has no `VirTypeId` mapping (unmapped sema type), or
    /// - a substituted compound type was never interned, or
    /// - the resulting `VirTypeId` has no reverse `TypeId` mapping.
    pub fn lookup_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        if subs.is_empty() {
            return Some(ty);
        }
        let vir_id = self.lookup_type_id(ty)?;
        let result_vir = self.substitute_vir(vir_id, subs)?;
        self.lookup_vir_type_id(result_vir)
    }

    /// Substitute type parameters in a type, panicking on failure.
    ///
    /// Like [`lookup_substitute`] but panics with a diagnostic message when the
    /// substituted type cannot be resolved.
    #[track_caller]
    pub fn expect_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
        context: &str,
    ) -> TypeId {
        self.lookup_substitute(ty, subs).unwrap_or_else(|| {
            panic!(
                "VirTypeTable::expect_substitute: type not found after substitution\n\
                 Context: {context}\n\
                 TypeId: {ty:?}\n\
                 Location: {}",
                std::panic::Location::caller(),
            )
        })
    }

    /// Substitute type parameters in a VIR type, returning the concrete `VirTypeId`.
    ///
    /// Like [`lookup_substitute`] but operates on `VirTypeId` input and returns
    /// `VirTypeId` output, avoiding the sema `TypeId` round-trip.  The
    /// substitution map still uses sema `TypeId` values because that is what
    /// codegen's monomorphization context (`Cg::substitutions`) provides.
    ///
    /// Returns `None` when:
    /// - a `Param` name is not in `subs`, or
    /// - the concrete `TypeId` has no `VirTypeId` mapping, or
    /// - a substituted compound type was never interned.
    pub fn lookup_substitute_vir(
        &self,
        vir_id: VirTypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<VirTypeId> {
        if subs.is_empty() {
            return Some(vir_id);
        }
        self.substitute_vir(vir_id, subs)
    }

    /// Recursive VIR-level substitution.
    ///
    /// Returns `Some(concrete_vir_id)` on success, `None` if any intermediate
    /// or final type is not interned.
    fn substitute_vir(
        &self,
        vir_id: VirTypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<VirTypeId> {
        let vir_type = self.get(vir_id);
        match vir_type {
            VirType::Param { name } => {
                let concrete_type_id = subs.get(name)?;
                self.lookup_type_id(*concrete_type_id)
            }

            // Compound types: recursively substitute children.
            VirType::Array { elem } => {
                let new_elem = self.substitute_vir(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Array { elem: new_elem })
            }
            VirType::FixedArray { elem, len } => {
                let new_elem = self.substitute_vir(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                self.lookup(&VirType::FixedArray {
                    elem: new_elem,
                    len: *len,
                })
            }
            VirType::Optional { inner } => {
                let new_inner = self.substitute_vir(*inner, subs)?;
                if new_inner == *inner {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Optional { inner: new_inner })
            }
            VirType::RuntimeIterator { elem } => {
                let new_elem = self.substitute_vir(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                self.lookup(&VirType::RuntimeIterator { elem: new_elem })
            }
            VirType::Tuple { elems } => {
                let new_elems = self.substitute_vir_vec(elems, subs)?;
                if new_elems == *elems {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Tuple { elems: new_elems })
            }
            VirType::Union { variants } => {
                let new_variants = self.substitute_vir_vec(variants, subs)?;
                if new_variants == *variants {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Union {
                    variants: new_variants,
                })
            }
            VirType::Fallible { success, errors } => {
                let new_success = self.substitute_vir(*success, subs)?;
                let new_errors = self.substitute_vir_vec(errors, subs)?;
                if new_success == *success && new_errors == *errors {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Fallible {
                    success: new_success,
                    errors: new_errors,
                })
            }
            VirType::Function { params, ret } => {
                let new_params = self.substitute_vir_vec(params, subs)?;
                let new_ret = self.substitute_vir(*ret, subs)?;
                if new_params == *params && new_ret == *ret {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Function {
                    params: new_params,
                    ret: new_ret,
                })
            }
            VirType::Class { def, type_args } => {
                let new_args = self.substitute_vir_vec(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Class {
                    def: *def,
                    type_args: new_args,
                })
            }
            VirType::Struct { def, type_args } => {
                let new_args = self.substitute_vir_vec(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Struct {
                    def: *def,
                    type_args: new_args,
                })
            }
            VirType::Interface { def, type_args } => {
                let new_args = self.substitute_vir_vec(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Interface {
                    def: *def,
                    type_args: new_args,
                })
            }

            // Leaf types: no type parameters inside.
            VirType::Primitive(_)
            | VirType::Error { .. }
            | VirType::Void
            | VirType::Never
            | VirType::Range
            | VirType::MetaType
            | VirType::Unknown => Some(vir_id),
        }
    }

    /// Substitute a vector of VirTypeIds, returning None if any fails.
    fn substitute_vir_vec(
        &self,
        ids: &[VirTypeId],
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<Vec<VirTypeId>> {
        ids.iter()
            .map(|&id| self.substitute_vir(id, subs))
            .collect()
    }

    /// Like [`lookup_substitute`] but interns compound types that don't already
    /// exist in the table after substitution.
    ///
    /// This is the mutable counterpart to `lookup_substitute`: instead of
    /// returning `None` when a substituted compound type is missing, it interns
    /// the new type and records its sema TypeId mapping.
    ///
    /// Returns `None` only when:
    /// - `ty` has no `VirTypeId` mapping (unmapped sema type), or
    /// - a `Param` name is not in `subs`, or
    /// - the concrete `TypeId` for a param has no `VirTypeId` mapping.
    pub fn lookup_substitute_or_intern(
        &mut self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        if subs.is_empty() {
            return Some(ty);
        }
        let vir_id = self.lookup_type_id(ty)?;
        let result_vir = self.substitute_vir_or_intern(vir_id, subs)?;
        // If no reverse mapping exists for result_vir, create one.
        if let Some(existing_tid) = self.lookup_vir_type_id(result_vir) {
            return Some(existing_tid);
        }
        // Synthesize a fresh TypeId for the newly interned compound type.
        // Use the same approach as translate_type_id: TypeId::from_raw(vir_id)
        // so the mapping is stable.
        let new_tid = TypeId::from_raw(result_vir.raw());
        self.record_type_id(new_tid, result_vir);
        Some(new_tid)
    }

    /// Recursive VIR-level substitution with intern-on-miss.
    ///
    /// Like [`substitute_vir`] but interns compound types that don't already
    /// exist in the table. Returns `None` only when a `Param` name is missing
    /// from `subs` or the concrete `TypeId` has no `VirTypeId` mapping.
    fn substitute_vir_or_intern(
        &mut self,
        vir_id: VirTypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<VirTypeId> {
        let vir_type = self.get(vir_id).clone();
        match &vir_type {
            VirType::Param { name } => {
                let concrete_type_id = subs.get(name)?;
                self.lookup_type_id(*concrete_type_id)
            }

            VirType::Array { elem } => {
                let new_elem = self.substitute_vir_or_intern(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                Some(self.intern(VirType::Array { elem: new_elem }, None))
            }
            VirType::FixedArray { elem, len } => {
                let new_elem = self.substitute_vir_or_intern(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::FixedArray {
                        elem: new_elem,
                        len: *len,
                    },
                    None,
                ))
            }
            VirType::Optional { inner } => {
                let new_inner = self.substitute_vir_or_intern(*inner, subs)?;
                if new_inner == *inner {
                    return Some(vir_id);
                }
                Some(self.intern(VirType::Optional { inner: new_inner }, None))
            }
            VirType::RuntimeIterator { elem } => {
                let new_elem = self.substitute_vir_or_intern(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                Some(self.intern(VirType::RuntimeIterator { elem: new_elem }, None))
            }
            VirType::Tuple { elems } => {
                let new_elems = self.substitute_vir_vec_or_intern(elems, subs)?;
                if new_elems == *elems {
                    return Some(vir_id);
                }
                Some(self.intern(VirType::Tuple { elems: new_elems }, None))
            }
            VirType::Union { variants } => {
                let new_variants = self.substitute_vir_vec_or_intern(variants, subs)?;
                if new_variants == *variants {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::Union {
                        variants: new_variants,
                    },
                    None,
                ))
            }
            VirType::Fallible { success, errors } => {
                let new_success = self.substitute_vir_or_intern(*success, subs)?;
                let new_errors = self.substitute_vir_vec_or_intern(errors, subs)?;
                if new_success == *success && new_errors == *errors {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::Fallible {
                        success: new_success,
                        errors: new_errors,
                    },
                    None,
                ))
            }
            VirType::Function { params, ret } => {
                let new_params = self.substitute_vir_vec_or_intern(params, subs)?;
                let new_ret = self.substitute_vir_or_intern(*ret, subs)?;
                if new_params == *params && new_ret == *ret {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::Function {
                        params: new_params,
                        ret: new_ret,
                    },
                    None,
                ))
            }
            VirType::Class { def, type_args } => {
                let new_args = self.substitute_vir_vec_or_intern(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::Class {
                        def: *def,
                        type_args: new_args,
                    },
                    None,
                ))
            }
            VirType::Struct { def, type_args } => {
                let new_args = self.substitute_vir_vec_or_intern(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::Struct {
                        def: *def,
                        type_args: new_args,
                    },
                    None,
                ))
            }
            VirType::Interface { def, type_args } => {
                let new_args = self.substitute_vir_vec_or_intern(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                Some(self.intern(
                    VirType::Interface {
                        def: *def,
                        type_args: new_args,
                    },
                    None,
                ))
            }

            VirType::Primitive(_)
            | VirType::Error { .. }
            | VirType::Void
            | VirType::Never
            | VirType::Range
            | VirType::MetaType
            | VirType::Unknown => Some(vir_id),
        }
    }

    /// Substitute a vector of VirTypeIds with intern-on-miss, returning None if any
    /// param fails to resolve.
    fn substitute_vir_vec_or_intern(
        &mut self,
        ids: &[VirTypeId],
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<Vec<VirTypeId>> {
        ids.iter()
            .map(|&id| self.substitute_vir_or_intern(id, subs))
            .collect()
    }

    /// Substitute type parameters using a VirTypeId-native substitution map.
    ///
    /// Like [`lookup_substitute_vir`] but the substitution map maps `NameId`
    /// directly to `VirTypeId`, avoiding the sema `TypeId` round-trip through
    /// `lookup_type_id`.  Use this when callers already have `VirTypeId` values
    /// for the concrete type arguments (e.g., from `unwrap_class`/`unwrap_struct`
    /// on the VIR type table).
    ///
    /// Returns `None` when:
    /// - a `Param` name is not in `subs`, or
    /// - a substituted compound type was never interned.
    pub fn substitute_vir_ids(
        &self,
        vir_id: VirTypeId,
        subs: &FxHashMap<NameId, VirTypeId>,
    ) -> Option<VirTypeId> {
        if subs.is_empty() {
            return Some(vir_id);
        }
        self.substitute_native(vir_id, subs)
    }

    /// Recursive VIR-level substitution with VirTypeId-native subs.
    fn substitute_native(
        &self,
        vir_id: VirTypeId,
        subs: &FxHashMap<NameId, VirTypeId>,
    ) -> Option<VirTypeId> {
        let vir_type = self.get(vir_id);
        match vir_type {
            VirType::Param { name } => subs.get(name).copied(),

            VirType::Array { elem } => {
                let new_elem = self.substitute_native(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Array { elem: new_elem })
            }
            VirType::FixedArray { elem, len } => {
                let new_elem = self.substitute_native(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                self.lookup(&VirType::FixedArray {
                    elem: new_elem,
                    len: *len,
                })
            }
            VirType::Optional { inner } => {
                let new_inner = self.substitute_native(*inner, subs)?;
                if new_inner == *inner {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Optional { inner: new_inner })
            }
            VirType::RuntimeIterator { elem } => {
                let new_elem = self.substitute_native(*elem, subs)?;
                if new_elem == *elem {
                    return Some(vir_id);
                }
                self.lookup(&VirType::RuntimeIterator { elem: new_elem })
            }
            VirType::Tuple { elems } => {
                let new_elems = self.substitute_native_vec(elems, subs)?;
                if new_elems == *elems {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Tuple { elems: new_elems })
            }
            VirType::Union { variants } => {
                let mut new_variants = self.substitute_native_vec(variants, subs)?;
                if new_variants == *variants {
                    return Some(vir_id);
                }
                // Re-sort variants by union_sort_key (descending) to match
                // sema's canonical order after substitution.  See substitute.rs
                // for the equivalent fix in the monomorphization pipeline.
                new_variants.sort_by_key(|v| std::cmp::Reverse(self.union_sort_key(*v)));
                self.lookup(&VirType::Union {
                    variants: new_variants,
                })
            }
            VirType::Fallible { success, errors } => {
                let new_success = self.substitute_native(*success, subs)?;
                let new_errors = self.substitute_native_vec(errors, subs)?;
                if new_success == *success && new_errors == *errors {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Fallible {
                    success: new_success,
                    errors: new_errors,
                })
            }
            VirType::Function { params, ret } => {
                let new_params = self.substitute_native_vec(params, subs)?;
                let new_ret = self.substitute_native(*ret, subs)?;
                if new_params == *params && new_ret == *ret {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Function {
                    params: new_params,
                    ret: new_ret,
                })
            }
            VirType::Class { def, type_args } => {
                let new_args = self.substitute_native_vec(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Class {
                    def: *def,
                    type_args: new_args,
                })
            }
            VirType::Struct { def, type_args } => {
                let new_args = self.substitute_native_vec(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Struct {
                    def: *def,
                    type_args: new_args,
                })
            }
            VirType::Interface { def, type_args } => {
                let new_args = self.substitute_native_vec(type_args, subs)?;
                if new_args == *type_args {
                    return Some(vir_id);
                }
                self.lookup(&VirType::Interface {
                    def: *def,
                    type_args: new_args,
                })
            }

            VirType::Primitive(_)
            | VirType::Error { .. }
            | VirType::Void
            | VirType::Never
            | VirType::Range
            | VirType::MetaType
            | VirType::Unknown => Some(vir_id),
        }
    }

    /// Substitute a vector of VirTypeIds using VirTypeId-native subs.
    fn substitute_native_vec(
        &self,
        ids: &[VirTypeId],
        subs: &FxHashMap<NameId, VirTypeId>,
    ) -> Option<Vec<VirTypeId>> {
        ids.iter()
            .map(|&id| self.substitute_native(id, subs))
            .collect()
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
        // NIL and DONE are now VirType::Struct with placeholder TypeDefIds
        assert!(matches!(table.get(VirTypeId::NIL), VirType::Struct { .. }));
        assert!(matches!(table.get(VirTypeId::DONE), VirType::Struct { .. }));
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

    // -- Type decomposition tests -------------------------------------------

    #[test]
    fn unwrap_union() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::STRING],
            },
            None,
        );
        let variants = table.unwrap_union(id).expect("should be a union");
        assert_eq!(variants, &[VirTypeId::I64, VirTypeId::STRING]);
        // Non-union returns None.
        assert!(table.unwrap_union(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_function() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::Function {
                params: vec![VirTypeId::I64, VirTypeId::BOOL],
                ret: VirTypeId::STRING,
            },
            None,
        );
        let (params, ret) = table.unwrap_function(id).expect("should be a function");
        assert_eq!(params, &[VirTypeId::I64, VirTypeId::BOOL]);
        assert_eq!(ret, VirTypeId::STRING);
        assert!(table.unwrap_function(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_optional() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::Optional {
                inner: VirTypeId::I64,
            },
            None,
        );
        assert_eq!(table.unwrap_optional(id), Some(VirTypeId::I64));
        assert!(table.unwrap_optional(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_array() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::Array {
                elem: VirTypeId::STRING,
            },
            None,
        );
        assert_eq!(table.unwrap_array(id), Some(VirTypeId::STRING));
        assert!(table.unwrap_array(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_fixed_array() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::FixedArray {
                elem: VirTypeId::F64,
                len: 8,
            },
            None,
        );
        let (elem, len) = table
            .unwrap_fixed_array(id)
            .expect("should be a fixed array");
        assert_eq!(elem, VirTypeId::F64);
        assert_eq!(len, 8);
        assert!(table.unwrap_fixed_array(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_tuple() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::Tuple {
                elems: vec![VirTypeId::I64, VirTypeId::BOOL, VirTypeId::STRING],
            },
            None,
        );
        let elems = table.unwrap_tuple(id).expect("should be a tuple");
        assert_eq!(elems, &[VirTypeId::I64, VirTypeId::BOOL, VirTypeId::STRING]);
        assert!(table.unwrap_tuple(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_fallible() {
        let mut table = VirTypeTable::new();
        let err_ty = table.intern(
            VirType::Error {
                def: TypeDefId::new(99),
            },
            None,
        );
        let id = table.intern(
            VirType::Fallible {
                success: VirTypeId::I64,
                errors: vec![err_ty],
            },
            None,
        );
        let (success, errors) = table.unwrap_fallible(id).expect("should be fallible");
        assert_eq!(success, VirTypeId::I64);
        assert_eq!(errors, &[err_ty]);
        assert!(table.unwrap_fallible(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_class() {
        let mut table = VirTypeTable::new();
        let def = TypeDefId::new(42);
        let id = table.intern(
            VirType::Class {
                def,
                type_args: vec![VirTypeId::STRING],
            },
            None,
        );
        let (d, args) = table.unwrap_class(id).expect("should be a class");
        assert_eq!(d, def);
        assert_eq!(args, &[VirTypeId::STRING]);
        assert!(table.unwrap_class(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_struct() {
        let mut table = VirTypeTable::new();
        let def = TypeDefId::new(7);
        let id = table.intern(
            VirType::Struct {
                def,
                type_args: vec![],
            },
            None,
        );
        let (d, args) = table.unwrap_struct(id).expect("should be a struct");
        assert_eq!(d, def);
        assert!(args.is_empty());
        assert!(table.unwrap_struct(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_interface() {
        let mut table = VirTypeTable::new();
        let def = TypeDefId::new(13);
        let id = table.intern(
            VirType::Interface {
                def,
                type_args: vec![VirTypeId::I64],
            },
            None,
        );
        let (d, args) = table.unwrap_interface(id).expect("should be an interface");
        assert_eq!(d, def);
        assert_eq!(args, &[VirTypeId::I64]);
        assert!(table.unwrap_interface(VirTypeId::I64).is_none());
    }

    #[test]
    fn unwrap_runtime_iterator() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::RuntimeIterator {
                elem: VirTypeId::I64,
            },
            None,
        );
        assert_eq!(table.unwrap_runtime_iterator(id), Some(VirTypeId::I64));
        assert!(table.unwrap_runtime_iterator(VirTypeId::I64).is_none());
    }

    // -- Type identity predicate tests --------------------------------------

    #[test]
    fn type_identity_predicates_reserved() {
        let table = VirTypeTable::new();
        assert!(table.is_string(VirTypeId::STRING));
        assert!(table.is_void(VirTypeId::VOID));
        assert!(table.is_never(VirTypeId::NEVER));
        assert!(table.is_unknown(VirTypeId::UNKNOWN));
        assert!(table.is_sentinel(VirTypeId::NIL));
        assert!(table.is_sentinel(VirTypeId::DONE));
        assert!(table.is_range(VirTypeId::RANGE));

        // Negative cases.
        assert!(!table.is_string(VirTypeId::I64));
        assert!(!table.is_void(VirTypeId::I64));
        assert!(!table.is_never(VirTypeId::I64));
        assert!(!table.is_sentinel(VirTypeId::I64));
        assert!(!table.is_range(VirTypeId::I64));
    }

    #[test]
    fn type_identity_predicates_compound() {
        let mut table = VirTypeTable::new();
        let union_id = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64],
            },
            None,
        );
        let func_id = table.intern(
            VirType::Function {
                params: vec![],
                ret: VirTypeId::VOID,
            },
            None,
        );
        let opt_id = table.intern(
            VirType::Optional {
                inner: VirTypeId::I64,
            },
            None,
        );
        let arr_id = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );
        let class_id = table.intern(
            VirType::Class {
                def: TypeDefId::new(1),
                type_args: vec![],
            },
            None,
        );
        let struct_id = table.intern(
            VirType::Struct {
                def: TypeDefId::new(2),
                type_args: vec![],
            },
            None,
        );
        let iface_id = table.intern(
            VirType::Interface {
                def: TypeDefId::new(3),
                type_args: vec![],
            },
            None,
        );
        let err_id = table.intern(
            VirType::Error {
                def: TypeDefId::new(4),
            },
            None,
        );

        assert!(table.is_union(union_id));
        assert!(table.is_function(func_id));
        assert!(table.is_optional(opt_id));
        assert!(table.is_array(arr_id));
        assert!(table.is_class(class_id));
        assert!(table.is_struct(struct_id));
        assert!(table.is_interface(iface_id));
        assert!(table.is_error(err_id));

        // Cross-check: none match the wrong predicate.
        assert!(!table.is_union(func_id));
        assert!(!table.is_function(union_id));
        assert!(!table.is_class(struct_id));
        assert!(!table.is_struct(class_id));
    }

    // -- Layout predicate tests ---------------------------------------------

    #[test]
    fn layout_predicates_reserved() {
        let table = VirTypeTable::new();

        // String: RC, heap, not wide, 1 slot, Pointer.
        assert!(table.is_rc(VirTypeId::STRING));
        assert!(table.is_heap(VirTypeId::STRING));
        assert!(!table.is_wide(VirTypeId::STRING));
        assert_eq!(table.slot_count(VirTypeId::STRING), 1);
        assert_eq!(
            table.storage_class(VirTypeId::STRING),
            Some(StorageClass::Pointer)
        );

        // I128: wide, 2 slots.
        assert!(table.is_wide(VirTypeId::I128));
        assert!(!table.is_rc(VirTypeId::I128));
        assert_eq!(table.slot_count(VirTypeId::I128), 2);
        assert_eq!(
            table.storage_class(VirTypeId::I128),
            Some(StorageClass::Wide)
        );

        // I64: word, 1 slot, not RC.
        assert!(!table.is_rc(VirTypeId::I64));
        assert!(!table.is_heap(VirTypeId::I64));
        assert!(!table.is_wide(VirTypeId::I64));
        assert_eq!(table.slot_count(VirTypeId::I64), 1);
        assert_eq!(
            table.storage_class(VirTypeId::I64),
            Some(StorageClass::Word)
        );

        // Void: 0 slots.
        assert_eq!(table.slot_count(VirTypeId::VOID), 0);
        assert_eq!(
            table.storage_class(VirTypeId::VOID),
            Some(StorageClass::Void)
        );
    }

    #[test]
    fn layout_predicates_no_layout() {
        let mut table = VirTypeTable::new();
        let id = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );
        // No layout was provided, so all layout predicates return defaults.
        assert!(!table.is_rc(id));
        assert!(!table.is_wide(id));
        assert!(!table.is_heap(id));
        assert_eq!(table.slot_count(id), 0);
        assert_eq!(table.storage_class(id), None);
    }

    // ===== lookup_substitute tests =====

    /// Helper to create a NameId for testing.
    fn test_name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    #[test]
    fn substitute_empty_subs_returns_original() {
        let table = VirTypeTable::new();
        let subs = FxHashMap::default();
        // Reserved i64 TypeId should round-trip.
        let ty = TypeId::from_raw(VirTypeId::I64.raw());
        assert_eq!(table.lookup_substitute(ty, &subs), Some(ty));
    }

    #[test]
    fn substitute_primitive_unchanged() {
        let table = VirTypeTable::new();
        let mut subs = FxHashMap::default();
        let t_name = test_name(100);
        // Substitute T -> i64, but query with i64 (no Param involved).
        subs.insert(t_name, TypeId::from_raw(VirTypeId::I64.raw()));
        let i64_ty = TypeId::from_raw(VirTypeId::I64.raw());
        assert_eq!(table.lookup_substitute(i64_ty, &subs), Some(i64_ty));
    }

    #[test]
    fn substitute_param_found() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        // Record a sema TypeId that maps to this Param VirTypeId.
        let param_sema = TypeId::from_raw(200);
        table.record_type_id(param_sema, param_vir);

        let concrete_sema = TypeId::from_raw(VirTypeId::I64.raw());
        let mut subs = FxHashMap::default();
        subs.insert(t_name, concrete_sema);

        assert_eq!(
            table.lookup_substitute(param_sema, &subs),
            Some(concrete_sema)
        );
    }

    #[test]
    fn substitute_param_not_in_subs_returns_original_with_empty_subs() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let param_sema = TypeId::from_raw(200);
        table.record_type_id(param_sema, param_vir);

        // Empty subs -> early return with the original type.
        let subs = FxHashMap::default();
        assert_eq!(table.lookup_substitute(param_sema, &subs), Some(param_sema));
    }

    #[test]
    fn substitute_param_not_in_nonempty_subs_returns_none() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let u_name = test_name(200);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let param_sema = TypeId::from_raw(300);
        table.record_type_id(param_sema, param_vir);

        // Non-empty subs, but T not in the map (only U is).
        let mut subs = FxHashMap::default();
        subs.insert(u_name, TypeId::from_raw(VirTypeId::I64.raw()));
        // Param T not in substitution map -> None (can't resolve).
        assert_eq!(table.lookup_substitute(param_sema, &subs), None);
    }

    #[test]
    fn substitute_array_of_param() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let array_of_param = table.intern(VirType::Array { elem: param_vir }, None);
        // Intern the concrete result type too.
        let array_of_i64 = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );

        let param_sema = TypeId::from_raw(200);
        let array_param_sema = TypeId::from_raw(201);
        let array_i64_sema = TypeId::from_raw(202);
        table.record_type_id(param_sema, param_vir);
        table.record_type_id(array_param_sema, array_of_param);
        table.record_type_id(array_i64_sema, array_of_i64);

        let mut subs = FxHashMap::default();
        let i64_sema = TypeId::from_raw(VirTypeId::I64.raw());
        subs.insert(t_name, i64_sema);

        assert_eq!(
            table.lookup_substitute(array_param_sema, &subs),
            Some(array_i64_sema)
        );
    }

    #[test]
    fn substitute_class_type_args() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let def = TypeDefId::new(42);
        let class_of_param = table.intern(
            VirType::Class {
                def,
                type_args: vec![param_vir],
            },
            None,
        );
        let class_of_i64 = table.intern(
            VirType::Class {
                def,
                type_args: vec![VirTypeId::I64],
            },
            None,
        );

        let param_sema = TypeId::from_raw(300);
        let class_param_sema = TypeId::from_raw(301);
        let class_i64_sema = TypeId::from_raw(302);
        table.record_type_id(param_sema, param_vir);
        table.record_type_id(class_param_sema, class_of_param);
        table.record_type_id(class_i64_sema, class_of_i64);

        let mut subs = FxHashMap::default();
        subs.insert(t_name, TypeId::from_raw(VirTypeId::I64.raw()));

        assert_eq!(
            table.lookup_substitute(class_param_sema, &subs),
            Some(class_i64_sema)
        );
    }

    #[test]
    fn substitute_returns_none_when_result_not_interned() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        // Intern Array<T> but NOT Array<i64>.
        let array_of_param = table.intern(VirType::Array { elem: param_vir }, None);

        let param_sema = TypeId::from_raw(200);
        let array_param_sema = TypeId::from_raw(201);
        table.record_type_id(param_sema, param_vir);
        table.record_type_id(array_param_sema, array_of_param);

        let mut subs = FxHashMap::default();
        subs.insert(t_name, TypeId::from_raw(VirTypeId::I64.raw()));

        // Array<i64> not interned -> None.
        assert_eq!(table.lookup_substitute(array_param_sema, &subs), None);
    }

    #[test]
    fn substitute_function_type() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let func_of_param = table.intern(
            VirType::Function {
                params: vec![param_vir],
                ret: param_vir,
            },
            None,
        );
        let func_of_i64 = table.intern(
            VirType::Function {
                params: vec![VirTypeId::I64],
                ret: VirTypeId::I64,
            },
            None,
        );

        let param_sema = TypeId::from_raw(400);
        let func_param_sema = TypeId::from_raw(401);
        let func_i64_sema = TypeId::from_raw(402);
        table.record_type_id(param_sema, param_vir);
        table.record_type_id(func_param_sema, func_of_param);
        table.record_type_id(func_i64_sema, func_of_i64);

        let mut subs = FxHashMap::default();
        subs.insert(t_name, TypeId::from_raw(VirTypeId::I64.raw()));

        assert_eq!(
            table.lookup_substitute(func_param_sema, &subs),
            Some(func_i64_sema)
        );
    }

    #[test]
    fn substitute_nested_optional_array() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let opt_param = table.intern(VirType::Optional { inner: param_vir }, None);
        let arr_opt_param = table.intern(VirType::Array { elem: opt_param }, None);

        let opt_i64 = table.intern(
            VirType::Optional {
                inner: VirTypeId::I64,
            },
            None,
        );
        let arr_opt_i64 = table.intern(VirType::Array { elem: opt_i64 }, None);

        let param_sema = TypeId::from_raw(500);
        let arr_opt_param_sema = TypeId::from_raw(501);
        let arr_opt_i64_sema = TypeId::from_raw(502);
        table.record_type_id(param_sema, param_vir);
        table.record_type_id(TypeId::from_raw(503), opt_param);
        table.record_type_id(arr_opt_param_sema, arr_opt_param);
        table.record_type_id(TypeId::from_raw(504), opt_i64);
        table.record_type_id(arr_opt_i64_sema, arr_opt_i64);

        let mut subs = FxHashMap::default();
        subs.insert(t_name, TypeId::from_raw(VirTypeId::I64.raw()));

        assert_eq!(
            table.lookup_substitute(arr_opt_param_sema, &subs),
            Some(arr_opt_i64_sema)
        );
    }

    // ===== lookup_substitute_vir tests =====

    #[test]
    fn lookup_substitute_vir_empty_subs() {
        let table = VirTypeTable::new();
        let subs = FxHashMap::default();
        assert_eq!(
            table.lookup_substitute_vir(VirTypeId::I64, &subs),
            Some(VirTypeId::I64)
        );
    }

    #[test]
    fn lookup_substitute_vir_param() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);

        let i64_sema = TypeId::from_raw(VirTypeId::I64.raw());
        let mut subs = FxHashMap::default();
        subs.insert(t_name, i64_sema);

        assert_eq!(
            table.lookup_substitute_vir(param_vir, &subs),
            Some(VirTypeId::I64)
        );
    }

    #[test]
    fn lookup_substitute_vir_array_of_param() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let arr_param = table.intern(VirType::Array { elem: param_vir }, None);
        let _arr_i64 = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );

        let i64_sema = TypeId::from_raw(VirTypeId::I64.raw());
        let mut subs = FxHashMap::default();
        subs.insert(t_name, i64_sema);

        let result = table.lookup_substitute_vir(arr_param, &subs);
        assert!(result.is_some());
        assert!(matches!(
            table.get(result.unwrap()),
            VirType::Array { elem } if *elem == VirTypeId::I64
        ));
    }

    // ===== substitute_vir_ids tests =====

    #[test]
    fn substitute_vir_ids_empty_subs() {
        let table = VirTypeTable::new();
        let subs = FxHashMap::default();
        assert_eq!(
            table.substitute_vir_ids(VirTypeId::I64, &subs),
            Some(VirTypeId::I64)
        );
    }

    #[test]
    fn substitute_vir_ids_param() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);

        let mut subs: FxHashMap<NameId, VirTypeId> = FxHashMap::default();
        subs.insert(t_name, VirTypeId::I64);

        assert_eq!(
            table.substitute_vir_ids(param_vir, &subs),
            Some(VirTypeId::I64)
        );
    }

    #[test]
    fn substitute_vir_ids_array_of_param() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let arr_param = table.intern(VirType::Array { elem: param_vir }, None);
        let _arr_i64 = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );

        let mut subs: FxHashMap<NameId, VirTypeId> = FxHashMap::default();
        subs.insert(t_name, VirTypeId::I64);

        let result = table.substitute_vir_ids(arr_param, &subs);
        assert!(result.is_some());
        assert!(matches!(
            table.get(result.unwrap()),
            VirType::Array { elem } if *elem == VirTypeId::I64
        ));
    }

    #[test]
    fn substitute_vir_ids_param_not_in_subs() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let u_name = test_name(200);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);

        let mut subs: FxHashMap<NameId, VirTypeId> = FxHashMap::default();
        subs.insert(u_name, VirTypeId::I64);

        // T is not in subs (only U is), so returns None.
        assert_eq!(table.substitute_vir_ids(param_vir, &subs), None);
    }

    #[test]
    fn substitute_vir_ids_primitive_unchanged() {
        let table = VirTypeTable::new();
        let mut subs: FxHashMap<NameId, VirTypeId> = FxHashMap::default();
        subs.insert(test_name(100), VirTypeId::STRING);

        assert_eq!(
            table.substitute_vir_ids(VirTypeId::I64, &subs),
            Some(VirTypeId::I64)
        );
    }

    #[test]
    fn substitute_vir_ids_struct_type_args() {
        let mut table = VirTypeTable::new();
        let t_name = test_name(100);
        let param_vir = table.intern(VirType::Param { name: t_name }, None);
        let def = TypeDefId::new(5);

        let generic_struct = table.intern(
            VirType::Struct {
                def,
                type_args: vec![param_vir],
            },
            None,
        );
        let concrete_struct = table.intern(
            VirType::Struct {
                def,
                type_args: vec![VirTypeId::I64],
            },
            None,
        );

        let mut subs: FxHashMap<NameId, VirTypeId> = FxHashMap::default();
        subs.insert(t_name, VirTypeId::I64);

        assert_eq!(
            table.substitute_vir_ids(generic_struct, &subs),
            Some(concrete_struct)
        );
    }
}
