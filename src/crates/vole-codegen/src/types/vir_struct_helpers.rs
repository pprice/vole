#![allow(dead_code)]
// types/vir_struct_helpers.rs
//
// VirTypeTable-based struct/class field layout helpers for code generation.
//
// These functions replace the TypeArena-based equivalents in structs/helpers.rs
// for code paths that operate on VirTypeId (post-VIR-lowering).  Field types
// come from `VirTypeDef::field_types` (populated during VIR lowering), so
// no sema round-trip is needed for layout computation.
//
use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use vole_identity::{NameId, TypeDefId, TypeId, VirTypeId};
use vole_vir::entity_metadata::VirTypeDef;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{VirPrimitiveKind, VirType};

use super::vir_conversions::{
    vir_field_byte_size, vir_field_slot_count, vir_unwrap_class, vir_unwrap_class_or_struct,
    vir_unwrap_struct, vir_unwrap_union,
};

pub(crate) trait VirStructEntityLookup {
    fn is_sentinel_type_def(&self, type_def_id: TypeDefId) -> bool;

    /// Resolve a NameId to its last segment string.
    ///
    /// Used by `vir_get_field_slot_and_type_id` to match field names.
    fn last_segment(&self, name_id: NameId) -> Option<String>;

    /// Look up the VirTypeDef for a TypeDefId.
    ///
    /// Used by `vir_get_field_slot_and_type_id` to access generic field
    /// types and type params from VIR metadata.
    fn vir_type_def(&self, type_def_id: TypeDefId) -> Option<&VirTypeDef>;
}

impl VirStructEntityLookup for crate::analyzed::AnalyzedProgram {
    fn is_sentinel_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.entity_type_is_sentinel(type_def_id)
    }

    fn last_segment(&self, name_id: NameId) -> Option<String> {
        crate::analyzed::AnalyzedProgram::last_segment(self, name_id)
    }

    fn vir_type_def(&self, type_def_id: TypeDefId) -> Option<&VirTypeDef> {
        Some(self.type_def(type_def_id))
    }
}

#[cfg(test)]
impl VirStructEntityLookup for vole_sema::entity_registry::EntityRegistry {
    fn is_sentinel_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.get_type(type_def_id).kind.is_sentinel()
    }

    fn last_segment(&self, _name_id: NameId) -> Option<String> {
        // Tests use NameTable directly; not available here.
        None
    }

    fn vir_type_def(&self, _type_def_id: TypeDefId) -> Option<&VirTypeDef> {
        // Tests don't have VirTypeDef; they use the TestStructRegistry wrapper.
        None
    }
}

// ============================================================================
// Field type lookup from VirTypeDef
// ============================================================================

/// Look up the concrete `VirTypeId` for each field on a type definition.
///
/// Returns `Some(&[VirTypeId])` from `VirTypeDef::field_types`, or `None`
/// if the entity has no VirTypeDef (e.g. test-only EntityRegistry impls).
fn vir_field_types_for(
    type_def_id: TypeDefId,
    entities: &impl VirStructEntityLookup,
) -> Option<&[VirTypeId]> {
    entities
        .vir_type_def(type_def_id)
        .map(|td| td.field_types.as_slice())
}

// ============================================================================
// Payload union detection
// ============================================================================

/// Check if a VIR union type carries a payload (has at least one non-sentinel,
/// non-void variant).
///
/// Payload unions need 16 bytes (2 flat slots) when stored inline in structs.
/// Tag-only unions (all Nil/Done/Void/sentinel-struct variants) need 8 bytes.
///
/// Also recognizes `VirType::Optional { inner }` (the `T?` sugar for `T | nil`),
/// which always carries a payload when `inner` is non-sentinel and non-void.
pub(crate) fn vir_is_payload_union(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> bool {
    // Check explicit Union variants.
    if let Some(variants) = vir_unwrap_union(vir_ty, table) {
        return variants
            .iter()
            .any(|&v| !vir_is_sentinel_or_void(v, table, entities));
    }
    // Optional<T> is sugar for T | nil — payload if inner is non-sentinel, non-void.
    if let VirType::Optional { inner } = table.get(vir_ty) {
        return !vir_is_sentinel_or_void(*inner, table, entities);
    }
    false
}

/// Check if a VIR type is a sentinel (zero-field struct like nil/Done) or void.
///
/// Used by `vir_is_payload_union` to classify union variants.
fn vir_is_sentinel_or_void(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    _entities: &impl VirStructEntityLookup,
) -> bool {
    table.is_sentinel(vir_ty) || matches!(table.get(vir_ty), VirType::Void)
}

// ============================================================================
// Field slot and type lookup (VirTypeId-native)
//
// VirTypeId-native equivalent of `get_field_slot_and_type_id_cg` in
// structs/helpers.rs.  Takes VirTypeId, returns (slot, VirTypeId).
// ============================================================================

/// Get field slot and type for a field access, using VirTypeId throughout.
///
/// VirTypeId-native equivalent of `get_field_slot_and_type_id_cg` in
/// `structs/helpers.rs`.  Uses `VirTypeDef::generic_field_types` (VirTypeId
/// vec) and `VirTypeTable::substitute_vir_ids` for substitution, avoiding
/// the sema TypeId round-trip.
///
/// `func_subs` are the monomorphization substitutions from the function
/// context (`NameId -> TypeId`).  Note: `Cg::substitutions` now stores
/// VirTypeId-native maps; callers convert via `sema_substitutions()` when
/// calling this function.
pub(crate) fn vir_get_field_slot_and_type_id(
    vir_ty: VirTypeId,
    field_name: &str,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
    func_subs: Option<&FxHashMap<NameId, TypeId>>,
) -> CodegenResult<(usize, VirTypeId)> {
    // Resolve the input type through function-level substitutions.
    let resolved_vir = resolve_through_subs(vir_ty, table, func_subs);

    // Unwrap as class or struct.
    let (type_def_id, type_args) =
        vir_unwrap_class_or_struct(resolved_vir, table).ok_or_else(|| {
            CodegenError::type_mismatch("field access", "class or struct", "other type")
        })?;

    let type_def = entities
        .vir_type_def(type_def_id)
        .ok_or_else(|| CodegenError::not_found("VirTypeDef", "type"))?;

    let vir_field_types = type_def
        .generic_field_types
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_field_types", "type"))?;
    let field_names = type_def
        .generic_field_names
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_field_names", "type"))?;

    // Build combined substitution map (VirTypeId-native).
    let combined_subs = build_combined_vir_subs(type_def, type_args, table, func_subs);

    let is_class = vir_unwrap_class(resolved_vir, table).is_some();
    find_field_slot(
        field_name,
        field_names,
        vir_field_types,
        &combined_subs,
        is_class,
        table,
        entities,
    )
}

/// Resolve a VirTypeId through function-level substitutions.
///
/// If `func_subs` is provided and the type is a Param, substitute it.
/// Otherwise return the original type.
fn resolve_through_subs(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    func_subs: Option<&FxHashMap<NameId, TypeId>>,
) -> VirTypeId {
    if let Some(subs) = func_subs {
        table.lookup_substitute_vir(vir_ty, subs).unwrap_or(vir_ty)
    } else {
        vir_ty
    }
}

/// Build a combined VirTypeId-native substitution map from type args and
/// function-level monomorphization subs.
fn build_combined_vir_subs(
    type_def: &VirTypeDef,
    type_args: &[VirTypeId],
    table: &VirTypeTable,
    func_subs: Option<&FxHashMap<NameId, TypeId>>,
) -> FxHashMap<NameId, VirTypeId> {
    // Start with type_params -> type_args (already VirTypeId).
    let mut combined: FxHashMap<NameId, VirTypeId> = type_def
        .type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Merge function-level substitutions, converting TypeId -> VirTypeId.
    // Prefer concrete function subs over placeholder type args.
    if let Some(subs) = func_subs {
        for (&k, &v) in subs {
            let vir_v = table.lookup_type_id(v).unwrap_or(VirTypeId::UNKNOWN);
            let should_override = combined
                .get(&k)
                .is_some_and(|&existing| matches!(table.get(existing), VirType::Param { .. }));
            if should_override || !combined.contains_key(&k) {
                combined.insert(k, vir_v);
            }
        }
    }

    combined
}

/// Search fields by name and compute the (physical_slot, field_type) pair.
fn find_field_slot(
    field_name: &str,
    field_names: &[NameId],
    vir_field_types: &[VirTypeId],
    combined_subs: &FxHashMap<NameId, VirTypeId>,
    is_class: bool,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> CodegenResult<(usize, VirTypeId)> {
    let mut physical_slot = 0usize;
    for (idx, &field_name_id) in field_names.iter().enumerate() {
        let name = entities.last_segment(field_name_id);
        if name.as_deref() == Some(field_name) {
            let base_vir_ty = vir_field_types[idx];
            let field_vir_ty = table
                .substitute_vir_ids(base_vir_ty, combined_subs)
                .unwrap_or(base_vir_ty);
            let slot = if is_class { physical_slot } else { idx };
            return Ok((slot, field_vir_ty));
        }
        // Advance physical slot counter for class types.
        let ft = vir_field_types[idx];
        let resolved_ft = table.substitute_vir_ids(ft, combined_subs).unwrap_or(ft);
        physical_slot += if is_class {
            vir_field_slot_count(resolved_ft, table)
        } else {
            1
        };
    }

    Err(CodegenError::not_found(
        "field",
        format!("{} in type", field_name),
    ))
}

// ============================================================================
// Struct flat layout helpers
//
// Structs store all data inline, including nested structs. Each leaf field
// occupies one 8-byte "slot". The "flat slot count" recursively counts all
// leaf slots. Field byte offsets are computed by summing the flat sizes of
// all preceding fields.
// ============================================================================

/// Compute the flat 8-byte slot count for a single field type.
///
/// Nested structs are recursively expanded; wide types (i128) use 2 slots;
/// payload-carrying unions use 2 slots (tag + payload); all others use 1 slot.
pub(crate) fn vir_field_flat_slots_recursive(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> usize {
    if let Some(count) = vir_struct_flat_slot_count(vir_ty, table, entities) {
        return count;
    }
    if vir_is_payload_union(vir_ty, table, entities) {
        return 2;
    }
    // Wide types (i128) need 2 slots, all others need 1
    vir_field_slot_count(vir_ty, table)
}

/// Compute the total flat 8-byte slot count for a struct type.
///
/// Recursively expands nested struct fields. Returns `None` if the type is
/// not a struct.
pub(crate) fn vir_struct_flat_slot_count(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> Option<usize> {
    let (type_def_id, _type_args) = vir_unwrap_struct(vir_ty, table)?;

    let field_vir_types = vir_field_types_for(type_def_id, entities)?;
    let mut total = 0usize;
    for &field_vir in field_vir_types {
        total += vir_field_flat_slots_recursive(field_vir, table, entities);
    }
    Some(total)
}

/// Compute the byte offset of field `slot` within a struct.
///
/// Accounts for nested struct fields that occupy more than one 8-byte slot.
/// Returns `None` if the type is not a struct or `slot` is out of range.
pub(crate) fn vir_struct_field_byte_offset(
    vir_ty: VirTypeId,
    slot: usize,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> Option<i32> {
    let (type_def_id, _type_args) = vir_unwrap_struct(vir_ty, table)?;

    let field_vir_types = vir_field_types_for(type_def_id, entities)?;
    if slot > field_vir_types.len() {
        return None;
    }

    let mut offset = 0i32;
    for &field_vir in field_vir_types.iter().take(slot) {
        let slots = vir_field_flat_slots_recursive(field_vir, table, entities);
        offset += (slots as i32) * 8;
    }
    Some(offset)
}

/// Total byte size of a struct, accounting for nested struct fields.
///
/// Returns `None` if the type is not a struct.
pub(crate) fn vir_struct_total_byte_size(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> Option<u32> {
    vir_struct_flat_slot_count(vir_ty, table, entities).map(|n| (n as u32) * 8)
}

// ============================================================================
// Leaf type helpers for struct equality comparison
// ============================================================================

/// Map a VIR leaf type to its Cranelift type for equality comparison.
///
/// Wide types (i128, f128) map to I128/F128. Float types map to F32/F64
/// so callers can use `fcmp` instead of `icmp`. All other types are
/// compared as I64.
///
/// Note: F128 is stored as `VirType::Unknown` in the type table (no
/// `VirPrimitiveKind::F128` yet), so it must be checked by constant
/// before the table lookup.
fn vir_leaf_cranelift_type(vir_ty: VirTypeId, table: &VirTypeTable) -> Type {
    // F128 is registered as VirType::Unknown (wide_layout) - check by ID.
    if vir_ty == VirTypeId::F128 {
        return types::F128;
    }
    match table.get(vir_ty) {
        VirType::Primitive(VirPrimitiveKind::F32) => types::F32,
        VirType::Primitive(VirPrimitiveKind::F64) => types::F64,
        VirType::Primitive(VirPrimitiveKind::I128) => types::I128,
        _ => types::I64,
    }
}

/// Collect (byte_offset, cranelift_type) for every leaf slot in a struct,
/// recursively flattening nested struct fields.
///
/// Wide types produce a single entry (callers issue one wide load+compare).
/// Returns `None` if `vir_ty` is not a struct type.
pub(crate) fn vir_struct_flat_field_cranelift_types(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> Option<Vec<(i32, Type)>> {
    let (type_def_id, _type_args) = vir_unwrap_struct(vir_ty, table)?;

    let field_vir_types = vir_field_types_for(type_def_id, entities)?;
    let mut result = Vec::new();
    let mut offset = 0i32;
    for &field_vir in field_vir_types {
        vir_collect_leaf_slots(field_vir, table, entities, &mut offset, &mut result);
    }
    Some(result)
}

/// Recursively collect leaf (offset, cranelift_type) entries for a VIR field.
///
/// Nested structs are flattened; payload unions produce 2 I64 entries;
/// leaf types produce a single entry.
fn vir_collect_leaf_slots(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
    offset: &mut i32,
    out: &mut Vec<(i32, Type)>,
) {
    // Recursively flatten nested structs
    if let Some((nested_def, _nested_args)) = vir_unwrap_struct(vir_ty, table) {
        if let Some(nested_field_types) = vir_field_types_for(nested_def, entities) {
            for &field_vir in nested_field_types {
                vir_collect_leaf_slots(field_vir, table, entities, offset, out);
            }
        }
        return;
    }
    // Payload-carrying unions: 2 x I64 (tag + payload)
    if vir_is_payload_union(vir_ty, table, entities) {
        out.push((*offset, types::I64));
        *offset += 8;
        out.push((*offset, types::I64));
        *offset += 8;
        return;
    }
    // Leaf field: single entry
    let cl_type = vir_leaf_cranelift_type(vir_ty, table);
    out.push((*offset, cl_type));
    let byte_size = vir_field_byte_size(vir_ty, table) as i32;
    *offset += byte_size;
}

// ============================================================================
// Field value conversion
// ============================================================================

/// Convert a raw i64 field value to the appropriate Cranelift type,
/// using VirTypeId for dispatch instead of TypeArena.
///
/// This is the VirTypeTable-based equivalent of `convert_field_value_id`
/// in `structs/helpers.rs`.
pub(crate) fn vir_convert_field_value(
    builder: &mut FunctionBuilder,
    raw_value: Value,
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> (Value, Type) {
    match table.get(vir_ty) {
        VirType::Primitive(VirPrimitiveKind::F64) => {
            let fval = builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_value);
            (fval, types::F64)
        }
        VirType::Primitive(VirPrimitiveKind::F32) => {
            let i32_val = builder.ins().ireduce(types::I32, raw_value);
            let fval = builder.ins().bitcast(types::F32, MemFlags::new(), i32_val);
            (fval, types::F32)
        }
        VirType::Primitive(VirPrimitiveKind::Bool) => {
            let bval = builder.ins().ireduce(types::I8, raw_value);
            (bval, types::I8)
        }
        VirType::Primitive(VirPrimitiveKind::I8 | VirPrimitiveKind::U8) => {
            let val = builder.ins().ireduce(types::I8, raw_value);
            (val, types::I8)
        }
        VirType::Primitive(VirPrimitiveKind::I16 | VirPrimitiveKind::U16) => {
            let val = builder.ins().ireduce(types::I16, raw_value);
            (val, types::I16)
        }
        VirType::Primitive(VirPrimitiveKind::I32 | VirPrimitiveKind::U32) => {
            let val = builder.ins().ireduce(types::I32, raw_value);
            (val, types::I32)
        }
        // Pointers stay as i64 (string, array, class, etc.)
        VirType::Primitive(VirPrimitiveKind::String)
        | VirType::Array { .. }
        | VirType::Class { .. } => (raw_value, types::I64),
        _ => (raw_value, types::I64),
    }
}

// ============================================================================
// Unit tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use vole_identity::TypeDefId;
    use vole_sema::entity_registry::EntityRegistry;
    use vole_vir::type_table::VirTypeTable;

    fn test_table() -> VirTypeTable {
        VirTypeTable::new()
    }

    // -----------------------------------------------------------------------
    // Payload union detection
    // -----------------------------------------------------------------------

    #[test]
    fn payload_union_with_i64_variant() {
        let mut table = test_table();
        let entities = EntityRegistry::new();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::NIL],
            },
            None,
        );
        // i64 is a payload variant, nil is sentinel -> payload union
        assert!(vir_is_payload_union(union_ty, &table, &entities));
    }

    #[test]
    fn tag_only_union_nil_done() {
        let mut table = test_table();
        let entities = EntityRegistry::new();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::NIL, VirTypeId::DONE],
            },
            None,
        );
        // Both nil and done are sentinels -> tag-only
        assert!(!vir_is_payload_union(union_ty, &table, &entities));
    }

    #[test]
    fn non_union_is_not_payload_union() {
        let table = test_table();
        let entities = EntityRegistry::new();
        assert!(!vir_is_payload_union(VirTypeId::I64, &table, &entities));
    }

    // -----------------------------------------------------------------------
    // Struct layout helpers
    // -----------------------------------------------------------------------

    /// Test wrapper that combines an EntityRegistry with VirTypeDef metadata.
    struct TestStructRegistry {
        registry: EntityRegistry,
        type_defs: FxHashMap<TypeDefId, VirTypeDef>,
    }

    impl VirStructEntityLookup for TestStructRegistry {
        fn is_sentinel_type_def(&self, type_def_id: TypeDefId) -> bool {
            self.registry.get_type(type_def_id).kind.is_sentinel()
        }

        fn last_segment(&self, _name_id: NameId) -> Option<String> {
            None
        }

        fn vir_type_def(&self, type_def_id: TypeDefId) -> Option<&VirTypeDef> {
            self.type_defs.get(&type_def_id)
        }
    }

    /// Create a test struct type with fields and VirTypeDef metadata.
    fn make_struct_registry(
        field_sema_types: &[TypeId],
        field_vir_types: &[VirTypeId],
    ) -> (TestStructRegistry, TypeDefId) {
        use vole_identity::NameTable;
        use vole_sema::entity_defs::TypeDefKind;
        use vole_vir::entity_metadata::VirTypeDefKind;

        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["TestStruct"]);

        let mut registry = EntityRegistry::new();
        let type_def_id = registry.register_type(type_name, TypeDefKind::Struct, main_mod);

        let mut field_ids = Vec::new();
        for (i, &ty) in field_sema_types.iter().enumerate() {
            let field_name_str = format!("f{i}");
            let field_name = names.intern_raw(builtin_mod, &[&field_name_str]);
            let full_name = names.intern_raw(main_mod, &["TestStruct", &field_name_str]);
            let fid = registry.register_field(type_def_id, field_name, full_name, ty, i);
            field_ids.push(fid);
        }

        let vir_td = VirTypeDef {
            id: type_def_id,
            name_id: type_name,
            kind: VirTypeDefKind::Struct,
            fields: field_ids,
            field_types: field_vir_types.to_vec(),
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: main_mod,
            is_generic: false,
            generic_field_types: None,
            sema_generic_field_types: None,
            generic_field_names: None,
        };

        let mut type_defs = FxHashMap::default();
        type_defs.insert(type_def_id, vir_td);

        (
            TestStructRegistry {
                registry,
                type_defs,
            },
            type_def_id,
        )
    }

    #[test]
    fn struct_flat_slot_count_two_i64_fields() {
        let sema_i64 = TypeId::I64;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i64, sema_i64], &[VirTypeId::I64, VirTypeId::I64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        assert_eq!(
            vir_struct_flat_slot_count(struct_ty, &table, &entities),
            Some(2)
        );
    }

    #[test]
    fn struct_flat_slot_count_with_wide_field() {
        let sema_i64 = TypeId::I64;
        let sema_i128 = TypeId::I128;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i64, sema_i128], &[VirTypeId::I64, VirTypeId::I128]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        // i64 = 1 slot, i128 = 2 slots -> 3 total
        assert_eq!(
            vir_struct_flat_slot_count(struct_ty, &table, &entities),
            Some(3)
        );
    }

    #[test]
    fn struct_flat_slot_count_returns_none_for_non_struct() {
        let table = test_table();
        let entities = EntityRegistry::new();
        assert!(vir_struct_flat_slot_count(VirTypeId::I64, &table, &entities).is_none());
    }

    #[test]
    fn struct_field_byte_offset_two_i64() {
        let sema_i64 = TypeId::I64;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i64, sema_i64], &[VirTypeId::I64, VirTypeId::I64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        assert_eq!(
            vir_struct_field_byte_offset(struct_ty, 0, &table, &entities),
            Some(0)
        );
        assert_eq!(
            vir_struct_field_byte_offset(struct_ty, 1, &table, &entities),
            Some(8)
        );
    }

    #[test]
    fn struct_field_byte_offset_with_wide() {
        let sema_i128 = TypeId::I128;
        let sema_i64 = TypeId::I64;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i128, sema_i64], &[VirTypeId::I128, VirTypeId::I64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        // First field (i128) at offset 0, second field after 16 bytes (2 slots)
        assert_eq!(
            vir_struct_field_byte_offset(struct_ty, 0, &table, &entities),
            Some(0)
        );
        assert_eq!(
            vir_struct_field_byte_offset(struct_ty, 1, &table, &entities),
            Some(16)
        );
    }

    #[test]
    fn struct_total_byte_size_two_i64() {
        let sema_i64 = TypeId::I64;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i64, sema_i64], &[VirTypeId::I64, VirTypeId::I64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        assert_eq!(
            vir_struct_total_byte_size(struct_ty, &table, &entities),
            Some(16)
        );
    }

    #[test]
    fn struct_flat_field_cranelift_types_two_i64() {
        let sema_i64 = TypeId::I64;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i64, sema_i64], &[VirTypeId::I64, VirTypeId::I64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        let fields = vir_struct_flat_field_cranelift_types(struct_ty, &table, &entities).unwrap();
        assert_eq!(fields, vec![(0, types::I64), (8, types::I64)]);
    }

    #[test]
    fn struct_flat_field_cranelift_types_with_f64() {
        let sema_i64 = TypeId::I64;
        let sema_f64 = TypeId::F64;
        let (entities, type_def_id) =
            make_struct_registry(&[sema_i64, sema_f64], &[VirTypeId::I64, VirTypeId::F64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        let fields = vir_struct_flat_field_cranelift_types(struct_ty, &table, &entities).unwrap();
        assert_eq!(fields, vec![(0, types::I64), (8, types::F64)]);
    }

    #[test]
    fn struct_flat_field_cranelift_types_returns_none_for_non_struct() {
        let table = test_table();
        let entities = EntityRegistry::new();
        assert!(vir_struct_flat_field_cranelift_types(VirTypeId::I64, &table, &entities).is_none());
    }

    #[test]
    fn field_flat_slots_recursive_for_primitives() {
        let table = test_table();
        let entities = EntityRegistry::new();
        assert_eq!(
            vir_field_flat_slots_recursive(VirTypeId::I64, &table, &entities),
            1
        );
        assert_eq!(
            vir_field_flat_slots_recursive(VirTypeId::I128, &table, &entities),
            2
        );
        assert_eq!(
            vir_field_flat_slots_recursive(VirTypeId::F64, &table, &entities),
            1
        );
    }

    #[test]
    fn leaf_cranelift_type_mapping() {
        let table = test_table();
        assert_eq!(vir_leaf_cranelift_type(VirTypeId::F32, &table), types::F32);
        assert_eq!(vir_leaf_cranelift_type(VirTypeId::F64, &table), types::F64);
        assert_eq!(
            vir_leaf_cranelift_type(VirTypeId::F128, &table),
            types::F128
        );
        assert_eq!(
            vir_leaf_cranelift_type(VirTypeId::I128, &table),
            types::I128
        );
        assert_eq!(vir_leaf_cranelift_type(VirTypeId::I64, &table), types::I64);
        assert_eq!(
            vir_leaf_cranelift_type(VirTypeId::STRING, &table),
            types::I64
        );
        assert_eq!(vir_leaf_cranelift_type(VirTypeId::BOOL, &table), types::I64);
    }

    // -----------------------------------------------------------------------
    // vir_get_field_slot_and_type_id tests
    // -----------------------------------------------------------------------

    /// Test helper that holds VirTypeDef data and a NameTable for field name
    /// resolution, implementing VirStructEntityLookup.
    struct TestVirEntities {
        registry: EntityRegistry,
        type_defs: FxHashMap<TypeDefId, VirTypeDef>,
        names: vole_identity::NameTable,
    }

    impl VirStructEntityLookup for TestVirEntities {
        fn is_sentinel_type_def(&self, type_def_id: TypeDefId) -> bool {
            self.registry.get_type(type_def_id).kind.is_sentinel()
        }

        fn last_segment(&self, name_id: NameId) -> Option<String> {
            self.names.last_segment_str(name_id)
        }

        fn vir_type_def(&self, type_def_id: TypeDefId) -> Option<&VirTypeDef> {
            self.type_defs.get(&type_def_id)
        }
    }

    /// Build test entities with a struct type, field names, and VirTypeDef.
    fn make_vir_test_entities(
        field_names: &[&str],
        field_sema_types: &[TypeId],
        field_vir_types: &[VirTypeId],
    ) -> (TestVirEntities, TypeDefId) {
        use vole_identity::NameTable;
        use vole_sema::entity_defs::TypeDefKind;
        use vole_vir::entity_metadata::VirTypeDefKind;

        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["TestStruct"]);

        let mut registry = EntityRegistry::new();
        let type_def_id = registry.register_type(type_name, TypeDefKind::Struct, main_mod);

        let mut generic_field_names = Vec::new();
        for (i, (&fname, &sema_ty)) in field_names.iter().zip(field_sema_types.iter()).enumerate() {
            let field_name = names.intern_raw(builtin_mod, &[fname]);
            let full_name = names.intern_raw(main_mod, &["TestStruct", fname]);
            registry.register_field(type_def_id, field_name, full_name, sema_ty, i);
            generic_field_names.push(field_name);
        }

        let vir_type_def = VirTypeDef {
            id: type_def_id,
            name_id: type_name,
            kind: VirTypeDefKind::Struct,
            fields: vec![],
            field_types: field_vir_types.to_vec(),
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: main_mod,
            is_generic: false,
            generic_field_types: Some(field_vir_types.to_vec()),
            sema_generic_field_types: Some(field_sema_types.to_vec()),
            generic_field_names: Some(generic_field_names),
        };

        let mut type_defs = FxHashMap::default();
        type_defs.insert(type_def_id, vir_type_def);

        (
            TestVirEntities {
                registry,
                type_defs,
                names,
            },
            type_def_id,
        )
    }

    #[test]
    fn vir_get_field_struct_two_i64() {
        let (entities, type_def_id) = make_vir_test_entities(
            &["x", "y"],
            &[TypeId::I64, TypeId::I64],
            &[VirTypeId::I64, VirTypeId::I64],
        );

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        // First field "x" at slot 0
        let (slot, ty) =
            vir_get_field_slot_and_type_id(struct_ty, "x", &table, &entities, None).unwrap();
        assert_eq!(slot, 0);
        assert_eq!(ty, VirTypeId::I64);

        // Second field "y" at slot 1
        let (slot, ty) =
            vir_get_field_slot_and_type_id(struct_ty, "y", &table, &entities, None).unwrap();
        assert_eq!(slot, 1);
        assert_eq!(ty, VirTypeId::I64);
    }

    #[test]
    fn vir_get_field_not_found() {
        let (entities, type_def_id) =
            make_vir_test_entities(&["x"], &[TypeId::I64], &[VirTypeId::I64]);

        let mut table = test_table();
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        assert!(vir_get_field_slot_and_type_id(struct_ty, "z", &table, &entities, None,).is_err());
    }

    #[test]
    fn vir_get_field_non_struct_type() {
        let entities = TestVirEntities {
            registry: EntityRegistry::new(),
            type_defs: FxHashMap::default(),
            names: vole_identity::NameTable::new(),
        };
        let table = test_table();

        assert!(
            vir_get_field_slot_and_type_id(VirTypeId::I64, "x", &table, &entities, None,).is_err()
        );
    }

    #[test]
    fn vir_get_field_class_with_wide_type() {
        use vole_identity::NameTable;
        use vole_sema::entity_defs::TypeDefKind;
        use vole_vir::entity_metadata::VirTypeDefKind;

        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["TestClass"]);

        let mut registry = EntityRegistry::new();
        let type_def_id = registry.register_type(type_name, TypeDefKind::Class, main_mod);

        let field_a_name = names.intern_raw(builtin_mod, &["a"]);
        let field_a_full = names.intern_raw(main_mod, &["TestClass", "a"]);
        registry.register_field(type_def_id, field_a_name, field_a_full, TypeId::I128, 0);

        let field_b_name = names.intern_raw(builtin_mod, &["b"]);
        let field_b_full = names.intern_raw(main_mod, &["TestClass", "b"]);
        registry.register_field(type_def_id, field_b_name, field_b_full, TypeId::I64, 1);

        let vir_type_def = VirTypeDef {
            id: type_def_id,
            name_id: type_name,
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![VirTypeId::I128, VirTypeId::I64],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: main_mod,
            is_generic: false,
            generic_field_types: Some(vec![VirTypeId::I128, VirTypeId::I64]),
            sema_generic_field_types: Some(vec![TypeId::I128, TypeId::I64]),
            generic_field_names: Some(vec![field_a_name, field_b_name]),
        };

        let mut type_defs = FxHashMap::default();
        type_defs.insert(type_def_id, vir_type_def);

        let entities = TestVirEntities {
            registry,
            type_defs,
            names,
        };

        let mut table = test_table();
        let class_ty = table.intern(
            VirType::Class {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        // Field "a" (i128) at physical slot 0
        let (slot, ty) =
            vir_get_field_slot_and_type_id(class_ty, "a", &table, &entities, None).unwrap();
        assert_eq!(slot, 0);
        assert_eq!(ty, VirTypeId::I128);

        // Field "b" (i64) at physical slot 2 (i128 takes 2 slots)
        let (slot, ty) =
            vir_get_field_slot_and_type_id(class_ty, "b", &table, &entities, None).unwrap();
        assert_eq!(slot, 2);
        assert_eq!(ty, VirTypeId::I64);
    }

    #[test]
    fn vir_get_field_generic_substitution() {
        use vole_identity::NameTable;
        use vole_sema::entity_defs::TypeDefKind;
        use vole_vir::entity_metadata::VirTypeDefKind;

        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["Wrapper"]);
        let t_param = names.intern_raw(builtin_mod, &["T"]);

        let mut registry = EntityRegistry::new();
        let type_def_id = registry.register_type(type_name, TypeDefKind::Struct, main_mod);

        let field_val_name = names.intern_raw(builtin_mod, &["val"]);
        let field_val_full = names.intern_raw(main_mod, &["Wrapper", "val"]);
        // sema type for the generic field is a type param placeholder
        let sema_param_ty = TypeId::from_raw(500);
        registry.register_field(
            type_def_id,
            field_val_name,
            field_val_full,
            sema_param_ty,
            0,
        );

        let mut table = test_table();
        // Intern the Param type for T
        let param_vir = table.intern(VirType::Param { name: t_param }, None);

        let vir_type_def = VirTypeDef {
            id: type_def_id,
            name_id: type_name,
            kind: VirTypeDefKind::Struct,
            fields: vec![],
            field_types: vec![param_vir],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![t_param],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: main_mod,
            is_generic: true,
            generic_field_types: Some(vec![param_vir]),
            sema_generic_field_types: Some(vec![sema_param_ty]),
            generic_field_names: Some(vec![field_val_name]),
        };

        let mut type_defs = FxHashMap::default();
        type_defs.insert(type_def_id, vir_type_def);

        let entities = TestVirEntities {
            registry,
            type_defs,
            names,
        };

        // Concrete instantiation: Wrapper<i64>
        let struct_ty = table.intern(
            VirType::Struct {
                def: type_def_id,
                type_args: vec![VirTypeId::I64],
            },
            None,
        );

        // Field "val" should resolve to i64 after substitution
        let (slot, ty) =
            vir_get_field_slot_and_type_id(struct_ty, "val", &table, &entities, None).unwrap();
        assert_eq!(slot, 0);
        assert_eq!(ty, VirTypeId::I64);
    }
}
