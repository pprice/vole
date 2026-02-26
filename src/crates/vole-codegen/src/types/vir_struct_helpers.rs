// types/vir_struct_helpers.rs
//
// VirTypeTable-based struct/class field layout helpers for code generation.
//
// These functions replace the TypeArena-based equivalents in structs/helpers.rs
// for code paths that operate on VirTypeId (post-VIR-lowering).  They still
// require EntityRegistry access for field lists (TypeDefId -> field
// names/types), but all type queries go through VirTypeTable.
//
// Many functions here are not yet called outside tests because callers are
// migrated incrementally (vol-y01m).
#![allow(dead_code)]

use cranelift::prelude::*;

use vole_identity::{TypeId, VirTypeId};
use vole_sema::EntityRegistry;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{VirPrimitiveKind, VirType};

use super::vir_conversions::{
    vir_field_byte_size, vir_field_slot_count, vir_unwrap_struct, vir_unwrap_union,
};

// ============================================================================
// Payload union detection
// ============================================================================

/// Check if a VIR union type carries a payload (has at least one non-sentinel,
/// non-void variant).
///
/// Payload unions need 16 bytes (2 flat slots) when stored inline in structs.
/// Tag-only unions (all Nil/Done/Void/sentinel-struct variants) need 8 bytes.
pub(crate) fn vir_is_payload_union(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &EntityRegistry,
) -> bool {
    let Some(variants) = vir_unwrap_union(vir_ty, table) else {
        return false;
    };
    variants
        .iter()
        .any(|&v| !vir_is_sentinel_or_void(v, table, entities))
}

/// Check if a VIR type is a sentinel (zero-field struct like nil/Done) or void.
///
/// Used by `vir_is_payload_union` to classify union variants.
fn vir_is_sentinel_or_void(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &EntityRegistry,
) -> bool {
    match table.get(vir_ty) {
        VirType::Nil | VirType::Done | VirType::Void => true,
        VirType::Struct { def, .. } => entities.get_type(*def).kind.is_sentinel(),
        _ => false,
    }
}

fn sema_to_vir_hint(sema_ty: TypeId) -> VirTypeId {
    // Temporary bridge after removing VirTypeTable's sema TypeId cache.
    // This helper intentionally maps only reserved IDs by index; dynamic
    // IDs fall back to UNKNOWN until field metadata is VirTypeId-native
    // in N279-C.
    if sema_ty.raw() < VirTypeId::FIRST_DYNAMIC {
        VirTypeId::from_raw(sema_ty.raw())
    } else {
        VirTypeId::UNKNOWN
    }
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
    entities: &EntityRegistry,
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
    entities: &EntityRegistry,
) -> Option<usize> {
    let (type_def_id, _type_args) = vir_unwrap_struct(vir_ty, table)?;

    let mut total = 0usize;
    for field_id in entities.fields_on_type(type_def_id) {
        let field = entities.get_field(field_id);
        let field_vir = sema_to_vir_hint(field.ty);
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
    entities: &EntityRegistry,
) -> Option<i32> {
    let (type_def_id, _type_args) = vir_unwrap_struct(vir_ty, table)?;

    let fields: Vec<_> = entities.fields_on_type(type_def_id).collect();
    if slot > fields.len() {
        return None;
    }

    let mut offset = 0i32;
    for &field_id in fields.iter().take(slot) {
        let field = entities.get_field(field_id);
        let field_vir = sema_to_vir_hint(field.ty);
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
    entities: &EntityRegistry,
) -> Option<u32> {
    vir_struct_flat_slot_count(vir_ty, table, entities).map(|n| (n as u32) * 8)
}

// ============================================================================
// Leaf type helpers for struct equality comparison
// ============================================================================

/// Map a VIR leaf type to its Cranelift type for equality comparison.
///
/// Wide types (i128) map to I128. Float types map to F32/F64 so callers
/// can use `fcmp` instead of `icmp`. All other types are compared as I64.
fn vir_leaf_cranelift_type(vir_ty: VirTypeId, table: &VirTypeTable) -> Type {
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
    entities: &EntityRegistry,
) -> Option<Vec<(i32, Type)>> {
    let (type_def_id, _type_args) = vir_unwrap_struct(vir_ty, table)?;

    let mut result = Vec::new();
    let mut offset = 0i32;
    for field_id in entities.fields_on_type(type_def_id) {
        let field = entities.get_field(field_id);
        let field_vir = sema_to_vir_hint(field.ty);
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
    entities: &EntityRegistry,
    offset: &mut i32,
    out: &mut Vec<(i32, Type)>,
) {
    // Recursively flatten nested structs
    if let Some((nested_def, _nested_args)) = vir_unwrap_struct(vir_ty, table) {
        for field_id in entities.fields_on_type(nested_def) {
            let field = entities.get_field(field_id);
            let field_vir = sema_to_vir_hint(field.ty);
            vir_collect_leaf_slots(field_vir, table, entities, offset, out);
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
    // Struct layout helpers (with EntityRegistry)
    // -----------------------------------------------------------------------

    /// Create a test EntityRegistry with a struct type and fields.
    fn make_struct_registry(field_type_ids: &[TypeId]) -> (EntityRegistry, TypeDefId) {
        use vole_identity::NameTable;
        use vole_sema::entity_defs::TypeDefKind;

        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["TestStruct"]);

        let mut registry = EntityRegistry::new();
        let type_def_id = registry.register_type(type_name, TypeDefKind::Struct, main_mod);

        for (i, &ty) in field_type_ids.iter().enumerate() {
            let field_name_str = format!("f{i}");
            let field_name = names.intern_raw(builtin_mod, &[&field_name_str]);
            let full_name = names.intern_raw(main_mod, &["TestStruct", &field_name_str]);
            registry.register_field(type_def_id, field_name, full_name, ty, i);
        }

        (registry, type_def_id)
    }

    #[test]
    fn struct_flat_slot_count_two_i64_fields() {
        let sema_i64 = TypeId::I64;
        let (entities, type_def_id) = make_struct_registry(&[sema_i64, sema_i64]);

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
        let (entities, type_def_id) = make_struct_registry(&[sema_i64, sema_i128]);

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
        let (entities, type_def_id) = make_struct_registry(&[sema_i64, sema_i64]);

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
        let (entities, type_def_id) = make_struct_registry(&[sema_i128, sema_i64]);

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
        let (entities, type_def_id) = make_struct_registry(&[sema_i64, sema_i64]);

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
        let (entities, type_def_id) = make_struct_registry(&[sema_i64, sema_i64]);

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
        let (entities, type_def_id) = make_struct_registry(&[sema_i64, sema_f64]);

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
}
