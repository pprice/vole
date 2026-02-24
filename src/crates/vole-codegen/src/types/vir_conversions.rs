// types/vir_conversions.rs
//
// VirTypeTable-based type conversion utilities for code generation.
//
// These functions replace the TypeArena-based equivalents in conversions.rs
// for code paths that operate on VirTypeId (post-VIR-lowering).  The old
// functions remain for callers that still use sema TypeId directly.
//
// Many functions here are not yet called outside tests because callers are
// migrated incrementally (vol-uofd, vol-y01m, vol-ubd5).
#![allow(dead_code)]

use cranelift::prelude::*;

use vole_identity::VirTypeId;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{StorageClass, VirPrimitiveKind, VirType};

/// Map a `VirTypeId` to a Cranelift type using the VIR type table.
///
/// Uses `VirType` variant + `VirPrimitiveKind` for precise width mapping
/// (I8, I16, I32, etc.), falling back to `StorageClass` for compound types.
pub(crate) fn vir_type_to_cranelift(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    pointer_type: Type,
) -> Type {
    match table.get(vir_ty) {
        VirType::Primitive(kind) => vir_primitive_to_cranelift(*kind, pointer_type),

        // Heap-allocated RC types: class instances, arrays, iterators.
        VirType::Class { .. } | VirType::Array { .. } | VirType::RuntimeIterator { .. } => {
            pointer_type
        }

        // Interfaces are fat pointers to RC implementors.
        VirType::Interface { .. } => pointer_type,

        // Structs are value types passed by pointer.
        VirType::Struct { .. } => pointer_type,

        // Functions/closures are RC heap objects.
        VirType::Function { .. } => pointer_type,

        // Error types are heap-allocated.
        VirType::Error { .. } => pointer_type,

        // Unions, optionals, fallibles: heap or stack pointers.
        VirType::Union { .. } | VirType::Optional { .. } | VirType::Fallible { .. } => pointer_type,

        // Tuples, fixed arrays: stack-allocated composites via pointer.
        VirType::Tuple { .. } | VirType::FixedArray { .. } => pointer_type,

        // Range: 16 bytes (start + end), but represented as pointer.
        VirType::Range => pointer_type,

        // Void: no meaningful value, I64 placeholder for uniform call ABI.
        VirType::Void => types::I64,

        // Nil and Done: sentinel types, zero-sized (I8 tag placeholder).
        VirType::Nil | VirType::Done => types::I8,

        // Never: bottom type. Pointer placeholder for unreachable branches.
        VirType::Never => pointer_type,

        // MetaType: heap pointer.
        VirType::MetaType => pointer_type,

        // Unknown: boxed TaggedValue, heap pointer.
        VirType::Unknown => pointer_type,

        // Unresolved generic parameter: pointer-erased.
        VirType::Param { .. } => pointer_type,
    }
}

/// Map a `VirPrimitiveKind` to its Cranelift type.
fn vir_primitive_to_cranelift(kind: VirPrimitiveKind, pointer_type: Type) -> Type {
    match kind {
        VirPrimitiveKind::I8 | VirPrimitiveKind::U8 => types::I8,
        VirPrimitiveKind::I16 | VirPrimitiveKind::U16 => types::I16,
        VirPrimitiveKind::I32 | VirPrimitiveKind::U32 => types::I32,
        VirPrimitiveKind::I64 | VirPrimitiveKind::U64 => types::I64,
        VirPrimitiveKind::I128 => types::I128,
        VirPrimitiveKind::F32 => types::F32,
        VirPrimitiveKind::F64 => types::F64,
        VirPrimitiveKind::Bool => types::I8,
        VirPrimitiveKind::String => pointer_type,
        VirPrimitiveKind::Handle => pointer_type,
    }
}

/// Check if a `VirTypeId` is a wide type (requires 2 register slots).
pub(crate) fn vir_is_wide(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    table.get_layout(vir_ty).is_some_and(|l| l.is_wide)
}

/// Check if a `VirTypeId` is reference-counted (needs RC management).
pub(crate) fn vir_is_rc(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    table.get_layout(vir_ty).is_some_and(|l| l.is_rc)
}

/// Check if a `VirTypeId` lives on the heap.
pub(crate) fn vir_is_heap(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    table.get_layout(vir_ty).is_some_and(|l| l.is_heap)
}

/// Get the register slot count for a `VirTypeId`.
///
/// Returns 0 for void, 1 for most types, 2 for wide types (i128).
pub(crate) fn vir_slot_count(vir_ty: VirTypeId, table: &VirTypeTable) -> usize {
    table
        .get_layout(vir_ty)
        .map_or(1, |l| l.slot_count as usize)
}

/// Get the `StorageClass` for a `VirTypeId`.
///
/// Returns `StorageClass::Pointer` as fallback if no layout is available
/// (should not happen post-monomorphization).
pub(crate) fn vir_storage_class(vir_ty: VirTypeId, table: &VirTypeTable) -> StorageClass {
    table
        .get_layout(vir_ty)
        .map_or(StorageClass::Pointer, |l| l.storage)
}

/// Get the byte size of a field for a `VirTypeId`: 16 for wide types, 8 for all others.
pub(crate) fn vir_field_byte_size(vir_ty: VirTypeId, table: &VirTypeTable) -> u32 {
    if vir_is_wide(vir_ty, table) { 16 } else { 8 }
}

/// Get the slot count of a field for a `VirTypeId`: 2 for wide types, 1 for all others.
pub(crate) fn vir_field_slot_count(vir_ty: VirTypeId, table: &VirTypeTable) -> usize {
    if vir_is_wide(vir_ty, table) { 2 } else { 1 }
}

/// Check if a `VirTypeId` is an unsigned integer primitive.
pub(crate) fn vir_is_unsigned(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Primitive(kind) if kind.is_unsigned())
}

// ============================================================================
// Unit tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use vole_vir::type_table::VirTypeTable;
    use vole_vir::types::VirTypeLayout;

    fn test_table() -> VirTypeTable {
        VirTypeTable::new()
    }

    // -----------------------------------------------------------------------
    // vir_type_to_cranelift
    // -----------------------------------------------------------------------

    #[test]
    fn cranelift_i8() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(VirTypeId::I8, &table, ptr), types::I8);
    }

    #[test]
    fn cranelift_i16() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::I16, &table, ptr),
            types::I16
        );
    }

    #[test]
    fn cranelift_i32() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::I32, &table, ptr),
            types::I32
        );
    }

    #[test]
    fn cranelift_i64() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::I64, &table, ptr),
            types::I64
        );
    }

    #[test]
    fn cranelift_i128() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::I128, &table, ptr),
            types::I128
        );
    }

    #[test]
    fn cranelift_u8() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(VirTypeId::U8, &table, ptr), types::I8);
    }

    #[test]
    fn cranelift_u64() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::U64, &table, ptr),
            types::I64
        );
    }

    #[test]
    fn cranelift_f32() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::F32, &table, ptr),
            types::F32
        );
    }

    #[test]
    fn cranelift_f64() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::F64, &table, ptr),
            types::F64
        );
    }

    #[test]
    fn cranelift_bool() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::BOOL, &table, ptr),
            types::I8
        );
    }

    #[test]
    fn cranelift_string_is_pointer() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(VirTypeId::STRING, &table, ptr), ptr);
    }

    #[test]
    fn cranelift_handle_is_pointer() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(VirTypeId::HANDLE, &table, ptr), ptr);
    }

    #[test]
    fn cranelift_void() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::VOID, &table, ptr),
            types::I64
        );
    }

    #[test]
    fn cranelift_nil() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::NIL, &table, ptr),
            types::I8
        );
    }

    #[test]
    fn cranelift_done() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(
            vir_type_to_cranelift(VirTypeId::DONE, &table, ptr),
            types::I8
        );
    }

    #[test]
    fn cranelift_never_is_pointer() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(VirTypeId::NEVER, &table, ptr), ptr);
    }

    #[test]
    fn cranelift_unknown_is_pointer() {
        let table = test_table();
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(VirTypeId::UNKNOWN, &table, ptr), ptr);
    }

    #[test]
    fn cranelift_array_is_pointer() {
        let mut table = test_table();
        let layout = VirTypeLayout {
            is_rc: true,
            is_heap: true,
            is_wide: false,
            slot_count: 1,
            storage: StorageClass::Pointer,
        };
        let arr = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            Some(layout),
        );
        let ptr = types::I64;
        assert_eq!(vir_type_to_cranelift(arr, &table, ptr), ptr);
    }

    // -----------------------------------------------------------------------
    // Layout queries
    // -----------------------------------------------------------------------

    #[test]
    fn is_wide_i128() {
        let table = test_table();
        assert!(vir_is_wide(VirTypeId::I128, &table));
    }

    #[test]
    fn is_wide_i64_false() {
        let table = test_table();
        assert!(!vir_is_wide(VirTypeId::I64, &table));
    }

    #[test]
    fn is_rc_string() {
        let table = test_table();
        assert!(vir_is_rc(VirTypeId::STRING, &table));
    }

    #[test]
    fn is_rc_i64_false() {
        let table = test_table();
        assert!(!vir_is_rc(VirTypeId::I64, &table));
    }

    #[test]
    fn is_rc_handle() {
        let table = test_table();
        assert!(vir_is_rc(VirTypeId::HANDLE, &table));
    }

    #[test]
    fn is_heap_string() {
        let table = test_table();
        assert!(vir_is_heap(VirTypeId::STRING, &table));
    }

    #[test]
    fn is_heap_i64_false() {
        let table = test_table();
        assert!(!vir_is_heap(VirTypeId::I64, &table));
    }

    #[test]
    fn slot_count_i64() {
        let table = test_table();
        assert_eq!(vir_slot_count(VirTypeId::I64, &table), 1);
    }

    #[test]
    fn slot_count_i128() {
        let table = test_table();
        assert_eq!(vir_slot_count(VirTypeId::I128, &table), 2);
    }

    #[test]
    fn slot_count_void() {
        let table = test_table();
        assert_eq!(vir_slot_count(VirTypeId::VOID, &table), 0);
    }

    #[test]
    fn storage_class_i64() {
        let table = test_table();
        assert_eq!(
            vir_storage_class(VirTypeId::I64, &table),
            StorageClass::Word
        );
    }

    #[test]
    fn storage_class_f64() {
        let table = test_table();
        assert_eq!(
            vir_storage_class(VirTypeId::F64, &table),
            StorageClass::Float
        );
    }

    #[test]
    fn storage_class_string() {
        let table = test_table();
        assert_eq!(
            vir_storage_class(VirTypeId::STRING, &table),
            StorageClass::Pointer
        );
    }

    #[test]
    fn storage_class_i128() {
        let table = test_table();
        assert_eq!(
            vir_storage_class(VirTypeId::I128, &table),
            StorageClass::Wide
        );
    }

    #[test]
    fn storage_class_void() {
        let table = test_table();
        assert_eq!(
            vir_storage_class(VirTypeId::VOID, &table),
            StorageClass::Void
        );
    }

    #[test]
    fn field_byte_size_i64() {
        let table = test_table();
        assert_eq!(vir_field_byte_size(VirTypeId::I64, &table), 8);
    }

    #[test]
    fn field_byte_size_i128() {
        let table = test_table();
        assert_eq!(vir_field_byte_size(VirTypeId::I128, &table), 16);
    }

    #[test]
    fn field_slot_count_i64() {
        let table = test_table();
        assert_eq!(vir_field_slot_count(VirTypeId::I64, &table), 1);
    }

    #[test]
    fn field_slot_count_i128() {
        let table = test_table();
        assert_eq!(vir_field_slot_count(VirTypeId::I128, &table), 2);
    }

    // -----------------------------------------------------------------------
    // Unsigned checks
    // -----------------------------------------------------------------------

    #[test]
    fn is_unsigned_u8() {
        let table = test_table();
        assert!(vir_is_unsigned(VirTypeId::U8, &table));
    }

    #[test]
    fn is_unsigned_u64() {
        let table = test_table();
        assert!(vir_is_unsigned(VirTypeId::U64, &table));
    }

    #[test]
    fn is_unsigned_i64_false() {
        let table = test_table();
        assert!(!vir_is_unsigned(VirTypeId::I64, &table));
    }

    #[test]
    fn is_unsigned_string_false() {
        let table = test_table();
        assert!(!vir_is_unsigned(VirTypeId::STRING, &table));
    }

    #[test]
    fn is_unsigned_bool_false() {
        let table = test_table();
        assert!(!vir_is_unsigned(VirTypeId::BOOL, &table));
    }
}
