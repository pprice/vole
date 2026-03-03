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
use cranelift_codegen::ir::FuncRef;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::ops::{sextend_const, uextend_const};
use vole_frontend::{Interner, Symbol};
use vole_identity::{NameId, NameTable, TypeDefId, VirTypeId};
use vole_vir::entity_metadata::VirEntityMetadata;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{StorageClass, VirPrimitiveKind, VirType};

use super::vir_struct_helpers::{
    VirStructEntityLookup, vir_struct_flat_slot_count, vir_struct_total_byte_size,
};

// Bridge functions vir_to_sema_type_id_lossy and vir_to_sema_type_id
// have been deleted. All callers now use VirTypeTable::vir_to_type_id().

/// Map a `VirTypeId` to a Cranelift type using the VIR type table.
///
/// Uses `VirType` variant + `VirPrimitiveKind` for precise width mapping
/// (I8, I16, I32, etc.), falling back to `StorageClass` for compound types.
pub(crate) fn vir_type_to_cranelift(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    pointer_type: Type,
) -> Type {
    if vir_ty == VirTypeId::F128 {
        return types::F128;
    }

    // Sentinel types (nil, Done, user-defined) are zero-sized, I8 tag placeholder.
    if table.is_sentinel(vir_ty) {
        return types::I8;
    }

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
// Type query helpers — VirTypeTable-based replacements for TypeArena queries
// ============================================================================

/// Check if a `VirTypeId` is a union type.
pub(crate) fn vir_is_union(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Union { .. } | VirType::Optional { .. }
    )
}

/// Get the variant `VirTypeId`s from a union type.
///
/// Returns `None` if the type is not a union.
pub(crate) fn vir_unwrap_union(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<&[VirTypeId]> {
    match table.get(vir_ty) {
        VirType::Union { variants } => Some(variants),
        _ => None,
    }
}

/// Check if a `VirTypeId` is an optional type (`T?`, i.e. `T | nil`).
pub(crate) fn vir_is_optional(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Optional { .. })
}

/// Unwrap an optional type, returning the inner `VirTypeId`.
///
/// Returns `None` if the type is not optional.
pub(crate) fn vir_unwrap_optional(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<VirTypeId> {
    match table.get(vir_ty) {
        VirType::Optional { inner } => Some(*inner),
        _ => None,
    }
}

/// Check if a `VirTypeId` is the string primitive type.
pub(crate) fn vir_is_string(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Primitive(VirPrimitiveKind::String)
    )
}

/// Check if a `VirTypeId` is a dynamic array type.
pub(crate) fn vir_is_array(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Array { .. })
}

/// Unwrap an array type, returning the element `VirTypeId`.
///
/// Returns `None` if the type is not a dynamic array.
pub(crate) fn vir_unwrap_array(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<VirTypeId> {
    match table.get(vir_ty) {
        VirType::Array { elem } => Some(*elem),
        _ => None,
    }
}

/// Check if a `VirTypeId` is a class (reference-counted instance) type.
pub(crate) fn vir_is_class(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Class { .. })
}

/// Unwrap a class type, returning its `TypeDefId` and type arguments.
///
/// Returns `None` if the type is not a class.
pub(crate) fn vir_unwrap_class(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(TypeDefId, &[VirTypeId])> {
    match table.get(vir_ty) {
        VirType::Class { def, type_args } => Some((*def, type_args)),
        _ => None,
    }
}

/// Check if a `VirTypeId` is a value-type struct.
pub(crate) fn vir_is_struct(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    // Sentinel types (Nil, Done, user-defined empties) are VirType::Struct
    // internally but not treated as structs for codegen purposes — matching
    // the arena's `is_struct()` which excludes them.
    !table.is_sentinel(vir_ty) && matches!(table.get(vir_ty), VirType::Struct { .. })
}

/// Unwrap a struct type, returning its `TypeDefId` and type arguments.
///
/// Returns `None` if the type is not a struct or is a sentinel (Nil, Done).
/// Matches `vir_is_struct()` which also excludes sentinels.
pub(crate) fn vir_unwrap_struct(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(TypeDefId, &[VirTypeId])> {
    if table.is_sentinel(vir_ty) {
        return None;
    }
    match table.get(vir_ty) {
        VirType::Struct { def, type_args } => Some((*def, type_args)),
        _ => None,
    }
}

/// Check if a `VirTypeId` is an interface (trait object) type.
pub(crate) fn vir_is_interface(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Interface { .. })
}

/// Unwrap an interface type, returning its `TypeDefId` and type arguments.
///
/// Returns `None` if the type is not an interface.
pub(crate) fn vir_unwrap_interface(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(TypeDefId, &[VirTypeId])> {
    match table.get(vir_ty) {
        VirType::Interface { def, type_args } => Some((*def, type_args)),
        _ => None,
    }
}

/// Check if a `VirTypeId` is the nil type.
pub(crate) fn vir_is_nil(vir_ty: VirTypeId, _table: &VirTypeTable) -> bool {
    vir_ty == VirTypeId::NIL
}

/// Check if a `VirTypeId` is a fallible return type.
pub(crate) fn vir_is_fallible(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Fallible { .. })
}

/// Unwrap a fallible type, returning the success type and error types.
///
/// Returns `None` if the type is not fallible.
pub(crate) fn vir_unwrap_fallible(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(VirTypeId, &[VirTypeId])> {
    match table.get(vir_ty) {
        VirType::Fallible { success, errors } => Some((*success, errors)),
        _ => None,
    }
}

/// Check if a `VirTypeId` is a function/closure type.
pub(crate) fn vir_is_function(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Function { .. })
}

/// Check if a `VirTypeId` is an error type.
pub(crate) fn vir_is_error(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Error { .. })
}

/// Check if a `VirTypeId` is a runtime iterator type.
pub(crate) fn vir_is_runtime_iterator(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::RuntimeIterator { .. })
}

/// Check if a `VirTypeId` is the unknown (boxed TaggedValue) type.
pub(crate) fn vir_is_unknown(vir_ty: VirTypeId, _table: &VirTypeTable) -> bool {
    vir_ty == VirTypeId::UNKNOWN
}

/// Check if a `VirTypeId` is the void type.
pub(crate) fn vir_is_void(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Void)
}

/// Check if a `VirTypeId` is a struct or class type.
pub(crate) fn vir_is_class_or_struct(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Class { .. } | VirType::Struct { .. }
    )
}

/// Unwrap a class or struct type, returning its `TypeDefId` and type arguments.
///
/// Returns `None` if the type is neither a class nor a struct, or is a sentinel.
pub(crate) fn vir_unwrap_class_or_struct(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(TypeDefId, &[VirTypeId])> {
    if table.is_sentinel(vir_ty) {
        return None;
    }
    match table.get(vir_ty) {
        VirType::Class { def, type_args } | VirType::Struct { def, type_args } => {
            Some((*def, type_args))
        }
        _ => None,
    }
}

/// Unwrap a nominal type (class, struct, or interface), returning its `TypeDefId`.
///
/// Returns `None` for non-nominal types (primitives, unions, etc.)
/// and for sentinel types (Nil, Done).
pub(crate) fn vir_unwrap_nominal(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<TypeDefId> {
    if table.is_sentinel(vir_ty) {
        return None;
    }
    match table.get(vir_ty) {
        VirType::Class { def, .. }
        | VirType::Struct { def, .. }
        | VirType::Interface { def, .. } => Some(*def),
        _ => None,
    }
}

/// Unwrap a runtime iterator type, returning the element `VirTypeId`.
///
/// Returns `None` if the type is not a runtime iterator.
pub(crate) fn vir_unwrap_runtime_iterator(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<VirTypeId> {
    match table.get(vir_ty) {
        VirType::RuntimeIterator { elem } => Some(*elem),
        _ => None,
    }
}

/// Unwrap a function type, returning the return type `VirTypeId`.
///
/// Returns `None` if the type is not a function.
pub(crate) fn vir_unwrap_function_ret(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<VirTypeId> {
    match table.get(vir_ty) {
        VirType::Function { ret, .. } => Some(*ret),
        _ => None,
    }
}

/// Check if a fallible type has a wide (i128) success type.
///
/// Returns true if the type is `Fallible { success, .. }` and `success`
/// is a wide type.  When true, the fallible return convention uses 3
/// registers instead of 2: (tag, payload_low, payload_high).
pub(crate) fn vir_is_wide_fallible(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    vir_unwrap_fallible(vir_ty, table).is_some_and(|(success, _)| vir_is_wide(success, table))
}

/// Check if a union type has non-sentinel payload variants.
///
/// Returns `true` if the type is a union (or optional) and at least one
/// variant is neither Nil, Done, nor Void.  `Optional<T>` is always a
/// payload union because its inner type `T` is non-nil by construction.
pub(crate) fn vir_is_payload_union(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    match table.get(vir_ty) {
        VirType::Optional { .. } => true,
        VirType::Union { variants } => variants
            .iter()
            .any(|&v| !table.is_sentinel(v) && !matches!(table.get(v), VirType::Void)),
        _ => false,
    }
}

/// Get the runtime type tag for boxing a value into the Unknown type
/// (TaggedValue).
///
/// Maps VIR types to the corresponding `RuntimeTypeId` tag values used
/// by the runtime's `TaggedValue.tag` field.
pub(crate) fn vir_unknown_type_tag(vir_ty: VirTypeId, table: &VirTypeTable) -> u64 {
    use vole_runtime::value::RuntimeTypeId;
    if (vir_ty.raw() as usize) >= table.len() {
        return RuntimeTypeId::I64 as u64;
    }
    match table.get(vir_ty) {
        VirType::Primitive(VirPrimitiveKind::String) => RuntimeTypeId::String as u64,
        VirType::Primitive(
            VirPrimitiveKind::I64
            | VirPrimitiveKind::I32
            | VirPrimitiveKind::I16
            | VirPrimitiveKind::I8
            | VirPrimitiveKind::U64
            | VirPrimitiveKind::U32
            | VirPrimitiveKind::U16
            | VirPrimitiveKind::U8,
        ) => RuntimeTypeId::I64 as u64,
        VirType::Primitive(VirPrimitiveKind::F64 | VirPrimitiveKind::F32) => {
            RuntimeTypeId::F64 as u64
        }
        VirType::Primitive(VirPrimitiveKind::Bool) => RuntimeTypeId::Bool as u64,
        VirType::Array { .. } | VirType::FixedArray { .. } => RuntimeTypeId::Array as u64,
        VirType::Function { .. } => RuntimeTypeId::Closure as u64,
        VirType::Class { .. } => RuntimeTypeId::Instance as u64,
        _ => RuntimeTypeId::I64 as u64,
    }
}

/// Format a VIR type for diagnostic/error messages.
///
/// Returns a simple human-readable name (e.g., "i64", "String",
/// "Class(42)", "Interface(7)").
pub(crate) fn vir_display_basic(vir_ty: VirTypeId, table: &VirTypeTable) -> String {
    // Check well-known sentinels by VirTypeId before pattern matching.
    if vir_ty == VirTypeId::NIL {
        return "nil".into();
    }
    if vir_ty == VirTypeId::DONE {
        return "Done".into();
    }

    match table.get(vir_ty) {
        VirType::Primitive(kind) => match kind {
            VirPrimitiveKind::I8 => "i8".into(),
            VirPrimitiveKind::I16 => "i16".into(),
            VirPrimitiveKind::I32 => "i32".into(),
            VirPrimitiveKind::I64 => "i64".into(),
            VirPrimitiveKind::I128 => "i128".into(),
            VirPrimitiveKind::U8 => "u8".into(),
            VirPrimitiveKind::U16 => "u16".into(),
            VirPrimitiveKind::U32 => "u32".into(),
            VirPrimitiveKind::U64 => "u64".into(),
            VirPrimitiveKind::F32 => "f32".into(),
            VirPrimitiveKind::F64 => "f64".into(),
            VirPrimitiveKind::Bool => "bool".into(),
            VirPrimitiveKind::String => "string".into(),
            VirPrimitiveKind::Handle => "handle".into(),
        },
        VirType::Void => "void".into(),
        VirType::Never => "never".into(),
        VirType::Unknown => "unknown".into(),
        VirType::Range => "range".into(),
        VirType::MetaType => "type".into(),
        VirType::Class { def, .. } => format!("Class({:?})", def),
        VirType::Struct { def, .. } => format!("Struct({:?})", def),
        VirType::Interface { def, .. } => format!("Interface({:?})", def),
        VirType::Array { .. } => "Array".into(),
        VirType::FixedArray { .. } => "FixedArray".into(),
        VirType::Tuple { .. } => "Tuple".into(),
        VirType::Optional { .. } => "Optional".into(),
        VirType::Union { .. } => "Union".into(),
        VirType::Fallible { .. } => "Fallible".into(),
        VirType::Function { .. } => "Function".into(),
        VirType::Error { .. } => "Error".into(),
        VirType::RuntimeIterator { .. } => "RuntimeIterator".into(),
        VirType::Param { .. } => "TypeParam".into(),
    }
}

/// Format a VIR type for display, resolving nominal types to their entity names.
///
/// Like [`vir_display_basic`] but resolves Class/Struct/Interface TypeDefId to
/// human-readable names via entity metadata and the name table.
pub(crate) fn vir_display_named(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
    names: &NameTable,
) -> String {
    // Check well-known sentinels first.
    if vir_ty == VirTypeId::NIL {
        return "nil".into();
    }
    if vir_ty == VirTypeId::DONE {
        return "Done".into();
    }

    match table.get(vir_ty) {
        VirType::Primitive(kind) => match kind {
            VirPrimitiveKind::I8 => "i8".into(),
            VirPrimitiveKind::I16 => "i16".into(),
            VirPrimitiveKind::I32 => "i32".into(),
            VirPrimitiveKind::I64 => "i64".into(),
            VirPrimitiveKind::I128 => "i128".into(),
            VirPrimitiveKind::U8 => "u8".into(),
            VirPrimitiveKind::U16 => "u16".into(),
            VirPrimitiveKind::U32 => "u32".into(),
            VirPrimitiveKind::U64 => "u64".into(),
            VirPrimitiveKind::F32 => "f32".into(),
            VirPrimitiveKind::F64 => "f64".into(),
            VirPrimitiveKind::Bool => "bool".into(),
            VirPrimitiveKind::String => "string".into(),
            VirPrimitiveKind::Handle => "handle".into(),
        },
        VirType::Void => "void".into(),
        VirType::Never => "never".into(),
        VirType::Unknown => "unknown".into(),
        VirType::Range => "range".into(),
        VirType::MetaType => "type".into(),
        VirType::Class { def, type_args } => {
            format_nominal("Class", *def, type_args, table, entities, names)
        }
        VirType::Struct { def, type_args } => {
            format_nominal("Struct", *def, type_args, table, entities, names)
        }
        VirType::Interface { def, type_args } => {
            format_nominal("Interface", *def, type_args, table, entities, names)
        }
        VirType::Array { elem } => {
            format!("[{}]", vir_display_named(*elem, table, entities, names))
        }
        VirType::FixedArray { elem, len } => {
            format!(
                "[{}; {}]",
                vir_display_named(*elem, table, entities, names),
                len
            )
        }
        VirType::Tuple { elems } => {
            let parts: Vec<_> = elems
                .iter()
                .map(|e| vir_display_named(*e, table, entities, names))
                .collect();
            format!("({})", parts.join(", "))
        }
        VirType::Optional { inner } => {
            format!("{}?", vir_display_named(*inner, table, entities, names))
        }
        VirType::Union { variants } => {
            let parts: Vec<_> = variants
                .iter()
                .map(|v| vir_display_named(*v, table, entities, names))
                .collect();
            parts.join(" | ")
        }
        VirType::Fallible { success, errors } => {
            let err_parts: Vec<_> = errors
                .iter()
                .map(|e| vir_display_named(*e, table, entities, names))
                .collect();
            format!(
                "{} ! {}",
                vir_display_named(*success, table, entities, names),
                err_parts.join(" | ")
            )
        }
        VirType::Function { params, ret } => {
            let param_parts: Vec<_> = params
                .iter()
                .map(|p| vir_display_named(*p, table, entities, names))
                .collect();
            format!(
                "({}) -> {}",
                param_parts.join(", "),
                vir_display_named(*ret, table, entities, names)
            )
        }
        VirType::RuntimeIterator { elem } => {
            format!(
                "RuntimeIterator<{}>",
                vir_display_named(*elem, table, entities, names)
            )
        }
        VirType::Error { def } => entities
            .type_name_id(*def)
            .and_then(|name_id| names.last_segment_str(name_id))
            .unwrap_or_else(|| format!("Error({def:?})")),
        VirType::Param { name } => names
            .last_segment_str(*name)
            .unwrap_or_else(|| format!("T({name:?})")),
    }
}

/// Format a nominal type (Class/Struct/Interface) with resolved entity name.
fn format_nominal(
    kind: &str,
    def: TypeDefId,
    type_args: &[VirTypeId],
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
    names: &NameTable,
) -> String {
    let name = entities
        .type_name_id(def)
        .and_then(|name_id| names.last_segment_str(name_id))
        .unwrap_or_else(|| format!("{kind}({def:?})"));
    if type_args.is_empty() {
        name
    } else {
        let args: Vec<_> = type_args
            .iter()
            .map(|a| vir_display_named(*a, table, entities, names))
            .collect();
        format!("{}<{}>", name, args.join(", "))
    }
}

/// Check if a `VirTypeId` is a sentinel type (Nil or Done).
pub(crate) fn vir_is_sentinel(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    table.is_sentinel(vir_ty)
}

/// Check if a `VirTypeId` is a boolean type.
pub(crate) fn vir_is_bool(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Primitive(VirPrimitiveKind::Bool)
    )
}

/// Check if a `VirTypeId` is an integer type (signed or unsigned).
pub(crate) fn vir_is_integer(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Primitive(
            VirPrimitiveKind::I8
                | VirPrimitiveKind::I16
                | VirPrimitiveKind::I32
                | VirPrimitiveKind::I64
                | VirPrimitiveKind::I128
                | VirPrimitiveKind::U8
                | VirPrimitiveKind::U16
                | VirPrimitiveKind::U32
                | VirPrimitiveKind::U64
        )
    )
}

/// Check if a `VirTypeId` is a floating point type.
pub(crate) fn vir_is_float(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Primitive(VirPrimitiveKind::F32 | VirPrimitiveKind::F64)
    )
}

/// Check if a `VirTypeId` is a numeric type (integer or float).
pub(crate) fn vir_is_numeric(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    vir_is_integer(vir_ty, table) || vir_is_float(vir_ty, table)
}

/// Check if a `VirTypeId` is the handle type.
pub(crate) fn vir_is_handle(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(vir_ty),
        VirType::Primitive(VirPrimitiveKind::Handle)
    )
}

/// Check if a `VirTypeId` is a SelfType placeholder.
///
/// VIR does not have a dedicated SelfType variant; this always returns false.
/// The wrapper falls back to the arena for monomorphized types.
pub(crate) fn vir_is_self_type(_vir_ty: VirTypeId, _table: &VirTypeTable) -> bool {
    // VIR resolves SelfType during lowering; no Placeholder variant exists.
    false
}

/// Unwrap a tuple type, returning the element `VirTypeId`s.
///
/// Returns `None` if the type is not a tuple.
pub(crate) fn vir_unwrap_tuple(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<&[VirTypeId]> {
    table.unwrap_tuple(vir_ty)
}

/// Unwrap a fixed array type, returning `(elem, len)`.
///
/// Returns `None` if the type is not a fixed array.
pub(crate) fn vir_unwrap_fixed_array(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(VirTypeId, u32)> {
    table.unwrap_fixed_array(vir_ty)
}

/// Unwrap a function type, returning `(params, return_type)`.
///
/// Returns `None` if the type is not a function.
pub(crate) fn vir_unwrap_function(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(&[VirTypeId], VirTypeId)> {
    table.unwrap_function(vir_ty)
}

/// Unwrap a type parameter, returning its `NameId`.
///
/// Returns `None` if the type is not a `Param`.
pub(crate) fn vir_unwrap_type_param(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<NameId> {
    match table.get(vir_ty) {
        VirType::Param { name } => Some(*name),
        _ => None,
    }
}

/// Unwrap an error type, returning its `TypeDefId`.
///
/// Returns `None` if the type is not an error.
pub(crate) fn vir_unwrap_error(vir_ty: VirTypeId, table: &VirTypeTable) -> Option<TypeDefId> {
    match table.get(vir_ty) {
        VirType::Error { def } => Some(*def),
        _ => None,
    }
}

/// Unwrap an error or struct type, returning its `TypeDefId`.
///
/// Returns `None` if the type is neither an error nor a struct.
pub(crate) fn vir_unwrap_error_or_struct_def(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<TypeDefId> {
    if table.is_sentinel(vir_ty) {
        return None;
    }
    match table.get(vir_ty) {
        VirType::Error { def } | VirType::Struct { def, .. } => Some(*def),
        _ => None,
    }
}

/// Check if a type contains any type parameter anywhere in its structure.
///
/// Recursively walks compound types (arrays, unions, classes, etc.).
pub(crate) fn vir_contains_type_param(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    match table.get(vir_ty) {
        VirType::Param { .. } => true,
        VirType::Class { type_args, .. }
        | VirType::Struct { type_args, .. }
        | VirType::Interface { type_args, .. } => type_args
            .iter()
            .any(|&arg| vir_contains_type_param(arg, table)),
        VirType::Union { variants } => variants.iter().any(|&v| vir_contains_type_param(v, table)),
        VirType::Tuple { elems } => elems.iter().any(|&e| vir_contains_type_param(e, table)),
        VirType::Array { elem } | VirType::RuntimeIterator { elem } => {
            vir_contains_type_param(*elem, table)
        }
        VirType::FixedArray { elem, .. } => vir_contains_type_param(*elem, table),
        VirType::Optional { inner } => vir_contains_type_param(*inner, table),
        VirType::Function { params, ret } => {
            params.iter().any(|&p| vir_contains_type_param(p, table))
                || vir_contains_type_param(*ret, table)
        }
        VirType::Fallible { success, errors } => {
            vir_contains_type_param(*success, table)
                || errors.iter().any(|&e| vir_contains_type_param(e, table))
        }
        _ => false,
    }
}

// ============================================================================
// VIR-native type conversion functions (Phase 3b)
//
// These replace the arena-based functions in conversions.rs for code paths
// that operate on VirTypeId.  Each function matches on VirType variants
// instead of SemaType variants.
// ============================================================================

/// Sum the byte sizes of all fields in a VIR error type definition.
///
/// VIR equivalent of `error_fields_size()` in conversions.rs.
fn vir_error_fields_size(
    type_def_id: TypeDefId,
    pointer_type: Type,
    entities: &impl VirStructEntityLookup,
    table: &VirTypeTable,
) -> u32 {
    let field_vir_types = entities
        .vir_type_def(type_def_id)
        .map(|td| &td.field_types[..])
        .unwrap_or(&[]);
    field_vir_types
        .iter()
        .map(|&field_vir_ty| vir_type_id_size(field_vir_ty, pointer_type, entities, table))
        .sum()
}

/// Get the byte size for a VIR type.
///
/// VIR equivalent of `type_id_size()` in conversions.rs.
pub(crate) fn vir_type_id_size(
    vir_ty: VirTypeId,
    pointer_type: Type,
    entities: &impl VirStructEntityLookup,
    table: &VirTypeTable,
) -> u32 {
    if vir_ty == VirTypeId::UNKNOWN {
        return pointer_type.bytes();
    }

    // Sentinel types are zero-sized.
    if table.is_sentinel(vir_ty) {
        return 0;
    }

    match table.get(vir_ty) {
        VirType::Primitive(kind) => match kind {
            VirPrimitiveKind::I8 | VirPrimitiveKind::U8 | VirPrimitiveKind::Bool => 1,
            VirPrimitiveKind::I16 | VirPrimitiveKind::U16 => 2,
            VirPrimitiveKind::I32 | VirPrimitiveKind::U32 | VirPrimitiveKind::F32 => 4,
            VirPrimitiveKind::I64 | VirPrimitiveKind::U64 | VirPrimitiveKind::F64 => 8,
            VirPrimitiveKind::I128 => 16,
            VirPrimitiveKind::String | VirPrimitiveKind::Handle => pointer_type.bytes(),
        },

        // Void: no meaningful value.
        VirType::Void => 0,

        // Range: 16 bytes (start i64 + end i64).
        VirType::Range => 16,

        // Unknown: TaggedValue representation: 8-byte tag + 8-byte value = 16 bytes.
        VirType::Unknown => 16,

        // Heap-allocated RC types: pointer-sized.
        VirType::Array { .. }
        | VirType::Class { .. }
        | VirType::RuntimeIterator { .. }
        | VirType::Function { .. }
        | VirType::Interface { .. } => pointer_type.bytes(),

        // Struct types: use flat slot count to account for nested struct fields.
        VirType::Struct { .. } => vir_struct_total_byte_size(vir_ty, table, entities)
            .expect("INTERNAL: valid struct must have computable size"),

        // Union: tag + max variant payload (aligned to 8 bytes).
        VirType::Union { variants } => {
            let max_payload = variants
                .iter()
                .map(|&t| {
                    // Struct variants are auto-boxed, so their payload is a pointer.
                    if matches!(table.get(t), VirType::Struct { .. }) {
                        pointer_type.bytes()
                    } else {
                        vir_type_id_size(t, pointer_type, entities, table)
                    }
                })
                .max()
                .unwrap_or(0);
            crate::union_layout::TAG_ONLY_SIZE + max_payload.div_ceil(8) * 8
        }

        // Optional: treated like union with nil variant.
        VirType::Optional { inner } => {
            let inner_size = vir_type_id_size(*inner, pointer_type, entities, table);
            crate::union_layout::TAG_ONLY_SIZE + inner_size.div_ceil(8) * 8
        }

        // Error: sum of field sizes, aligned.
        VirType::Error { def } => {
            vir_error_fields_size(*def, pointer_type, entities, table).div_ceil(8) * 8
        }

        // Fallible: tag + max(success, error) payload, aligned.
        VirType::Fallible { success, errors } => {
            let success_size = vir_type_id_size(*success, pointer_type, entities, table);
            let error_size = if errors.len() == 1 {
                // Single error type.
                match table.get(errors[0]) {
                    VirType::Error { def } => {
                        vir_error_fields_size(*def, pointer_type, entities, table)
                    }
                    _ => 0,
                }
            } else {
                // Union of error types: max of all error field sizes.
                errors
                    .iter()
                    .filter_map(|&e| match table.get(e) {
                        VirType::Error { def } => {
                            Some(vir_error_fields_size(*def, pointer_type, entities, table))
                        }
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0)
            };
            let max_payload = success_size.max(error_size);
            crate::union_layout::TAG_ONLY_SIZE + max_payload.div_ceil(8) * 8
        }

        // Tuple: sum of element sizes (each aligned to 8 bytes).
        VirType::Tuple { elems } => elems
            .iter()
            .map(|&t| vir_type_id_size(t, pointer_type, entities, table).div_ceil(8) * 8)
            .sum(),

        // Fixed array: element size * count.
        VirType::FixedArray { elem, len } => {
            let elem_size = vir_type_id_size(*elem, pointer_type, entities, table).div_ceil(8) * 8;
            elem_size * *len
        }

        // Bottom/meta/param types: pointer-erased.
        VirType::Never | VirType::MetaType | VirType::Param { .. } => pointer_type.bytes(),
    }
}

/// Calculate layout for tuple elements using VirTypeId.
///
/// VIR equivalent of `tuple_layout_id()` in conversions.rs.
/// Returns (total_size, offsets) where offsets[i] is the byte offset for element i.
/// Each element is aligned to 8 bytes.
pub(crate) fn vir_tuple_layout(
    elements: &[VirTypeId],
    pointer_type: Type,
    entities: &impl VirStructEntityLookup,
    table: &VirTypeTable,
) -> (u32, Vec<i32>) {
    let mut offsets = Vec::with_capacity(elements.len());
    let mut offset = 0i32;

    for &elem in elements {
        offsets.push(offset);
        let elem_size = vir_type_id_size(elem, pointer_type, entities, table).div_ceil(8) * 8;
        offset += elem_size as i32;
    }

    (offset as u32, offsets)
}

/// Get the runtime tag value for an array element type.
///
/// VIR equivalent of `array_element_tag_id()` in conversions.rs.
/// These tags must match the `RuntimeTypeId` variants in `vole_runtime::value`
/// so that `tag_needs_rc` correctly identifies RC-managed elements for cleanup
/// in `array_drop`.
pub(crate) fn vir_array_element_tag_id(vir_ty: VirTypeId, table: &VirTypeTable) -> i64 {
    use vole_runtime::value::RuntimeTypeId;
    // Handle type check
    if matches!(
        table.get(vir_ty),
        VirType::Primitive(VirPrimitiveKind::Handle)
    ) {
        return RuntimeTypeId::Rng as i64;
    }
    // Sentinel types (nil, Done) are non-RC stack values.
    if table.is_sentinel(vir_ty) {
        return RuntimeTypeId::I64 as i64;
    }
    // F128 is stored as VirType::Unknown placeholder (no VirPrimitiveKind::F128 yet),
    // but it's a wide type that uses 2-slot storage like i128.
    if vir_ty == VirTypeId::F128 {
        return RuntimeTypeId::Wide128 as i64;
    }
    match table.get(vir_ty) {
        VirType::Primitive(VirPrimitiveKind::String) => RuntimeTypeId::String as i64,
        VirType::Primitive(
            VirPrimitiveKind::I64
            | VirPrimitiveKind::I32
            | VirPrimitiveKind::I16
            | VirPrimitiveKind::I8,
        ) => RuntimeTypeId::I64 as i64,
        VirType::Primitive(VirPrimitiveKind::I128) => RuntimeTypeId::Wide128 as i64,
        VirType::Primitive(VirPrimitiveKind::F64 | VirPrimitiveKind::F32) => {
            RuntimeTypeId::F64 as i64
        }
        VirType::Primitive(VirPrimitiveKind::Bool) => RuntimeTypeId::Bool as i64,
        VirType::Array { .. } => RuntimeTypeId::Array as i64,
        VirType::Function { .. } => RuntimeTypeId::Closure as i64,
        VirType::Class { .. } => RuntimeTypeId::Instance as i64,
        VirType::Union { .. } => RuntimeTypeId::UnionHeap as i64,
        VirType::Unknown => RuntimeTypeId::UnknownHeap as i64,
        _ => RuntimeTypeId::I64 as i64,
    }
}

/// Convert a compiled value to a target Cranelift type.
///
/// VIR equivalent of `convert_to_type()` in conversions.rs.
/// Uses VirTypeTable instead of TypeArena for unsigned type detection.
pub(crate) fn vir_convert_to_type(
    builder: &mut FunctionBuilder,
    val: super::CompiledValue,
    target: Type,
    table: &VirTypeTable,
) -> Value {
    fn pack_f64_to_f128(builder: &mut FunctionBuilder, f64_val: Value) -> Value {
        let bits64 = builder.ins().bitcast(types::I64, MemFlags::new(), f64_val);
        let bits128 = uextend_const(builder, types::I128, bits64);
        builder.ins().bitcast(types::F128, MemFlags::new(), bits128)
    }

    fn unpack_f128_to_f64(builder: &mut FunctionBuilder, f128_val: Value) -> Value {
        let bits128 = builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), f128_val);
        let bits64 = builder.ins().ireduce(types::I64, bits128);
        builder.ins().bitcast(types::F64, MemFlags::new(), bits64)
    }

    if val.ty == target {
        return val.value;
    }

    if target == types::F64 {
        if val.ty == types::I64 || val.ty == types::I32 {
            return builder.ins().fcvt_from_sint(types::F64, val.value);
        }
        if val.ty == types::F128 {
            return unpack_f128_to_f64(builder, val.value);
        }
        if val.ty == types::F32 {
            return builder.ins().fpromote(types::F64, val.value);
        }
    }

    if target == types::F32 {
        if val.ty == types::F128 {
            let f64_val = unpack_f128_to_f64(builder, val.value);
            return builder.ins().fdemote(types::F32, f64_val);
        }
        if val.ty == types::F64 {
            return builder.ins().fdemote(types::F32, val.value);
        }
    }

    if target == types::F128 {
        if val.ty == types::F64 {
            return pack_f64_to_f128(builder, val.value);
        }
        if val.ty == types::F32 {
            let f64_val = builder.ins().fpromote(types::F64, val.value);
            return pack_f64_to_f128(builder, f64_val);
        }
        if val.ty.is_int() {
            let f64_val = if val.ty == types::I128 {
                let low = builder.ins().ireduce(types::I64, val.value);
                builder.ins().fcvt_from_sint(types::F64, low)
            } else {
                builder.ins().fcvt_from_sint(types::F64, val.value)
            };
            return pack_f64_to_f128(builder, f64_val);
        }
    }

    // Integer widening — use uextend for unsigned types, sextend for signed.
    if target.is_int() && val.ty.is_int() && target.bits() > val.ty.bits() {
        // Check VirTypeTable for unsigned status; for UNKNOWN types default to signed.
        let is_unsigned = val.type_id != VirTypeId::UNKNOWN && vir_is_unsigned(val.type_id, table);
        if is_unsigned {
            return uextend_const(builder, target, val.value);
        } else {
            return sextend_const(builder, target, val.value);
        }
    }

    // Integer narrowing.
    if target.is_int() && val.ty.is_int() && target.bits() < val.ty.bits() {
        return builder.ins().ireduce(target, val.value);
    }

    if target.is_int() && val.ty == types::F128 {
        let f64_val = unpack_f128_to_f64(builder, val.value);
        if target == types::I128 {
            let narrowed = builder.ins().fcvt_to_sint(types::I64, f64_val);
            return sextend_const(builder, types::I128, narrowed);
        }
        return builder.ins().fcvt_to_sint(target, f64_val);
    }

    val.value
}

/// Convert a value to a uniform word representation for interface dispatch.
///
/// VIR equivalent of `value_to_word()` in conversions.rs.
pub(crate) fn vir_value_to_word(
    builder: &mut FunctionBuilder,
    value: &super::CompiledValue,
    pointer_type: Type,
    heap_alloc_ref: Option<FuncRef>,
    entities: &impl VirStructEntityLookup,
    table: &VirTypeTable,
) -> CodegenResult<Value> {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();

    let vir_ty = value.type_id;
    let value_size = vir_type_id_size(vir_ty, pointer_type, entities, table);
    let needs_box = value_size > word_bytes;

    if needs_box {
        // If the Cranelift type is already a pointer and the Vole type needs boxing,
        // then the value is already a pointer to boxed data. Just return it directly.
        if value.ty == pointer_type {
            return Ok(value.value);
        }
        let Some(heap_alloc_ref) = heap_alloc_ref else {
            return Err(CodegenError::missing_resource(
                "heap allocator for interface boxing",
            ));
        };
        let size_val = builder.ins().iconst(pointer_type, value_size as i64);
        let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
        let alloc_ptr = builder.inst_results(alloc_call)[0];
        builder
            .ins()
            .store(MemFlags::new(), value.value, alloc_ptr, 0);
        return Ok(alloc_ptr);
    }

    let word = match table.get(vir_ty) {
        VirType::Primitive(VirPrimitiveKind::F64) => {
            builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), value.value)
        }
        VirType::Primitive(VirPrimitiveKind::F32) => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            uextend_const(builder, word_type, i32_val)
        }
        VirType::Primitive(
            VirPrimitiveKind::Bool
            | VirPrimitiveKind::I8
            | VirPrimitiveKind::U8
            | VirPrimitiveKind::I16
            | VirPrimitiveKind::U16
            | VirPrimitiveKind::I32
            | VirPrimitiveKind::U32,
        ) => {
            if value.ty == word_type {
                value.value
            } else {
                uextend_const(builder, word_type, value.value)
            }
        }
        VirType::Primitive(VirPrimitiveKind::I64 | VirPrimitiveKind::U64) => value.value,
        VirType::Primitive(VirPrimitiveKind::I128) => {
            let low = builder.ins().ireduce(types::I64, value.value);
            if word_type == types::I64 {
                low
            } else {
                uextend_const(builder, word_type, low)
            }
        }
        _ => value.value,
    };

    Ok(word)
}

/// Convert a uniform word representation back into a typed value.
///
/// VIR equivalent of `word_to_value_type_id()` in conversions.rs.
pub(crate) fn vir_word_to_value(
    builder: &mut FunctionBuilder,
    word: Value,
    vir_ty: VirTypeId,
    pointer_type: Type,
    entities: &impl VirStructEntityLookup,
    table: &VirTypeTable,
) -> Value {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let needs_unbox = vir_type_id_size(vir_ty, pointer_type, entities, table) > word_bytes;

    if needs_unbox {
        let target_type = vir_type_to_cranelift(vir_ty, table, pointer_type);
        if target_type == pointer_type {
            return word;
        }
        return builder.ins().load(target_type, MemFlags::new(), word, 0);
    }

    match table.get(vir_ty) {
        VirType::Primitive(VirPrimitiveKind::F64) => {
            builder.ins().bitcast(types::F64, MemFlags::new(), word)
        }
        VirType::Primitive(VirPrimitiveKind::F32) => {
            let i32_val = builder.ins().ireduce(types::I32, word);
            builder.ins().bitcast(types::F32, MemFlags::new(), i32_val)
        }
        VirType::Primitive(
            VirPrimitiveKind::Bool | VirPrimitiveKind::I8 | VirPrimitiveKind::U8,
        ) => builder.ins().ireduce(types::I8, word),
        VirType::Primitive(VirPrimitiveKind::I16 | VirPrimitiveKind::U16) => {
            builder.ins().ireduce(types::I16, word)
        }
        VirType::Primitive(VirPrimitiveKind::I32 | VirPrimitiveKind::U32) => {
            builder.ins().ireduce(types::I32, word)
        }
        VirType::Primitive(VirPrimitiveKind::I64 | VirPrimitiveKind::U64) => word,
        VirType::Primitive(VirPrimitiveKind::I128) => {
            let low = if word_type == types::I64 {
                word
            } else {
                builder.ins().ireduce(types::I64, word)
            };
            uextend_const(builder, types::I128, low)
        }
        _ => word,
    }
}

/// Returns the 1-based error tag for a given error name in a fallible type.
///
/// VIR equivalent of `fallible_error_tag_by_id()` in conversions.rs.
/// Takes the error VirTypeIds from a Fallible type and finds the tag
/// for the given error_name.
pub(crate) fn vir_fallible_error_tag_by_id(
    error_vir_types: &[VirTypeId],
    error_name: Symbol,
    table: &VirTypeTable,
    interner: &Interner,
    name_table: &NameTable,
    entities: &VirEntityMetadata,
) -> Option<i64> {
    let error_name_str = interner.resolve(error_name);

    if error_vir_types.len() == 1 {
        // Single error type.
        if let VirType::Error { def } = table.get(error_vir_types[0]) {
            let info_name = entities
                .type_name_id(*def)
                .and_then(|name_id| name_table.last_segment_str(name_id));
            if info_name.as_deref() == Some(error_name_str) {
                return Some(1);
            }
        }
        return None;
    }

    // Multiple error types: search by index.
    for (idx, &error_vir_ty) in error_vir_types.iter().enumerate() {
        if let VirType::Error { def } = table.get(error_vir_ty) {
            let info_name = entities
                .type_name_id(*def)
                .and_then(|name_id| name_table.last_segment_str(name_id));
            if info_name.as_deref() == Some(error_name_str) {
                return Some((idx + 1) as i64);
            }
        }
    }

    None
}

// Struct/class field layout helpers and convert_field_value are in
// types::vir_struct_helpers (split for file size).
// Callers import directly from that submodule.

// ============================================================================
// VIR-native RC state computation (Phase 3b)
//
// VIR equivalent of `compute_rc_state()` in rc_state.rs.
// Uses VirTypeTable instead of TypeArena for all type queries.
// ============================================================================

use crate::rc_state::RcState;

/// Check if a VIR type is a simple RC type (single pointer to RC-managed heap object).
///
/// Simple RC types: String, Array, Function, Class, Handle, Interface,
/// RuntimeIterator. NOT simple: Struct (stack-allocated), sentinels, primitives.
fn vir_is_simple_rc_type(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    vir_is_string(vir_ty, table)
        || vir_is_array(vir_ty, table)
        || vir_is_function(vir_ty, table)
        || vir_is_class(vir_ty, table)
        || vir_is_handle(vir_ty, table)
        || vir_is_interface(vir_ty, table)
        || vir_is_runtime_iterator(vir_ty, table)
}

/// Check if a VIR type qualifies for capture RC management in closures.
///
/// Subset of simple RC types — excludes handles and iterators.
fn vir_is_capture_rc_type(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    vir_is_string(vir_ty, table)
        || vir_is_array(vir_ty, table)
        || vir_is_function(vir_ty, table)
        || vir_is_class(vir_ty, table)
}

/// Compute which union variant tags correspond to RC types (VIR version).
pub(crate) fn vir_compute_union_rc_variants(
    variants: &[VirTypeId],
    table: &VirTypeTable,
) -> Vec<(u8, bool)> {
    variants
        .iter()
        .enumerate()
        .filter(|(_, variant_ty)| vir_is_simple_rc_type(**variant_ty, table))
        .map(|(i, variant_ty)| (i as u8, vir_is_interface(*variant_ty, table)))
        .collect()
}

/// Compute the RC state for a VIR type.
///
/// VIR equivalent of `compute_rc_state()` in rc_state.rs.
/// Analyzes VIR type structure via VirTypeTable and returns the appropriate
/// RcState variant. The result can be cached per VirTypeId.
pub(crate) fn vir_compute_rc_state(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> RcState {
    // Check for simple RC types first (most common case for RC values)
    if vir_is_simple_rc_type(vir_ty, table) {
        let is_capture = vir_is_capture_rc_type(vir_ty, table);
        return RcState::Simple { is_capture };
    }

    // Check for union/optional types with RC variants
    match table.get(vir_ty) {
        VirType::Optional { inner } => {
            // Optional<T> is always a payload union; check if inner is RC
            let rc_variants = if vir_is_simple_rc_type(*inner, table) {
                // Inner type is RC (tag 0 = inner, tag 1 = nil)
                vec![(0u8, vir_is_interface(*inner, table))]
            } else {
                vec![]
            };
            if !rc_variants.is_empty() {
                return RcState::Union { rc_variants };
            }
            return RcState::None;
        }
        VirType::Union { variants } => {
            let rc_variants = vir_compute_union_rc_variants(variants, table);
            if !rc_variants.is_empty() {
                return RcState::Union { rc_variants };
            }
            return RcState::None;
        }
        _ => {}
    }

    // Check for composite types (struct, tuple, fixed array) with RC fields
    if let Some((shallow_offsets, deep_offsets, union_fields)) =
        vir_compute_composite_rc_offsets(vir_ty, table, entities)
    {
        return RcState::Composite {
            shallow_offsets,
            deep_offsets,
            union_fields,
        };
    }

    RcState::None
}

/// Composite RC offsets: (shallow_offsets, deep_offsets, union_fields).
type VirCompositeRcOffsets = (Vec<i32>, Vec<i32>, Vec<(i32, Vec<(u8, bool)>)>);

/// Compute the byte offsets of RC fields within a VIR composite type.
///
/// Returns `Some((shallow_offsets, deep_offsets, union_fields))` if the type
/// has RC fields, or `None` if the type has no RC fields needing cleanup.
fn vir_compute_composite_rc_offsets(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> Option<VirCompositeRcOffsets> {
    // Struct: iterate fields, collect offsets of RC-typed fields
    if let Some((type_def_id, type_args)) = vir_unwrap_struct(vir_ty, table) {
        let td = entities.vir_type_def(type_def_id);

        // For generic structs, substitute type params with concrete type_args
        // using VIR-native substitution (VirTypeId → VirTypeId).
        let field_vir_types: Vec<VirTypeId> = if !type_args.is_empty() {
            let type_params: Vec<NameId> = td.map(|td| td.type_params.clone()).unwrap_or_default();
            if type_params.is_empty() {
                td.map(|td| td.field_types.clone()).unwrap_or_default()
            } else if let Some(generic_field_types) =
                td.and_then(|td| td.generic_field_types.clone())
            {
                let subs: FxHashMap<NameId, VirTypeId> = type_params
                    .iter()
                    .zip(type_args.iter())
                    .map(|(&param, &arg)| (param, arg))
                    .collect();
                generic_field_types
                    .iter()
                    .map(|&field_ty| {
                        table
                            .substitute_vir_ids(field_ty, &subs)
                            .unwrap_or(VirTypeId::UNKNOWN)
                    })
                    .collect()
            } else {
                td.map(|td| td.field_types.clone()).unwrap_or_default()
            }
        } else {
            td.map(|td| td.field_types.clone()).unwrap_or_default()
        };
        let mut shallow_offsets = Vec::new();
        let mut deep_offsets = Vec::new();
        let mut union_fields = Vec::new();
        let mut byte_offset = 0i32;

        for field_vir in &field_vir_types {
            let field_vir = *field_vir;
            let slots = vir_field_flat_slots(field_vir, table, entities);

            // Shallow: only direct RC fields
            if vir_is_simple_rc_type(field_vir, table) {
                shallow_offsets.push(byte_offset);
                deep_offsets.push(byte_offset);
            } else if let Some(variants) = vir_unwrap_union(field_vir, table) {
                // Inline union field: collect RC variant tags for tag-based cleanup
                let rc_tags = vir_compute_union_rc_variants(variants, table);
                if !rc_tags.is_empty() {
                    union_fields.push((byte_offset, rc_tags));
                }
            } else if matches!(table.get(field_vir), VirType::Optional { .. }) {
                // Optional field: check inner type for RC
                if let VirType::Optional { inner } = table.get(field_vir)
                    && vir_is_simple_rc_type(*inner, table)
                {
                    let rc_tags = vec![(0u8, vir_is_interface(*inner, table))];
                    union_fields.push((byte_offset, rc_tags));
                }
            } else {
                // Deep: recursively collect from nested structs
                if let Some((_, nested_deep, nested_unions)) =
                    vir_compute_composite_rc_offsets(field_vir, table, entities)
                {
                    for off in nested_deep {
                        deep_offsets.push(byte_offset + off);
                    }
                    for (off, tags) in nested_unions {
                        union_fields.push((byte_offset + off, tags));
                    }
                }
            }

            byte_offset += (slots as i32) * 8;
        }

        if shallow_offsets.is_empty() && deep_offsets.is_empty() && union_fields.is_empty() {
            return None;
        }
        return Some((shallow_offsets, deep_offsets, union_fields));
    }

    // Fixed array: if element type is RC, all elements need cleanup
    if let Some((elem_vir, len)) = vir_unwrap_fixed_array(vir_ty, table) {
        if vir_is_simple_rc_type(elem_vir, table) {
            let offsets: Vec<i32> = (0..len).map(|i| (i as i32) * 8).collect();
            return Some((offsets.clone(), offsets, Vec::new()));
        }
        return None;
    }

    // Tuple: compute offsets based on element sizes, then filter RC elements
    if let Some(elem_types) = vir_unwrap_tuple(vir_ty, table) {
        let all_offsets = vir_compute_tuple_offsets(elem_types, table, entities);
        let rc_offsets: Vec<i32> = elem_types
            .iter()
            .enumerate()
            .filter(|(_, elem_ty)| vir_is_simple_rc_type(**elem_ty, table))
            .map(|(i, _)| all_offsets[i])
            .collect();

        if rc_offsets.is_empty() {
            return None;
        }
        return Some((rc_offsets.clone(), rc_offsets, Vec::new()));
    }

    None
}

/// Compute the number of flat 8-byte slots a single VIR field occupies.
///
/// Used by `vir_compute_composite_rc_offsets` for offset computation.
/// This duplicates the logic from `vir_field_flat_slots_recursive` in
/// vir_struct_helpers to avoid a circular dependency.
fn vir_field_flat_slots(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> usize {
    if let Some(count) = vir_struct_flat_slot_count(vir_ty, table, entities) {
        return count;
    }
    if super::vir_struct_helpers::vir_is_payload_union(vir_ty, table, entities) {
        return 2;
    }
    vir_field_slot_count(vir_ty, table)
}

/// Compute byte offsets for VIR tuple elements.
///
/// Each element is aligned to 8 bytes. This matches `vir_tuple_layout`
/// but doesn't require a Cranelift pointer type.
fn vir_compute_tuple_offsets(
    elem_types: &[VirTypeId],
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> Vec<i32> {
    let mut offsets = Vec::with_capacity(elem_types.len());
    let mut offset = 0i32;

    for &elem in elem_types {
        offsets.push(offset);
        let elem_size = vir_compute_type_size_aligned(elem, table, entities);
        offset += elem_size;
    }

    offsets
}

/// Compute the size of a VIR type in bytes, aligned to 8 bytes.
///
/// Simplified version of `vir_type_id_size` that assumes 64-bit pointers
/// and aligns all sizes to 8 bytes (matching tuple layout behavior).
fn vir_compute_type_size_aligned(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &impl VirStructEntityLookup,
) -> i32 {
    // Sentinel types are zero-sized
    if vir_is_sentinel(vir_ty, table) {
        return 0;
    }

    let raw_size: i32 = match table.get(vir_ty) {
        VirType::Primitive(kind) => match kind {
            VirPrimitiveKind::I8 | VirPrimitiveKind::U8 | VirPrimitiveKind::Bool => 1,
            VirPrimitiveKind::I16 | VirPrimitiveKind::U16 => 2,
            VirPrimitiveKind::I32 | VirPrimitiveKind::U32 | VirPrimitiveKind::F32 => 4,
            VirPrimitiveKind::I64 | VirPrimitiveKind::U64 | VirPrimitiveKind::F64 => 8,
            VirPrimitiveKind::I128 => 16,
            VirPrimitiveKind::String | VirPrimitiveKind::Handle => 8,
        },

        VirType::Void => 0,
        VirType::Range => 16,   // start + end
        VirType::Unknown => 16, // TaggedValue: 8-byte tag + 8-byte value

        // Heap-allocated RC types: pointer-sized
        VirType::Array { .. }
        | VirType::Class { .. }
        | VirType::RuntimeIterator { .. }
        | VirType::Function { .. }
        | VirType::Interface { .. }
        | VirType::Error { .. }
        | VirType::Fallible { .. } => 8,

        // Struct types: use flat slot count
        VirType::Struct { .. } => vir_struct_total_byte_size(vir_ty, table, entities)
            .expect("INTERNAL: valid struct must have computable size")
            as i32,

        // Union: tag + max variant payload, aligned
        VirType::Union { variants } => {
            let max_payload = variants
                .iter()
                .map(|&v| vir_compute_type_size_aligned(v, table, entities))
                .max()
                .unwrap_or(0);
            crate::union_layout::TAG_ONLY_SIZE as i32 + max_payload
        }

        // Optional: treated like union with nil variant
        VirType::Optional { inner } => {
            let inner_size = vir_compute_type_size_aligned(*inner, table, entities);
            crate::union_layout::TAG_ONLY_SIZE as i32 + inner_size
        }

        // Tuple: sum of aligned element sizes
        VirType::Tuple { elems } => elems
            .iter()
            .map(|&e| vir_compute_type_size_aligned(e, table, entities))
            .sum(),

        // Fixed array: element size * count
        VirType::FixedArray { elem, len } => {
            let elem_size = vir_compute_type_size_aligned(*elem, table, entities);
            elem_size * (*len as i32)
        }

        // Erased types: pointer-sized
        VirType::Never | VirType::MetaType | VirType::Param { .. } => 8,
    };

    // Align to 8 bytes
    ((raw_size + 7) / 8) * 8
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

    // -----------------------------------------------------------------------
    // WideType::from_vir_type_id
    // -----------------------------------------------------------------------

    #[test]
    fn wide_type_from_vir_i128() {
        use crate::types::wide_ops::WideType;
        let table = test_table();
        assert_eq!(
            WideType::from_vir_type_id(VirTypeId::I128, &table),
            Some(WideType::I128),
        );
    }

    #[test]
    fn wide_type_from_vir_f128() {
        use crate::types::wide_ops::WideType;
        let table = test_table();
        assert_eq!(
            WideType::from_vir_type_id(VirTypeId::F128, &table),
            Some(WideType::F128),
        );
    }

    #[test]
    fn wide_type_from_vir_i64_none() {
        use crate::types::wide_ops::WideType;
        let table = test_table();
        assert_eq!(WideType::from_vir_type_id(VirTypeId::I64, &table), None);
    }

    #[test]
    fn wide_type_from_vir_string_none() {
        use crate::types::wide_ops::WideType;
        let table = test_table();
        assert_eq!(WideType::from_vir_type_id(VirTypeId::STRING, &table), None);
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

    // -----------------------------------------------------------------------
    // Type query helpers
    // -----------------------------------------------------------------------

    #[test]
    fn union_predicate_and_unwrap() {
        let mut table = test_table();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::STRING],
            },
            None,
        );
        assert!(vir_is_union(union_ty, &table));
        assert!(!vir_is_union(VirTypeId::I64, &table));

        let variants = vir_unwrap_union(union_ty, &table).unwrap();
        assert_eq!(variants, &[VirTypeId::I64, VirTypeId::STRING]);
        assert!(vir_unwrap_union(VirTypeId::I64, &table).is_none());
    }

    #[test]
    fn optional_predicate_and_unwrap() {
        let mut table = test_table();
        let opt_ty = table.intern(
            VirType::Optional {
                inner: VirTypeId::STRING,
            },
            None,
        );
        assert!(vir_is_optional(opt_ty, &table));
        assert!(!vir_is_optional(VirTypeId::STRING, &table));

        assert_eq!(vir_unwrap_optional(opt_ty, &table), Some(VirTypeId::STRING));
        assert!(vir_unwrap_optional(VirTypeId::I64, &table).is_none());
    }

    #[test]
    fn string_predicate() {
        let table = test_table();
        assert!(vir_is_string(VirTypeId::STRING, &table));
        assert!(!vir_is_string(VirTypeId::I64, &table));
        assert!(!vir_is_string(VirTypeId::BOOL, &table));
    }

    #[test]
    fn array_predicate_and_unwrap() {
        let mut table = test_table();
        let arr_ty = table.intern(
            VirType::Array {
                elem: VirTypeId::I32,
            },
            None,
        );
        assert!(vir_is_array(arr_ty, &table));
        assert!(!vir_is_array(VirTypeId::I64, &table));

        assert_eq!(vir_unwrap_array(arr_ty, &table), Some(VirTypeId::I32));
        assert!(vir_unwrap_array(VirTypeId::STRING, &table).is_none());
    }

    #[test]
    fn class_predicate_and_unwrap() {
        let mut table = test_table();
        let def = TypeDefId::new(42);
        let class_ty = table.intern(
            VirType::Class {
                def,
                type_args: vec![VirTypeId::STRING],
            },
            None,
        );
        assert!(vir_is_class(class_ty, &table));
        assert!(!vir_is_class(VirTypeId::I64, &table));

        let (d, args) = vir_unwrap_class(class_ty, &table).unwrap();
        assert_eq!(d, def);
        assert_eq!(args, &[VirTypeId::STRING]);
        assert!(vir_unwrap_class(VirTypeId::STRING, &table).is_none());
    }

    #[test]
    fn struct_predicate_and_unwrap() {
        let mut table = test_table();
        let def = TypeDefId::new(10);
        let struct_ty = table.intern(
            VirType::Struct {
                def,
                type_args: vec![],
            },
            None,
        );
        assert!(vir_is_struct(struct_ty, &table));
        assert!(!vir_is_struct(VirTypeId::I64, &table));

        let (d, args) = vir_unwrap_struct(struct_ty, &table).unwrap();
        assert_eq!(d, def);
        assert!(args.is_empty());
        assert!(vir_unwrap_struct(VirTypeId::STRING, &table).is_none());
    }

    #[test]
    fn interface_predicate_and_unwrap() {
        let mut table = test_table();
        let def = TypeDefId::new(7);
        let iface_ty = table.intern(
            VirType::Interface {
                def,
                type_args: vec![VirTypeId::I64],
            },
            None,
        );
        assert!(vir_is_interface(iface_ty, &table));
        assert!(!vir_is_interface(VirTypeId::STRING, &table));

        let (d, args) = vir_unwrap_interface(iface_ty, &table).unwrap();
        assert_eq!(d, def);
        assert_eq!(args, &[VirTypeId::I64]);
        assert!(vir_unwrap_interface(VirTypeId::I64, &table).is_none());
    }

    #[test]
    fn nil_predicate() {
        let table = test_table();
        assert!(vir_is_nil(VirTypeId::NIL, &table));
        assert!(!vir_is_nil(VirTypeId::I64, &table));
        assert!(!vir_is_nil(VirTypeId::VOID, &table));
    }

    #[test]
    fn fallible_predicate_and_unwrap() {
        let mut table = test_table();
        let err_def = TypeDefId::new(99);
        let err_ty = table.intern(VirType::Error { def: err_def }, None);
        let fallible_ty = table.intern(
            VirType::Fallible {
                success: VirTypeId::STRING,
                errors: vec![err_ty],
            },
            None,
        );
        assert!(vir_is_fallible(fallible_ty, &table));
        assert!(!vir_is_fallible(VirTypeId::I64, &table));

        let (success, errors) = vir_unwrap_fallible(fallible_ty, &table).unwrap();
        assert_eq!(success, VirTypeId::STRING);
        assert_eq!(errors, &[err_ty]);
        assert!(vir_unwrap_fallible(VirTypeId::I64, &table).is_none());
    }

    #[test]
    fn function_predicate() {
        let mut table = test_table();
        let fn_ty = table.intern(
            VirType::Function {
                params: vec![VirTypeId::I64],
                ret: VirTypeId::STRING,
            },
            None,
        );
        assert!(vir_is_function(fn_ty, &table));
        assert!(!vir_is_function(VirTypeId::I64, &table));
    }

    #[test]
    fn error_predicate() {
        let mut table = test_table();
        let err_ty = table.intern(
            VirType::Error {
                def: TypeDefId::new(50),
            },
            None,
        );
        assert!(vir_is_error(err_ty, &table));
        assert!(!vir_is_error(VirTypeId::I64, &table));
    }

    #[test]
    fn runtime_iterator_predicate() {
        let mut table = test_table();
        let iter_ty = table.intern(
            VirType::RuntimeIterator {
                elem: VirTypeId::I64,
            },
            None,
        );
        assert!(vir_is_runtime_iterator(iter_ty, &table));
        assert!(!vir_is_runtime_iterator(VirTypeId::I64, &table));
    }

    #[test]
    fn unknown_predicate() {
        let table = test_table();
        assert!(vir_is_unknown(VirTypeId::UNKNOWN, &table));
        assert!(!vir_is_unknown(VirTypeId::I64, &table));
        assert!(!vir_is_unknown(VirTypeId::STRING, &table));
        assert!(!vir_is_unknown(VirTypeId::F128, &table));
    }

    #[test]
    fn predicates_are_mutually_exclusive_for_reserved() {
        let table = test_table();
        // Verify that reserved types don't overlap between predicates
        assert!(!vir_is_union(VirTypeId::STRING, &table));
        assert!(!vir_is_optional(VirTypeId::STRING, &table));
        assert!(!vir_is_fallible(VirTypeId::STRING, &table));
        assert!(!vir_is_array(VirTypeId::STRING, &table));
        assert!(!vir_is_class(VirTypeId::STRING, &table));
        assert!(!vir_is_struct(VirTypeId::STRING, &table));
        assert!(!vir_is_interface(VirTypeId::STRING, &table));
        assert!(!vir_is_nil(VirTypeId::STRING, &table));
        assert!(!vir_is_error(VirTypeId::STRING, &table));
        assert!(vir_is_string(VirTypeId::STRING, &table));
    }

    // -----------------------------------------------------------------------
    // Void predicate
    // -----------------------------------------------------------------------

    #[test]
    fn void_predicate() {
        let table = test_table();
        assert!(vir_is_void(VirTypeId::VOID, &table));
        assert!(!vir_is_void(VirTypeId::I64, &table));
        assert!(!vir_is_void(VirTypeId::NIL, &table));
    }

    // -----------------------------------------------------------------------
    // Class-or-struct helpers
    // -----------------------------------------------------------------------

    #[test]
    fn class_or_struct_predicate() {
        let mut table = test_table();
        let def = TypeDefId::new(10);
        let struct_ty = table.intern(
            VirType::Struct {
                def,
                type_args: vec![],
            },
            None,
        );
        let class_ty = table.intern(
            VirType::Class {
                def,
                type_args: vec![VirTypeId::I64],
            },
            None,
        );
        assert!(vir_is_class_or_struct(struct_ty, &table));
        assert!(vir_is_class_or_struct(class_ty, &table));
        assert!(!vir_is_class_or_struct(VirTypeId::I64, &table));
        assert!(!vir_is_class_or_struct(VirTypeId::STRING, &table));
    }

    #[test]
    fn unwrap_class_or_struct() {
        let mut table = test_table();
        let def_s = TypeDefId::new(5);
        let def_c = TypeDefId::new(6);
        let struct_ty = table.intern(
            VirType::Struct {
                def: def_s,
                type_args: vec![],
            },
            None,
        );
        let class_ty = table.intern(
            VirType::Class {
                def: def_c,
                type_args: vec![VirTypeId::STRING],
            },
            None,
        );

        let (d, args) = vir_unwrap_class_or_struct(struct_ty, &table).unwrap();
        assert_eq!(d, def_s);
        assert!(args.is_empty());

        let (d, args) = vir_unwrap_class_or_struct(class_ty, &table).unwrap();
        assert_eq!(d, def_c);
        assert_eq!(args, &[VirTypeId::STRING]);

        assert!(vir_unwrap_class_or_struct(VirTypeId::I64, &table).is_none());
    }

    // -----------------------------------------------------------------------
    // vir_unwrap_nominal
    // -----------------------------------------------------------------------

    #[test]
    fn unwrap_nominal_class() {
        let mut table = test_table();
        let def = TypeDefId::new(42);
        let class_ty = table.intern(
            VirType::Class {
                def,
                type_args: vec![],
            },
            None,
        );
        assert_eq!(vir_unwrap_nominal(class_ty, &table), Some(def));
    }

    #[test]
    fn unwrap_nominal_struct() {
        let mut table = test_table();
        let def = TypeDefId::new(7);
        let struct_ty = table.intern(
            VirType::Struct {
                def,
                type_args: vec![],
            },
            None,
        );
        assert_eq!(vir_unwrap_nominal(struct_ty, &table), Some(def));
    }

    #[test]
    fn unwrap_nominal_interface() {
        let mut table = test_table();
        let def = TypeDefId::new(99);
        let iface_ty = table.intern(
            VirType::Interface {
                def,
                type_args: vec![],
            },
            None,
        );
        assert_eq!(vir_unwrap_nominal(iface_ty, &table), Some(def));
    }

    #[test]
    fn unwrap_nominal_non_nominal() {
        let table = test_table();
        assert!(vir_unwrap_nominal(VirTypeId::I64, &table).is_none());
        assert!(vir_unwrap_nominal(VirTypeId::STRING, &table).is_none());
        assert!(vir_unwrap_nominal(VirTypeId::UNKNOWN, &table).is_none());
    }

    // -----------------------------------------------------------------------
    // vir_unwrap_runtime_iterator
    // -----------------------------------------------------------------------

    #[test]
    fn unwrap_runtime_iterator() {
        let mut table = test_table();
        let iter_ty = table.intern(
            VirType::RuntimeIterator {
                elem: VirTypeId::STRING,
            },
            None,
        );
        assert_eq!(
            vir_unwrap_runtime_iterator(iter_ty, &table),
            Some(VirTypeId::STRING)
        );
        assert!(vir_unwrap_runtime_iterator(VirTypeId::I64, &table).is_none());
    }

    // -----------------------------------------------------------------------
    // vir_unwrap_function_ret
    // -----------------------------------------------------------------------

    #[test]
    fn unwrap_function_ret() {
        let mut table = test_table();
        let fn_ty = table.intern(
            VirType::Function {
                params: vec![VirTypeId::I64],
                ret: VirTypeId::STRING,
            },
            None,
        );
        assert_eq!(
            vir_unwrap_function_ret(fn_ty, &table),
            Some(VirTypeId::STRING)
        );
        assert!(vir_unwrap_function_ret(VirTypeId::I64, &table).is_none());
    }

    // -----------------------------------------------------------------------
    // vir_is_wide_fallible
    // -----------------------------------------------------------------------

    #[test]
    fn wide_fallible_true() {
        let mut table = test_table();
        let err_ty = table.intern(
            VirType::Error {
                def: TypeDefId::new(1),
            },
            None,
        );
        let fallible = table.intern(
            VirType::Fallible {
                success: VirTypeId::I128,
                errors: vec![err_ty],
            },
            None,
        );
        assert!(vir_is_wide_fallible(fallible, &table));
    }

    #[test]
    fn wide_fallible_false_narrow_success() {
        let mut table = test_table();
        let err_ty = table.intern(
            VirType::Error {
                def: TypeDefId::new(1),
            },
            None,
        );
        let fallible = table.intern(
            VirType::Fallible {
                success: VirTypeId::I64,
                errors: vec![err_ty],
            },
            None,
        );
        assert!(!vir_is_wide_fallible(fallible, &table));
    }

    #[test]
    fn wide_fallible_false_non_fallible() {
        let table = test_table();
        assert!(!vir_is_wide_fallible(VirTypeId::I64, &table));
    }

    // -----------------------------------------------------------------------
    // vir_is_payload_union
    // -----------------------------------------------------------------------

    #[test]
    fn payload_union_true() {
        let mut table = test_table();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::NIL],
            },
            None,
        );
        assert!(vir_is_payload_union(union_ty, &table));
    }

    #[test]
    fn payload_union_false_all_sentinels() {
        let mut table = test_table();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::NIL, VirTypeId::DONE],
            },
            None,
        );
        assert!(!vir_is_payload_union(union_ty, &table));
    }

    #[test]
    fn payload_union_false_non_union() {
        let table = test_table();
        assert!(!vir_is_payload_union(VirTypeId::I64, &table));
    }

    // -----------------------------------------------------------------------
    // vir_unknown_type_tag
    // -----------------------------------------------------------------------

    #[test]
    fn unknown_tag_string() {
        use vole_runtime::value::RuntimeTypeId;
        let table = test_table();
        assert_eq!(
            vir_unknown_type_tag(VirTypeId::STRING, &table),
            RuntimeTypeId::String as u64
        );
    }

    #[test]
    fn unknown_tag_i64() {
        use vole_runtime::value::RuntimeTypeId;
        let table = test_table();
        assert_eq!(
            vir_unknown_type_tag(VirTypeId::I64, &table),
            RuntimeTypeId::I64 as u64
        );
    }

    #[test]
    fn unknown_tag_f64() {
        use vole_runtime::value::RuntimeTypeId;
        let table = test_table();
        assert_eq!(
            vir_unknown_type_tag(VirTypeId::F64, &table),
            RuntimeTypeId::F64 as u64
        );
    }

    #[test]
    fn unknown_tag_bool() {
        use vole_runtime::value::RuntimeTypeId;
        let table = test_table();
        assert_eq!(
            vir_unknown_type_tag(VirTypeId::BOOL, &table),
            RuntimeTypeId::Bool as u64
        );
    }

    #[test]
    fn unknown_tag_array() {
        use vole_runtime::value::RuntimeTypeId;
        let mut table = test_table();
        let arr_ty = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );
        assert_eq!(
            vir_unknown_type_tag(arr_ty, &table),
            RuntimeTypeId::Array as u64
        );
    }

    #[test]
    fn unknown_tag_class() {
        use vole_runtime::value::RuntimeTypeId;
        let mut table = test_table();
        let class_ty = table.intern(
            VirType::Class {
                def: TypeDefId::new(1),
                type_args: vec![],
            },
            None,
        );
        assert_eq!(
            vir_unknown_type_tag(class_ty, &table),
            RuntimeTypeId::Instance as u64
        );
    }

    // -----------------------------------------------------------------------
    // vir_display_basic
    // -----------------------------------------------------------------------

    #[test]
    fn display_basic_primitives() {
        let table = test_table();
        assert_eq!(vir_display_basic(VirTypeId::I64, &table), "i64");
        assert_eq!(vir_display_basic(VirTypeId::STRING, &table), "string");
        assert_eq!(vir_display_basic(VirTypeId::BOOL, &table), "bool");
        assert_eq!(vir_display_basic(VirTypeId::VOID, &table), "void");
        assert_eq!(vir_display_basic(VirTypeId::NIL, &table), "nil");
        assert_eq!(vir_display_basic(VirTypeId::NEVER, &table), "never");
    }

    #[test]
    fn display_basic_compound() {
        let mut table = test_table();
        let class_ty = table.intern(
            VirType::Class {
                def: TypeDefId::new(42),
                type_args: vec![],
            },
            None,
        );
        assert!(vir_display_basic(class_ty, &table).starts_with("Class("));
    }

    // -----------------------------------------------------------------------
    // vir_compute_rc_state
    // -----------------------------------------------------------------------

    use crate::types::vir_struct_helpers::VirStructEntityLookup;
    use vole_identity::{NameId, TypeDefId};
    use vole_vir::entity_metadata::VirTypeDef;

    /// Minimal VirStructEntityLookup for tests that don't need VirTypeDef
    /// or field name resolution.
    struct NullEntities;

    impl VirStructEntityLookup for NullEntities {
        fn is_sentinel_type_def(&self, _type_def_id: TypeDefId) -> bool {
            false
        }
        fn last_segment(&self, _name_id: NameId) -> Option<String> {
            None
        }
        fn vir_type_def(&self, _type_def_id: TypeDefId) -> Option<&VirTypeDef> {
            None
        }
    }

    #[test]
    fn rc_state_primitives_not_rc() {
        let table = test_table();
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(VirTypeId::I8, &table, &entities),
            RcState::None
        );
        assert_eq!(
            vir_compute_rc_state(VirTypeId::I64, &table, &entities),
            RcState::None
        );
        assert_eq!(
            vir_compute_rc_state(VirTypeId::BOOL, &table, &entities),
            RcState::None
        );
        assert_eq!(
            vir_compute_rc_state(VirTypeId::F64, &table, &entities),
            RcState::None
        );
    }

    #[test]
    fn rc_state_string_is_simple_capture() {
        let table = test_table();
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(VirTypeId::STRING, &table, &entities),
            RcState::Simple { is_capture: true }
        );
    }

    #[test]
    fn rc_state_handle_is_simple_not_capture() {
        let table = test_table();
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(VirTypeId::HANDLE, &table, &entities),
            RcState::Simple { is_capture: false }
        );
    }

    #[test]
    fn rc_state_void_not_rc() {
        let table = test_table();
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(VirTypeId::VOID, &table, &entities),
            RcState::None
        );
    }

    #[test]
    fn rc_state_array_is_simple_capture() {
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
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(arr, &table, &entities),
            RcState::Simple { is_capture: true }
        );
    }

    #[test]
    fn rc_state_class_is_simple_capture() {
        let mut table = test_table();
        let class_ty = table.intern(
            VirType::Class {
                def: TypeDefId::new(42),
                type_args: vec![],
            },
            None,
        );
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(class_ty, &table, &entities),
            RcState::Simple { is_capture: true }
        );
    }

    #[test]
    fn rc_state_union_with_no_rc_variants() {
        let mut table = test_table();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::BOOL],
            },
            None,
        );
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(union_ty, &table, &entities),
            RcState::None
        );
    }

    #[test]
    fn rc_state_union_with_rc_variant() {
        let mut table = test_table();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::STRING],
            },
            None,
        );
        let entities = NullEntities;
        match vir_compute_rc_state(union_ty, &table, &entities) {
            RcState::Union { rc_variants } => {
                assert!(!rc_variants.is_empty());
                // String is at index 1
                assert!(rc_variants.contains(&(1u8, false)));
            }
            other => panic!("Expected RcState::Union, got {:?}", other),
        }
    }

    #[test]
    fn rc_state_fixed_array_of_rc_type() {
        let mut table = test_table();
        let fa = table.intern(
            VirType::FixedArray {
                elem: VirTypeId::STRING,
                len: 3,
            },
            None,
        );
        let entities = NullEntities;
        match vir_compute_rc_state(fa, &table, &entities) {
            RcState::Composite {
                shallow_offsets,
                deep_offsets,
                ..
            } => {
                assert_eq!(shallow_offsets, vec![0, 8, 16]);
                assert_eq!(deep_offsets, vec![0, 8, 16]);
            }
            other => panic!("Expected RcState::Composite, got {:?}", other),
        }
    }

    #[test]
    fn rc_state_fixed_array_of_non_rc_type() {
        let mut table = test_table();
        let fa = table.intern(
            VirType::FixedArray {
                elem: VirTypeId::I64,
                len: 3,
            },
            None,
        );
        let entities = NullEntities;
        assert_eq!(vir_compute_rc_state(fa, &table, &entities), RcState::None);
    }

    #[test]
    fn rc_state_tuple_with_mixed_types() {
        let mut table = test_table();
        let tuple_ty = table.intern(
            VirType::Tuple {
                elems: vec![VirTypeId::I64, VirTypeId::STRING, VirTypeId::BOOL],
            },
            None,
        );
        let entities = NullEntities;
        match vir_compute_rc_state(tuple_ty, &table, &entities) {
            RcState::Composite {
                shallow_offsets,
                deep_offsets,
                ..
            } => {
                // String is at offset 8 (after i64)
                assert_eq!(shallow_offsets, vec![8]);
                assert_eq!(deep_offsets, vec![8]);
            }
            other => panic!("Expected RcState::Composite, got {:?}", other),
        }
    }

    #[test]
    fn rc_state_tuple_with_no_rc_types() {
        let mut table = test_table();
        let tuple_ty = table.intern(
            VirType::Tuple {
                elems: vec![VirTypeId::I64, VirTypeId::BOOL],
            },
            None,
        );
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(tuple_ty, &table, &entities),
            RcState::None
        );
    }

    #[test]
    fn rc_state_range_not_rc() {
        let table = test_table();
        let entities = NullEntities;
        assert_eq!(
            vir_compute_rc_state(VirTypeId::RANGE, &table, &entities),
            RcState::None
        );
    }
}
