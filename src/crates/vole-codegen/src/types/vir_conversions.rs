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

use vole_identity::{TypeDefId, TypeId, TypeIdVec, VirTypeId};
use vole_sema::type_arena::TypeArena;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{StorageClass, VirPrimitiveKind, VirType};

/// Temporary bridge from `VirTypeId` to sema `TypeId`.
///
/// Reserved type IDs are aligned by raw index; dynamic VIR IDs cannot be
/// reliably mapped without a dedicated bridge table, so they degrade to
/// `TypeId::UNKNOWN` for legacy sema-typed code paths.
/// TODO(N279-C): remove after all codegen consumers are `VirTypeId`-native.
pub(crate) fn vir_to_sema_type_id_lossy(vir_ty: VirTypeId) -> TypeId {
    if vir_ty.raw() < TypeId::FIRST_DYNAMIC {
        TypeId::from_raw(vir_ty.raw())
    } else {
        TypeId::UNKNOWN
    }
}

/// Convert a `VirTypeId` to sema `TypeId` using VIR structure and arena lookups.
///
/// This handles both true VIR dynamic IDs (lookup via `VirTypeTable`) and
/// legacy sema-encoded IDs carried in compatibility fields by falling back to
/// raw `TypeId` when the candidate exists in the arena.
pub(crate) fn vir_to_sema_type_id(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    arena: &TypeArena,
) -> TypeId {
    let mapped = vir_to_sema_type_id_lossy(vir_ty);
    if mapped != TypeId::UNKNOWN || vir_ty == VirTypeId::UNKNOWN {
        return mapped;
    }

    let in_vir_table = (vir_ty.raw() as usize) < table.len();
    if in_vir_table {
        let resolved = match table.get(vir_ty) {
            VirType::Primitive(_) => Some(vir_to_sema_type_id_lossy(vir_ty)),
            VirType::Array { elem } => {
                let elem_id = vir_to_sema_type_id(*elem, table, arena);
                arena.lookup_array(elem_id)
            }
            VirType::FixedArray { elem, len } => {
                let elem_id = vir_to_sema_type_id(*elem, table, arena);
                arena.lookup_fixed_array(elem_id, *len as usize)
            }
            VirType::Tuple { elems } => {
                let mapped: TypeIdVec = elems
                    .iter()
                    .map(|&elem| vir_to_sema_type_id(elem, table, arena))
                    .collect();
                arena.lookup_tuple(mapped)
            }
            VirType::Union { variants } => {
                let mapped: TypeIdVec = variants
                    .iter()
                    .map(|&variant| vir_to_sema_type_id(variant, table, arena))
                    .collect();
                arena.lookup_union(mapped)
            }
            VirType::Optional { inner } => {
                let value_id = vir_to_sema_type_id(*inner, table, arena);
                arena.lookup_optional(value_id)
            }
            VirType::Fallible { success, errors } => {
                let success_id = vir_to_sema_type_id(*success, table, arena);
                let error_id = if let [single] = errors.as_slice() {
                    vir_to_sema_type_id(*single, table, arena)
                } else {
                    let mapped_errors: TypeIdVec = errors
                        .iter()
                        .map(|&error_ty| vir_to_sema_type_id(error_ty, table, arena))
                        .collect();
                    arena.lookup_union(mapped_errors).unwrap_or(TypeId::UNKNOWN)
                };
                arena.lookup_fallible(success_id, error_id)
            }
            VirType::Function { params, ret } => {
                let mapped_params: TypeIdVec = params
                    .iter()
                    .map(|&param| vir_to_sema_type_id(param, table, arena))
                    .collect();
                let ret_id = vir_to_sema_type_id(*ret, table, arena);
                arena
                    .lookup_function(mapped_params.clone(), ret_id, false)
                    .or_else(|| arena.lookup_function(mapped_params, ret_id, true))
            }
            VirType::RuntimeIterator { elem } => {
                let elem_id = vir_to_sema_type_id(*elem, table, arena);
                arena.lookup_runtime_iterator(elem_id)
            }
            VirType::Class { def, type_args } => {
                let mapped_args: TypeIdVec = type_args
                    .iter()
                    .map(|&arg| vir_to_sema_type_id(arg, table, arena))
                    .collect();
                arena.lookup_class(*def, mapped_args)
            }
            VirType::Struct { def, type_args } => {
                let mapped_args: TypeIdVec = type_args
                    .iter()
                    .map(|&arg| vir_to_sema_type_id(arg, table, arena))
                    .collect();
                arena.lookup_struct(*def, mapped_args)
            }
            VirType::Interface { def, type_args } => {
                let mapped_args: TypeIdVec = type_args
                    .iter()
                    .map(|&arg| vir_to_sema_type_id(arg, table, arena))
                    .collect();
                arena.lookup_interface(*def, mapped_args)
            }
            VirType::Error { def } => arena.lookup_error(*def),
            VirType::Range => Some(TypeId::RANGE),
            VirType::MetaType => Some(TypeId::METATYPE),
            VirType::Never => Some(TypeId::NEVER),
            VirType::Void => Some(TypeId::VOID),
            VirType::Nil => Some(TypeId::NIL),
            VirType::Done => Some(TypeId::DONE),
            VirType::Unknown => Some(TypeId::UNKNOWN),
            VirType::Param { name } => arena.lookup_type_param(*name).or(Some(TypeId::UNKNOWN)),
        };
        if let Some(id) = resolved {
            return id;
        }

        // For true VIR type IDs present in the table, raw-ID fallback is only
        // safe when the sema candidate has a compatible shape. This keeps
        // legacy compat behavior for same-kind IDs while avoiding accidental
        // reinterpretation (e.g. VIR Array ID colliding with sema Interface ID).
        let candidate = TypeId::from_raw(vir_ty.raw());
        let candidate_exists = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = arena.get(candidate);
        }))
        .is_ok();
        if candidate_exists && raw_fallback_kind_matches(vir_ty, candidate, table, arena) {
            return candidate;
        }

        return TypeId::UNKNOWN;
    }

    let candidate = TypeId::from_raw(vir_ty.raw());
    let candidate_exists = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = arena.get(candidate);
    }))
    .is_ok();
    if candidate_exists {
        candidate
    } else {
        TypeId::UNKNOWN
    }
}

fn raw_fallback_kind_matches(
    vir_ty: VirTypeId,
    candidate: TypeId,
    table: &VirTypeTable,
    arena: &TypeArena,
) -> bool {
    match table.get(vir_ty) {
        VirType::Primitive(kind) => match kind {
            VirPrimitiveKind::I8 => candidate == TypeId::I8,
            VirPrimitiveKind::I16 => candidate == TypeId::I16,
            VirPrimitiveKind::I32 => candidate == TypeId::I32,
            VirPrimitiveKind::I64 => candidate == TypeId::I64,
            VirPrimitiveKind::I128 => candidate == TypeId::I128,
            VirPrimitiveKind::U8 => candidate == TypeId::U8,
            VirPrimitiveKind::U16 => candidate == TypeId::U16,
            VirPrimitiveKind::U32 => candidate == TypeId::U32,
            VirPrimitiveKind::U64 => candidate == TypeId::U64,
            VirPrimitiveKind::F32 => candidate == TypeId::F32,
            VirPrimitiveKind::F64 => candidate == TypeId::F64,
            VirPrimitiveKind::Bool => candidate == TypeId::BOOL,
            VirPrimitiveKind::String => candidate == TypeId::STRING,
            VirPrimitiveKind::Handle => candidate == TypeId::HANDLE,
        },
        VirType::Array { elem } => {
            let Some(candidate_elem) = arena.unwrap_array(candidate) else {
                return false;
            };
            let expected_elem = vir_to_sema_type_id(*elem, table, arena);
            expected_elem == TypeId::UNKNOWN || candidate_elem == expected_elem
        }
        VirType::FixedArray { elem, len } => {
            let Some((candidate_elem, candidate_len)) = arena.unwrap_fixed_array(candidate) else {
                return false;
            };
            let expected_elem = vir_to_sema_type_id(*elem, table, arena);
            candidate_len == *len as usize
                && (expected_elem == TypeId::UNKNOWN || candidate_elem == expected_elem)
        }
        VirType::Tuple { .. } => arena.unwrap_tuple(candidate).is_some(),
        VirType::Union { .. } => {
            arena.unwrap_union(candidate).is_some() && !arena.is_optional(candidate)
        }
        VirType::Optional { .. } => arena.is_optional(candidate),
        VirType::Fallible { .. } => arena.unwrap_fallible(candidate).is_some(),
        VirType::Function { .. } => arena.is_function(candidate),
        VirType::RuntimeIterator { .. } => arena.is_runtime_iterator(candidate),
        VirType::Class { .. } => arena.is_class(candidate),
        VirType::Struct { .. } => arena.is_struct(candidate),
        VirType::Interface { .. } => arena.is_interface(candidate),
        VirType::Error { .. } => arena.is_error(candidate),
        VirType::Range => candidate == TypeId::RANGE,
        VirType::MetaType => candidate == TypeId::METATYPE,
        VirType::Never => candidate == TypeId::NEVER,
        VirType::Void => candidate == TypeId::VOID,
        VirType::Nil => candidate == TypeId::NIL,
        VirType::Done => candidate == TypeId::DONE,
        VirType::Unknown => candidate == TypeId::UNKNOWN,
        VirType::Param { .. } => {
            arena.unwrap_type_param(candidate).is_some()
                || arena.unwrap_type_param_ref(candidate).is_some()
        }
    }
}

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
    matches!(table.get(vir_ty), VirType::Struct { .. })
}

/// Unwrap a struct type, returning its `TypeDefId` and type arguments.
///
/// Returns `None` if the type is not a struct.
pub(crate) fn vir_unwrap_struct(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(TypeDefId, &[VirTypeId])> {
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
pub(crate) fn vir_is_nil(vir_ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(table.get(vir_ty), VirType::Nil)
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
/// Returns `None` if the type is neither a class nor a struct.
pub(crate) fn vir_unwrap_class_or_struct(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<(TypeDefId, &[VirTypeId])> {
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
            .any(|&v| !matches!(table.get(v), VirType::Nil | VirType::Done | VirType::Void)),
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
            VirPrimitiveKind::String => "String".into(),
            VirPrimitiveKind::Handle => "Handle".into(),
        },
        VirType::Void => "void".into(),
        VirType::Nil => "nil".into(),
        VirType::Done => "Done".into(),
        VirType::Never => "never".into(),
        VirType::Unknown => "unknown".into(),
        VirType::Range => "Range".into(),
        VirType::MetaType => "TypeMeta".into(),
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

// Struct/class field layout helpers and convert_field_value are in
// types::vir_struct_helpers (split for file size).
// Callers import directly from that submodule.

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
        assert_eq!(vir_display_basic(VirTypeId::STRING, &table), "String");
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
}
