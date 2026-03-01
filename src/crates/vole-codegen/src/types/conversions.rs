// types/conversions.rs
//
// Type conversion and resolution utilities for code generation.

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use rustc_hash::FxHashMap;

use crate::AnalyzedProgram;
use crate::errors::{CodegenError, CodegenResult};
use crate::structs::helpers::StructEntityLookup;
use crate::union_layout;
use vole_frontend::{Interner, Symbol};
use vole_identity::{FieldId, ModuleId, NameId, NameTable, TypeDefId, TypeId, VirTypeId};
use vole_runtime::native_registry::NativeType;
use vole_sema::type_arena::TypeArena;

use super::codegen_state::TypeMetadataMap;
use crate::ops::{sextend_const, uextend_const};

pub(crate) trait TypeEntityLookup: StructEntityLookup {
    fn field_ids_on_type(&self, type_def_id: TypeDefId) -> Vec<FieldId>;
    fn field_type(&self, field_id: FieldId) -> TypeId;
    fn type_name_id(&self, type_def_id: TypeDefId) -> NameId;
}

impl TypeEntityLookup for AnalyzedProgram {
    fn field_ids_on_type(&self, type_def_id: TypeDefId) -> Vec<FieldId> {
        self.entity_field_ids_on_type(type_def_id)
    }

    fn field_type(&self, field_id: FieldId) -> TypeId {
        self.entity_field_type(field_id)
    }

    fn type_name_id(&self, type_def_id: TypeDefId) -> NameId {
        self.entity_type_name_id(type_def_id)
    }
}

#[cfg(test)]
impl TypeEntityLookup for vole_sema::entity_registry::EntityRegistry {
    fn field_ids_on_type(&self, type_def_id: TypeDefId) -> Vec<FieldId> {
        self.fields_on_type(type_def_id).collect()
    }

    fn field_type(&self, field_id: FieldId) -> TypeId {
        self.get_field(field_id).ty
    }

    fn type_name_id(&self, type_def_id: TypeDefId) -> NameId {
        self.name_id(type_def_id)
    }
}

/// Lifecycle state for reference-counted values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RcLifecycle {
    /// Fresh allocation — caller must consume or auto-drop
    Owned,
    /// Borrow from existing binding — rc_inc already emitted
    Borrowed,
    /// Handed off (assigned, returned, passed) — no further action
    Consumed,
    /// Non-RC type, or explicitly opted out
    Untracked,
}

/// Compiled value with its type
#[derive(Clone, Copy)]
pub struct CompiledValue {
    pub value: Value,
    pub ty: Type,
    /// The Vole type of this value (interned TypeId handle - use arena to query).
    /// Migration: being replaced by `vir_type_id` (vol-zlly).
    pub type_id: TypeId,
    /// The VIR type of this value (proper VirTypeId from VirTypeTable).
    pub vir_type_id: VirTypeId,
    /// Lifecycle state for reference-counted values.
    pub rc_lifecycle: RcLifecycle,
    /// Debug-only flag: set by `mark_consumed()` to catch accidental RC ops
    /// on values whose ownership has already been transferred to a container.
    #[cfg(debug_assertions)]
    consumed: bool,
}

impl CompiledValue {
    /// Create a compiled value (not an RC temporary).
    pub fn new(value: Value, ty: Type, type_id: TypeId, vir_type_id: VirTypeId) -> Self {
        Self {
            value,
            ty,
            type_id,
            vir_type_id,
            rc_lifecycle: RcLifecycle::Untracked,
            #[cfg(debug_assertions)]
            consumed: false,
        }
    }

    /// Create a compiled value marked as an RC temporary that needs cleanup.
    pub fn owned(value: Value, ty: Type, type_id: TypeId, vir_type_id: VirTypeId) -> Self {
        Self {
            value,
            ty,
            type_id,
            vir_type_id,
            rc_lifecycle: RcLifecycle::Owned,
            #[cfg(debug_assertions)]
            consumed: false,
        }
    }

    /// Create a new CompiledValue with a different value but the same types
    pub fn with_value(&self, value: Value) -> Self {
        Self {
            value,
            ty: self.ty,
            type_id: self.type_id,
            vir_type_id: self.vir_type_id,
            rc_lifecycle: RcLifecycle::Untracked,
            #[cfg(debug_assertions)]
            consumed: false,
        }
    }

    /// Return a copy with the given VIR type ID set.
    pub fn with_vir_type(mut self, vir_type_id: VirTypeId) -> Self {
        self.vir_type_id = vir_type_id;
        self
    }

    /// Whether this value has Owned lifecycle.
    pub fn is_owned(&self) -> bool {
        self.rc_lifecycle == RcLifecycle::Owned
    }

    /// Whether this value has Borrowed lifecycle.
    pub fn is_borrowed(&self) -> bool {
        self.rc_lifecycle == RcLifecycle::Borrowed
    }

    /// Whether this value is tracked (Owned or Borrowed).
    pub fn is_tracked(&self) -> bool {
        matches!(
            self.rc_lifecycle,
            RcLifecycle::Owned | RcLifecycle::Borrowed
        )
    }

    /// Mark this value as a borrow from an existing binding.
    pub fn mark_borrowed(&mut self) {
        self.rc_lifecycle = RcLifecycle::Borrowed;
    }

    /// Mark this value as consumed — no further RC action needed.
    pub fn mark_consumed(&mut self) {
        self.rc_lifecycle = RcLifecycle::Consumed;
        #[cfg(debug_assertions)]
        {
            self.consumed = true;
        }
    }

    /// Debug-only: assert that this value has not been consumed.
    /// Panics in debug builds if an RC operation is attempted on a consumed value.
    #[inline]
    #[cfg(debug_assertions)]
    pub fn debug_assert_not_consumed(&self, op: &str) {
        debug_assert!(
            !self.consumed,
            "RC op `{op}` on consumed value (type_id={:?}, lifecycle={:?})",
            self.type_id, self.rc_lifecycle,
        );
    }

    /// Debug assertion that this value's RC lifecycle has been handled.
    /// Panics in debug builds if the value is still Owned or Borrowed,
    /// meaning a codegen path forgot to consume or clean up the value.
    #[inline]
    pub fn debug_assert_rc_handled(&self, context: &str) {
        debug_assert!(
            !self.is_tracked(),
            "Unhandled RC value at {context}: lifecycle={:?} type_id={:?}",
            self.rc_lifecycle,
            self.type_id,
        );
    }
}

/// Metadata about a class type for code generation
#[derive(Debug, Clone)]
pub(crate) struct TypeMetadata {
    /// Unique type ID for runtime
    pub type_id: u32,
    /// Map from field name to physical slot index (i128 fields use 2 consecutive slots)
    pub field_slots: FxHashMap<String, usize>,
    /// Total number of physical u64 slots (may be > field_slots.len() when i128 fields exist)
    pub physical_slot_count: usize,
    /// The Vole type (Class) - interned TypeId handle
    pub vole_type: TypeId,
    /// Method info: method name -> method info
    pub method_infos: FxHashMap<NameId, MethodInfo>,
}

/// Metadata for a compiled method (opaque function key)
/// Return type is looked up from sema on demand.
#[derive(Debug, Clone, Copy)]
pub(crate) struct MethodInfo {
    pub func_key: crate::FunctionKey,
}

/// Look up TypeMetadata by NameId (cross-interner safe)
/// Returns the TypeMetadata for a class with the given name_id
pub(crate) fn type_metadata_by_name_id(
    type_metadata: &TypeMetadataMap,
    name_id: NameId,
) -> Option<&TypeMetadata> {
    tracing::trace!(?name_id, "type_metadata_by_name_id lookup");
    let result = type_metadata.get_by_name_id(name_id);
    if result.is_none() {
        tracing::debug!(?name_id, "type_metadata_by_name_id: no match found");
    }
    result
}

pub(crate) fn module_name_id(
    analyzed: &AnalyzedProgram,
    module_id: ModuleId,
    name: &str,
) -> Option<NameId> {
    let module_interner = analyzed.module_interner(module_id)?;
    let sym = module_interner.lookup(name)?;
    analyzed
        .name_table()
        .name_id(module_id, &[sym], module_interner)
}

/// Look up a method NameId by string name (cross-interner safe)
pub(crate) fn method_name_id_by_str(
    analyzed: &AnalyzedProgram,
    interner: &Interner,
    name_str: &str,
) -> Option<NameId> {
    let name_table = analyzed.name_table();
    vole_identity::method_name_id_by_str(name_table, interner, name_str)
}

/// Convert a TypeId to a Cranelift type.
///
/// # Panics
///
/// Panics if the TypeId is INVALID, which indicates a sema bug where an unknown
/// type was not properly reported as an error.
pub(crate) fn type_id_to_cranelift(ty: TypeId, arena: &TypeArena, pointer_type: Type) -> Type {
    // Defensive check: INVALID types should never reach codegen.
    // If they do, it means sema failed to report an error for an unknown type.
    if ty.is_invalid() {
        panic!(
            "internal error: received invalid type ID (this is a sema bug - \
             unknown types should be reported as errors before reaching codegen)"
        );
    }
    // Sentinel types are always represented as i8 (zero-field struct tag),
    // regardless of whether they've been rebound to SemaType::Struct by the prelude.
    if arena.is_sentinel(ty) {
        return types::I8;
    }

    match ty {
        TypeId::I8 | TypeId::U8 => return types::I8,
        TypeId::I16 | TypeId::U16 => return types::I16,
        TypeId::I32 | TypeId::U32 => return types::I32,
        TypeId::I64 | TypeId::U64 => return types::I64,
        TypeId::I128 => return types::I128,
        TypeId::F32 => return types::F32,
        TypeId::F64 => return types::F64,
        TypeId::F128 => return types::F128,
        TypeId::BOOL => return types::I8,
        TypeId::STRING => return pointer_type,
        _ => {}
    }

    use vole_sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        // Pointer-sized types: heap-allocated (String, Handle, Interface, Union, etc.),
        // stack-allocated via pointer (Struct, FixedArray, Tuple, Fallible, Range),
        // or boxed (Unknown as TaggedValue).
        ArenaType::Handle
        | ArenaType::Interface { .. }
        | ArenaType::Union(_)
        | ArenaType::Fallible { .. }
        | ArenaType::Function { .. }
        | ArenaType::Range
        | ArenaType::Tuple(_)
        | ArenaType::FixedArray { .. }
        | ArenaType::Struct { .. }
        | ArenaType::Unknown
        // Heap-allocated nominal types passed by reference:
        | ArenaType::Class { .. }
        | ArenaType::Error { .. }
        | ArenaType::Array(_)
        | ArenaType::RuntimeIterator(_) => pointer_type,
        // Erased generic type parameters: appear in uninstantiated generic function
        // signatures and bodies before monomorphization.  Use pointer_type as the
        // erased representation so the signature is consistent with monomorphized
        // call sites that pass any value type.
        ArenaType::TypeParam(_) | ArenaType::TypeParamRef(_) => pointer_type,
        // Void: a zero-return type.  Callers typically check is_void() separately and
        // avoid emitting a value; this arm provides a harmless I64 placeholder for
        // call sites that query the Cranelift type unconditionally before branching.
        ArenaType::Void => types::I64,
        // Unresolved inference placeholders that escaped sema: treat as pointer-erased.
        // Ideally sema would resolve all placeholders before codegen; this is a safety net.
        ArenaType::Placeholder(_) => pointer_type,
        // Bottom type and sema-internal types.  These should not appear as value types
        // in codegen; treat as pointer-erased to preserve prior behaviour.
        // Note: `Never` appears in unreachable branches; `MetaType` is the type of types.
        ArenaType::Never
        | ArenaType::MetaType
        | ArenaType::Module(_)
        | ArenaType::Structural(_)
        | ArenaType::Invalid { .. }
        | ArenaType::Primitive(_) => pointer_type,
    }
}

/// Check if a type requires 2 u64 slots in class instance storage.
/// Currently only i128 (128-bit integer) is wider than a single u64.
pub(crate) fn is_wide_type(ty: TypeId, _arena: &TypeArena) -> bool {
    matches!(ty, TypeId::I128 | TypeId::F128)
}

/// Get the byte size of a field: 16 for i128 (wide) types, 8 for all others.
pub(crate) fn field_byte_size(ty: TypeId, arena: &TypeArena) -> u32 {
    if is_wide_type(ty, arena) { 16 } else { 8 }
}

/// Get the slot count of a field: 2 for i128 (wide) types, 1 for all others.
pub(crate) fn field_slot_count(ty: TypeId, arena: &TypeArena) -> usize {
    if is_wide_type(ty, arena) { 2 } else { 1 }
}

/// Check if a fallible type has a wide (i128) success type.
/// Returns true if the type is `fallible(i128, ...)`.
/// When true, the fallible return convention uses 3 i64 registers instead of 2
/// to carry (tag, payload_low, payload_high).
pub(crate) fn is_wide_fallible(ty: TypeId, arena: &TypeArena) -> bool {
    arena
        .unwrap_fallible(ty)
        .is_some_and(|(success_type_id, _)| is_wide_type(success_type_id, arena))
}

/// Sum the byte sizes of all fields in an error type definition.
fn error_fields_size(
    type_def_id: TypeDefId,
    pointer_type: Type,
    entities: &impl TypeEntityLookup,
    arena: &TypeArena,
) -> u32 {
    entities
        .field_ids_on_type(type_def_id)
        .into_iter()
        .map(|field_id| {
            let field_type = entities.field_type(field_id);
            type_id_size(field_type, pointer_type, entities, arena)
        })
        .sum()
}

/// Get the size in bytes for a TypeId.
///
/// # Panics
///
/// Panics if the TypeId is INVALID, which indicates a sema bug where an unknown
/// type was not properly reported as an error.
pub(crate) fn type_id_size(
    ty: TypeId,
    pointer_type: Type,
    entities: &impl TypeEntityLookup,
    arena: &TypeArena,
) -> u32 {
    // Defensive check: INVALID types should never reach codegen.
    if ty.is_invalid() {
        panic!(
            "internal error: received invalid type ID in type_id_size (this is a sema bug - \
             unknown types should be reported as errors before reaching codegen)"
        );
    }
    // Sentinel types are zero-sized,
    // regardless of whether they've been rebound to SemaType::Struct by the prelude.
    if arena.is_sentinel(ty) {
        return 0;
    }

    match ty {
        TypeId::I8 | TypeId::U8 | TypeId::BOOL => return 1,
        TypeId::I16 | TypeId::U16 => return 2,
        TypeId::I32 | TypeId::U32 | TypeId::F32 => return 4,
        TypeId::I64 | TypeId::U64 | TypeId::F64 => return 8,
        TypeId::I128 | TypeId::F128 => return 16,
        TypeId::STRING => return pointer_type.bytes(),
        _ => {}
    }

    use vole_sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Array(_) => pointer_type.bytes(),
        ArenaType::Handle => pointer_type.bytes(),
        ArenaType::Interface { .. } => pointer_type.bytes(),
        ArenaType::Void => 0,
        ArenaType::Range => 16,
        ArenaType::Union(variants) => {
            let max_payload = variants
                .iter()
                .map(|&t| {
                    // Struct variants are auto-boxed, so their payload is a pointer.
                    // Use arena.is_struct() which excludes well-known sentinels (Done, nil).
                    if arena.is_struct(t) {
                        pointer_type.bytes()
                    } else {
                        type_id_size(t, pointer_type, entities, arena)
                    }
                })
                .max()
                .unwrap_or(0);
            union_layout::TAG_ONLY_SIZE + max_payload.div_ceil(8) * 8
        }
        ArenaType::Error { type_def_id } => {
            error_fields_size(*type_def_id, pointer_type, entities, arena).div_ceil(8) * 8
        }
        ArenaType::Fallible { success, error } => {
            let success_size = type_id_size(*success, pointer_type, entities, arena);
            let error_size = match arena.get(*error) {
                ArenaType::Error { type_def_id } => {
                    error_fields_size(*type_def_id, pointer_type, entities, arena)
                }
                ArenaType::Union(variants) => variants
                    .iter()
                    .filter_map(|&v| match arena.get(v) {
                        ArenaType::Error { type_def_id } => Some(error_fields_size(
                            *type_def_id,
                            pointer_type,
                            entities,
                            arena,
                        )),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0),
                _ => 0,
            };
            let max_payload = success_size.max(error_size);
            union_layout::TAG_ONLY_SIZE + max_payload.div_ceil(8) * 8
        }
        ArenaType::Tuple(elements) => elements
            .iter()
            .map(|&t| type_id_size(t, pointer_type, entities, arena).div_ceil(8) * 8)
            .sum(),
        ArenaType::FixedArray { element, size } => {
            let elem_size = type_id_size(*element, pointer_type, entities, arena).div_ceil(8) * 8;
            elem_size * (*size as u32)
        }
        // Struct types: use flat slot count to account for nested struct fields
        ArenaType::Struct { .. } => {
            crate::structs::struct_total_byte_size(ty, arena, entities)
                .expect("INTERNAL: valid struct must have computable size")
        }
        // Unknown type uses TaggedValue representation: 8-byte tag + 8-byte value = 16 bytes
        ArenaType::Unknown => 16,
        // Heap-allocated nominal types passed by reference (pointer-sized).
        ArenaType::Class { .. }
        | ArenaType::RuntimeIterator(_)
        // Closures/functions are fat-pointer-like objects stored as a pointer.
        | ArenaType::Function { .. } => pointer_type.bytes(),
        // Erased generic type parameters: appear in uninstantiated generic function
        // bodies before monomorphization.  Use pointer_type as the erased size.
        ArenaType::TypeParam(_) | ArenaType::TypeParamRef(_) => pointer_type.bytes(),
        // Unresolved inference placeholders, bottom type, and sema-internal types.
        // These should not appear as sized value types, but treat as pointer-erased
        // to preserve prior behaviour and avoid a hard crash.
        ArenaType::Placeholder(_)
        | ArenaType::Never
        | ArenaType::MetaType
        | ArenaType::Module(_)
        | ArenaType::Structural(_)
        | ArenaType::Invalid { .. }
        | ArenaType::Primitive(_) => pointer_type.bytes(),
    }
}

/// Calculate layout for tuple elements using TypeId.
/// Returns (total_size, offsets) where offsets[i] is the byte offset for element i.
/// Each element is aligned to 8 bytes for simplicity.
pub(crate) fn tuple_layout_id(
    elements: &[TypeId],
    pointer_type: Type,
    entities: &impl TypeEntityLookup,
    arena: &TypeArena,
) -> (u32, Vec<i32>) {
    let mut offsets = Vec::with_capacity(elements.len());
    let mut offset = 0i32;

    for &elem in elements {
        offsets.push(offset);
        let elem_size = type_id_size(elem, pointer_type, entities, arena).div_ceil(8) * 8;
        offset += elem_size as i32;
    }

    (offset as u32, offsets)
}

// ============================================================================
// Fallible type layout helpers
// ============================================================================

/// Tag value for success in a fallible type (payload is the success value)
pub(crate) const FALLIBLE_SUCCESS_TAG: i64 = 0;

/// Offset of the tag field in a fallible value (always 0)
pub(crate) const FALLIBLE_TAG_OFFSET: i32 = 0;

/// Offset of the payload field in a fallible value (always 8, after the i64 tag)
pub(crate) const FALLIBLE_PAYLOAD_OFFSET: i32 = 8;

/// Load the tag field from a fallible value.
/// The tag is an i64 at offset 0: 0 = success, 1+ = error variants.
#[inline]
pub(crate) fn load_fallible_tag(builder: &mut FunctionBuilder, value: Value) -> Value {
    builder
        .ins()
        .load(types::I64, MemFlags::new(), value, FALLIBLE_TAG_OFFSET)
}

/// Load the payload field from a fallible value.
/// The payload is at offset 8 (after the i64 tag).
#[inline]
pub(crate) fn load_fallible_payload(
    builder: &mut FunctionBuilder,
    value: Value,
    payload_ty: Type,
) -> Value {
    builder
        .ins()
        .load(payload_ty, MemFlags::new(), value, FALLIBLE_PAYLOAD_OFFSET)
}

/// Returns the 1-based index (tag 0 is reserved for success).
///
/// Takes the error part of a fallible type as a TypeId and uses arena queries
/// to determine the tag for the given error_name.
pub(crate) fn fallible_error_tag_by_id(
    error_type_id: TypeId,
    error_name: Symbol,
    arena: &TypeArena,
    interner: &Interner,
    name_table: &NameTable,
    entities: &impl TypeEntityLookup,
) -> Option<i64> {
    let error_name_str = interner.resolve(error_name);

    // Check if error_type_id is a single Error type
    if let Some(type_def_id) = arena.unwrap_error(error_type_id) {
        let info_name = name_table.last_segment_str(entities.type_name_id(type_def_id));
        if info_name.as_deref() == Some(error_name_str) {
            return Some(1); // Single error type always gets tag 1
        }
        return None;
    }

    // Check if error_type_id is a Union of error types
    if let Some(variants) = arena.unwrap_union(error_type_id) {
        for (idx, &variant) in variants.iter().enumerate() {
            if let Some(type_def_id) = arena.unwrap_error(variant) {
                let info_name = name_table.last_segment_str(entities.type_name_id(type_def_id));
                if info_name.as_deref() == Some(error_name_str) {
                    return Some((idx + 1) as i64);
                }
            }
        }
        return None;
    }

    None
}

/// Convert a compiled value to a target Cranelift type
pub(crate) fn convert_to_type(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    target: Type,
    arena: &TypeArena,
) -> Value {
    fn pack_f64_to_f128(builder: &mut FunctionBuilder, f64_val: Value) -> Value {
        // Runtime f128 currently uses a compact software representation:
        // low 64 bits = f64 payload, high 64 bits = 0.
        let bits64 = builder.ins().bitcast(types::I64, MemFlags::new(), f64_val);
        let bits128 = uextend_const(builder, types::I128, bits64);
        builder.ins().bitcast(types::F128, MemFlags::new(), bits128)
    }

    fn unpack_f128_to_f64(builder: &mut FunctionBuilder, f128_val: Value) -> Value {
        // Reverse of pack_f64_to_f128: read low 64-bit payload as f64 bits.
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
        // Convert int to float
        if val.ty == types::I64 || val.ty == types::I32 {
            return builder.ins().fcvt_from_sint(types::F64, val.value);
        }
        // Convert f128 to f64
        if val.ty == types::F128 {
            return unpack_f128_to_f64(builder, val.value);
        }
        // Convert f32 to f64
        if val.ty == types::F32 {
            return builder.ins().fpromote(types::F64, val.value);
        }
    }

    if target == types::F32 {
        if val.ty == types::F128 {
            let f64_val = unpack_f128_to_f64(builder, val.value);
            return builder.ins().fdemote(types::F32, f64_val);
        }
        // Convert f64 to f32
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
                // x64 lowering has no i128->float conversion path; use low 64 bits.
                let low = builder.ins().ireduce(types::I64, val.value);
                builder.ins().fcvt_from_sint(types::F64, low)
            } else {
                builder.ins().fcvt_from_sint(types::F64, val.value)
            };
            return pack_f64_to_f128(builder, f64_val);
        }
    }

    // Integer widening - use uextend for unsigned types, sextend for signed
    if target.is_int() && val.ty.is_int() && target.bits() > val.ty.bits() {
        if arena.is_unsigned(val.type_id) {
            return uextend_const(builder, target, val.value);
        } else {
            return sextend_const(builder, target, val.value);
        }
    }

    // Integer narrowing
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
pub(crate) fn value_to_word(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    pointer_type: Type,
    heap_alloc_ref: Option<FuncRef>,
    arena: &TypeArena,
    entities: &impl TypeEntityLookup,
) -> CodegenResult<Value> {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let value_size = type_id_size(value.type_id, pointer_type, entities, arena);
    let needs_box = value_size > word_bytes;

    if needs_box {
        // If the Cranelift type is already a pointer and the Vole type needs boxing,
        // then the value is already a pointer to boxed data (e.g., from external functions
        // returning unions). Just return it directly - don't double-box.
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

    let word = match value.type_id {
        TypeId::F64 => builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), value.value),
        TypeId::F32 => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            uextend_const(builder, word_type, i32_val)
        }
        TypeId::BOOL
        | TypeId::I8
        | TypeId::U8
        | TypeId::I16
        | TypeId::U16
        | TypeId::I32
        | TypeId::U32 => {
            // Only extend if the Cranelift value isn't already word-sized
            if value.ty == word_type {
                value.value
            } else {
                uextend_const(builder, word_type, value.value)
            }
        }
        TypeId::I64 | TypeId::U64 => value.value,
        TypeId::I128 => {
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

/// Convert a uniform word representation back into a typed value using TypeId.
/// Convert a word-sized value to its proper Cranelift type.
pub(crate) fn word_to_value_type_id(
    builder: &mut FunctionBuilder,
    word: Value,
    type_id: TypeId,
    pointer_type: Type,
    entities: &impl TypeEntityLookup,
    arena: &TypeArena,
) -> Value {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let needs_unbox = type_id_size(type_id, pointer_type, entities, arena) > word_bytes;

    if needs_unbox {
        // If the target Cranelift type is pointer_type (e.g., unions), the word is
        // already a pointer to the data - just return it, don't load from it.
        let target_type = type_id_to_cranelift(type_id, arena, pointer_type);
        if target_type == pointer_type {
            return word;
        }
        return builder.ins().load(target_type, MemFlags::new(), word, 0);
    }

    match type_id {
        TypeId::F64 => builder.ins().bitcast(types::F64, MemFlags::new(), word),
        TypeId::F32 => {
            let i32_val = builder.ins().ireduce(types::I32, word);
            builder.ins().bitcast(types::F32, MemFlags::new(), i32_val)
        }
        TypeId::BOOL | TypeId::I8 | TypeId::U8 => builder.ins().ireduce(types::I8, word),
        TypeId::I16 | TypeId::U16 => builder.ins().ireduce(types::I16, word),
        TypeId::I32 | TypeId::U32 => builder.ins().ireduce(types::I32, word),
        TypeId::I64 | TypeId::U64 => word,
        TypeId::I128 => {
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

/// Get the runtime tag value for an array element type.
/// These tags must match the `RuntimeTypeId` variants in `vole_runtime::value`
/// so that `tag_needs_rc` correctly identifies RC-managed elements for cleanup
/// in `array_drop`.
pub(crate) fn array_element_tag_id(ty: TypeId, arena: &TypeArena) -> i64 {
    use vole_runtime::value::RuntimeTypeId;
    use vole_sema::type_arena::SemaType as ArenaType;
    // Handle type uses a special TypeId sentinel, check before SemaType match
    if arena.is_handle(ty) {
        return RuntimeTypeId::Rng as i64;
    }
    // Sentinel types (nil, Done, user-defined) are non-RC stack values
    if arena.is_sentinel(ty) {
        return RuntimeTypeId::I64 as i64;
    }
    if ty == TypeId::STRING {
        return RuntimeTypeId::String as i64;
    }
    if matches!(ty, TypeId::I64 | TypeId::I32 | TypeId::I16 | TypeId::I8) {
        return RuntimeTypeId::I64 as i64;
    }
    if matches!(ty, TypeId::I128 | TypeId::F128) {
        return RuntimeTypeId::Wide128 as i64;
    }
    if matches!(ty, TypeId::F64 | TypeId::F32) {
        return RuntimeTypeId::F64 as i64;
    }
    if ty == TypeId::BOOL {
        return RuntimeTypeId::Bool as i64;
    }
    match arena.get(ty) {
        ArenaType::Array(_) => RuntimeTypeId::Array as i64,
        ArenaType::Function { .. } => RuntimeTypeId::Closure as i64,
        ArenaType::Class { .. } => RuntimeTypeId::Instance as i64,
        // Union values boxed by codegen use raw heap buffers (tag+payload), not
        // RcHeader-prefixed allocations. Tagged as RuntimeTypeId::UnionHeap so array_drop
        // calls union_heap_cleanup (which frees the buffer and conditionally
        // rc_dec's the RC payload inside).
        ArenaType::Union(_) => RuntimeTypeId::UnionHeap as i64,
        // Unknown values are heap-allocated TaggedValues [tag: u64, value: u64].
        // Tagged as UnknownHeap so array_drop calls unknown_heap_cleanup.
        ArenaType::Unknown => RuntimeTypeId::UnknownHeap as i64,
        _ => RuntimeTypeId::I64 as i64,
    }
}

// ============================================================================
// Unknown type (TaggedValue) helpers
// ============================================================================

/// Get the runtime tag for boxing a value into the unknown type (TaggedValue).
/// Returns the tag that should be stored in the TaggedValue.tag field.
pub(crate) fn unknown_type_tag(ty: TypeId, arena: &TypeArena) -> u64 {
    use vole_runtime::value::RuntimeTypeId;
    use vole_sema::type_arena::SemaType as ArenaType;
    if ty == TypeId::STRING {
        return RuntimeTypeId::String as u64;
    }
    if matches!(
        ty,
        TypeId::I64
            | TypeId::I32
            | TypeId::I16
            | TypeId::I8
            | TypeId::U64
            | TypeId::U32
            | TypeId::U16
            | TypeId::U8
    ) {
        return RuntimeTypeId::I64 as u64;
    }
    if matches!(ty, TypeId::F64 | TypeId::F32) {
        return RuntimeTypeId::F64 as u64;
    }
    if ty == TypeId::BOOL {
        return RuntimeTypeId::Bool as u64;
    }
    match arena.get(ty) {
        ArenaType::Array(_) | ArenaType::FixedArray { .. } => RuntimeTypeId::Array as u64,
        ArenaType::Function { .. } => RuntimeTypeId::Closure as u64,
        ArenaType::Class { .. } => RuntimeTypeId::Instance as u64,
        // For other types (nil, done, tuples, unions, structs, etc.), default to I64 representation
        _ => RuntimeTypeId::I64 as u64,
    }
}

/// Convert NativeType to Cranelift type.
/// Shared utility for external function calls in both compiler.rs and context.rs.
pub(crate) fn native_type_to_cranelift(nt: &NativeType, pointer_type: Type) -> Type {
    match nt {
        NativeType::I8 => types::I8,
        NativeType::I16 => types::I16,
        NativeType::I32 => types::I32,
        NativeType::I64 => types::I64,
        NativeType::I128 => types::I128,
        NativeType::U8 => types::I8,
        NativeType::U16 => types::I16,
        NativeType::U32 => types::I32,
        NativeType::U64 => types::I64,
        NativeType::F32 => types::F32,
        NativeType::F64 => types::F64,
        NativeType::F128 => types::F128,
        NativeType::Bool => types::I8,
        NativeType::String => pointer_type,
        NativeType::Handle => pointer_type,
        NativeType::Nil => types::I8, // Nil uses I8 as placeholder
        NativeType::Optional(_) => types::I64, // Optionals are boxed
        NativeType::Array(_) => pointer_type,
        // Struct returns use pointer type (the actual return convention
        // is handled by call_native_indirect_struct)
        NativeType::Struct { .. } => pointer_type,
    }
}
