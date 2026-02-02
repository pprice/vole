// types/conversions.rs
//
// Type conversion and resolution utilities for code generation.

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use rustc_hash::FxHashMap;

use crate::AnalyzedProgram;
use crate::errors::CodegenError;
use vole_frontend::{Interner, Symbol};
use vole_identity::{ModuleId, NameId, NameTable, NamerLookup, TypeDefId};
use vole_runtime::native_registry::NativeType;
use vole_sema::type_arena::{TypeArena, TypeId};
use vole_sema::{EntityRegistry, PrimitiveType};

use super::TypeCtx;
use super::codegen_state::TypeMetadataMap;

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
    /// The Vole type of this value (interned TypeId handle - use arena to query)
    pub type_id: TypeId,
    /// Lifecycle state for reference-counted values.
    pub rc_lifecycle: RcLifecycle,
}

impl CompiledValue {
    /// Create a compiled value (not an RC temporary).
    pub fn new(value: Value, ty: Type, type_id: TypeId) -> Self {
        Self {
            value,
            ty,
            type_id,
            rc_lifecycle: RcLifecycle::Untracked,
        }
    }

    /// Create a compiled value marked as an RC temporary that needs cleanup.
    pub fn owned(value: Value, ty: Type, type_id: TypeId) -> Self {
        Self {
            value,
            ty,
            type_id,
            rc_lifecycle: RcLifecycle::Owned,
        }
    }

    /// Alias for `owned`.
    #[allow(dead_code)]
    pub fn temp(value: Value, ty: Type, type_id: TypeId) -> Self {
        Self::owned(value, ty, type_id)
    }

    /// Create a new CompiledValue with a different value but the same types
    pub fn with_value(&self, value: Value) -> Self {
        Self {
            value,
            ty: self.ty,
            type_id: self.type_id,
            rc_lifecycle: RcLifecycle::Untracked,
        }
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
    /// Map from field name to slot index
    pub field_slots: FxHashMap<String, usize>,
    /// The Vole type (Class) - interned TypeId handle
    pub vole_type: TypeId,
    /// TypeDefId for sema lookups (method return types, etc.)
    pub type_def_id: TypeDefId,
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
pub(crate) fn type_metadata_by_name_id<'a>(
    type_metadata: &'a TypeMetadataMap,
    name_id: NameId,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> Option<&'a TypeMetadata> {
    tracing::trace!(
        ?name_id,
        count = type_metadata.len(),
        "type_metadata_by_name_id lookup"
    );
    let result = type_metadata.values().find(|meta| {
        // Use arena queries to check if this is a class with matching name_id
        if let Some((type_def_id, _)) = arena.unwrap_class(meta.vole_type) {
            let class_name_id = entity_registry.get_type(type_def_id).name_id;
            tracing::trace!(target_name_id = ?name_id, class_name_id = ?class_name_id, "comparing class name_id");
            return class_name_id == name_id;
        }
        false
    });
    if result.is_none() {
        // Log all class name_ids for debugging
        let class_name_ids: Vec<_> = type_metadata
            .values()
            .filter_map(|meta| {
                arena
                    .unwrap_class(meta.vole_type)
                    .map(|(type_def_id, _)| entity_registry.get_type(type_def_id).name_id)
            })
            .collect();
        tracing::debug!(
            ?name_id,
            ?class_name_ids,
            "type_metadata_by_name_id: no match found"
        );
    }
    result
}

pub(crate) fn module_name_id(
    analyzed: &AnalyzedProgram,
    module_id: ModuleId,
    name: &str,
) -> Option<NameId> {
    let query = analyzed.query();
    let module_path = query.module_path(module_id);
    let (_, module_interner) = query.module_program(&module_path)?;
    let sym = module_interner.lookup(name)?;
    analyzed
        .name_table()
        .name_id(module_id, &[sym], module_interner)
}

/// Look up a method NameId by Symbol with explicit interner (for cross-interner usage)
pub(crate) fn method_name_id_with_interner(
    analyzed: &AnalyzedProgram,
    interner: &Interner,
    name: Symbol,
) -> Option<NameId> {
    let name_table = analyzed.name_table();
    let namer = NamerLookup::new(name_table, interner);
    namer.method(name)
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

/// Look up a function NameId by Symbol with explicit interner (for cross-interner usage)
pub(crate) fn function_name_id_with_interner(
    analyzed: &AnalyzedProgram,
    interner: &Interner,
    module: ModuleId,
    name: Symbol,
) -> Option<NameId> {
    let name_table = analyzed.name_table();
    let namer = NamerLookup::new(name_table, interner);
    namer.function(module, name)
}

/// Convert a TypeId to a Cranelift type.
pub(crate) fn type_id_to_cranelift(ty: TypeId, arena: &TypeArena, pointer_type: Type) -> Type {
    // Sentinel types are always represented as i8 (zero-field struct tag),
    // regardless of whether they've been rebound to SemaType::Struct by the prelude.
    if arena.is_sentinel(ty) {
        return types::I8;
    }
    use vole_sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::I8) | ArenaType::Primitive(PrimitiveType::U8) => {
            types::I8
        }
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => {
            types::I16
        }
        ArenaType::Primitive(PrimitiveType::I32) | ArenaType::Primitive(PrimitiveType::U32) => {
            types::I32
        }
        ArenaType::Primitive(PrimitiveType::I64) | ArenaType::Primitive(PrimitiveType::U64) => {
            types::I64
        }
        ArenaType::Primitive(PrimitiveType::I128) => types::I128,
        ArenaType::Primitive(PrimitiveType::F32) => types::F32,
        ArenaType::Primitive(PrimitiveType::F64) => types::F64,
        ArenaType::Primitive(PrimitiveType::Bool) => types::I8,
        ArenaType::Primitive(PrimitiveType::String) => pointer_type,
        ArenaType::Handle => pointer_type,
        ArenaType::Interface { .. } => pointer_type,
        ArenaType::Union(_) => pointer_type,
        ArenaType::Fallible { .. } => pointer_type,
        ArenaType::Function { .. } => pointer_type,
        ArenaType::Range => pointer_type,
        ArenaType::Tuple(_) => pointer_type,
        ArenaType::FixedArray { .. } => pointer_type,
        // Struct types are stack-allocated, represented as pointers
        ArenaType::Struct { .. } => pointer_type,
        // Unknown type uses TaggedValue (16 bytes: tag + value), stored via pointer
        ArenaType::Unknown => pointer_type,
        _ => types::I64,
    }
}

/// Get the size in bytes for a TypeId.
pub(crate) fn type_id_size(
    ty: TypeId,
    pointer_type: Type,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> u32 {
    // Sentinel types are zero-sized,
    // regardless of whether they've been rebound to SemaType::Struct by the prelude.
    if arena.is_sentinel(ty) {
        return 0;
    }
    use vole_sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::I8)
        | ArenaType::Primitive(PrimitiveType::U8)
        | ArenaType::Primitive(PrimitiveType::Bool) => 1,
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => 2,
        ArenaType::Primitive(PrimitiveType::I32)
        | ArenaType::Primitive(PrimitiveType::U32)
        | ArenaType::Primitive(PrimitiveType::F32) => 4,
        ArenaType::Primitive(PrimitiveType::I64)
        | ArenaType::Primitive(PrimitiveType::U64)
        | ArenaType::Primitive(PrimitiveType::F64) => 8,
        ArenaType::Primitive(PrimitiveType::I128) => 16,
        ArenaType::Primitive(PrimitiveType::String) | ArenaType::Array(_) => pointer_type.bytes(),
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
                        type_id_size(t, pointer_type, entity_registry, arena)
                    }
                })
                .max()
                .unwrap_or(0);
            8 + max_payload.div_ceil(8) * 8
        }
        ArenaType::Error { type_def_id } => {
            let fields_size: u32 = entity_registry
                .fields_on_type(*type_def_id)
                .map(|field_id| {
                    let field = entity_registry.get_field(field_id);
                    type_id_size(field.ty, pointer_type, entity_registry, arena)
                })
                .sum();
            fields_size.div_ceil(8) * 8
        }
        ArenaType::Fallible { success, error } => {
            let success_size = type_id_size(*success, pointer_type, entity_registry, arena);
            let error_size = match arena.get(*error) {
                ArenaType::Error { type_def_id } => entity_registry
                    .fields_on_type(*type_def_id)
                    .map(|field_id| {
                        let field = entity_registry.get_field(field_id);
                        type_id_size(field.ty, pointer_type, entity_registry, arena)
                    })
                    .sum(),
                ArenaType::Union(variants) => variants
                    .iter()
                    .filter_map(|&v| match arena.get(v) {
                        ArenaType::Error { type_def_id } => {
                            let size: u32 = entity_registry
                                .fields_on_type(*type_def_id)
                                .map(|field_id| {
                                    let field = entity_registry.get_field(field_id);
                                    type_id_size(field.ty, pointer_type, entity_registry, arena)
                                })
                                .sum();
                            Some(size)
                        }
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0),
                _ => 0,
            };
            let max_payload = success_size.max(error_size);
            8 + max_payload.div_ceil(8) * 8
        }
        ArenaType::Tuple(elements) => elements
            .iter()
            .map(|&t| type_id_size(t, pointer_type, entity_registry, arena).div_ceil(8) * 8)
            .sum(),
        ArenaType::FixedArray { element, size } => {
            let elem_size =
                type_id_size(*element, pointer_type, entity_registry, arena).div_ceil(8) * 8;
            elem_size * (*size as u32)
        }
        // Struct types: use flat slot count to account for nested struct fields
        ArenaType::Struct { .. } => {
            crate::structs::struct_total_byte_size(ty, arena, entity_registry).unwrap_or(8) // fallback: shouldn't happen for valid struct types
        }
        // Unknown type uses TaggedValue representation: 8-byte tag + 8-byte value = 16 bytes
        ArenaType::Unknown => 16,
        _ => 8,
    }
}

/// Calculate layout for tuple elements using TypeId.
/// Returns (total_size, offsets) where offsets[i] is the byte offset for element i.
/// Each element is aligned to 8 bytes for simplicity.
pub(crate) fn tuple_layout_id(
    elements: &[TypeId],
    pointer_type: Type,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> (u32, Vec<i32>) {
    let mut offsets = Vec::with_capacity(elements.len());
    let mut offset = 0i32;

    for &elem in elements {
        offsets.push(offset);
        let elem_size = type_id_size(elem, pointer_type, entity_registry, arena).div_ceil(8) * 8;
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

/// Get the error tag for a specific error type within a fallible type.
/// Get error tag using TypeCtx - preferred API.
#[allow(dead_code)]
pub(crate) fn fallible_error_tag_with_ctx(
    error_type_id: TypeId,
    error_name: Symbol,
    type_ctx: &TypeCtx,
) -> Option<i64> {
    let arena = type_ctx.arena();
    let interner = type_ctx.interner();
    let entity_registry = type_ctx.entities();
    fallible_error_tag_by_id(
        error_type_id,
        error_name,
        arena,
        interner,
        type_ctx.name_table_rc(),
        entity_registry,
    )
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
    entity_registry: &EntityRegistry,
) -> Option<i64> {
    let error_name_str = interner.resolve(error_name);

    // Check if error_type_id is a single Error type
    if let Some(type_def_id) = arena.unwrap_error(error_type_id) {
        let info_name = name_table.last_segment_str(entity_registry.name_id(type_def_id));
        if info_name.as_deref() == Some(error_name_str) {
            return Some(1); // Single error type always gets tag 1
        }
        return None;
    }

    // Check if error_type_id is a Union of error types
    if let Some(variants) = arena.unwrap_union(error_type_id) {
        for (idx, &variant) in variants.iter().enumerate() {
            if let Some(type_def_id) = arena.unwrap_error(variant) {
                let info_name = name_table.last_segment_str(entity_registry.name_id(type_def_id));
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
    if val.ty == target {
        return val.value;
    }

    if target == types::F64 {
        // Convert int to float
        if val.ty == types::I64 || val.ty == types::I32 {
            return builder.ins().fcvt_from_sint(types::F64, val.value);
        }
        // Convert f32 to f64
        if val.ty == types::F32 {
            return builder.ins().fpromote(types::F64, val.value);
        }
    }

    if target == types::F32 {
        // Convert f64 to f32
        if val.ty == types::F64 {
            return builder.ins().fdemote(types::F32, val.value);
        }
    }

    // Integer widening - use uextend for unsigned types, sextend for signed
    if target.is_int() && val.ty.is_int() && target.bits() > val.ty.bits() {
        if arena.is_unsigned(val.type_id) {
            return builder.ins().uextend(target, val.value);
        } else {
            return builder.ins().sextend(target, val.value);
        }
    }

    // Integer narrowing
    if target.is_int() && val.ty.is_int() && target.bits() < val.ty.bits() {
        return builder.ins().ireduce(target, val.value);
    }

    val.value
}

/// Convert a value to a uniform word representation using TypeCtx.
#[allow(dead_code)]
pub(crate) fn value_to_word_with_ctx(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    type_ctx: &TypeCtx,
    heap_alloc_ref: Option<FuncRef>,
) -> Result<Value, String> {
    value_to_word(
        builder,
        value,
        type_ctx.pointer_type,
        heap_alloc_ref,
        type_ctx.query.arena(),
        type_ctx.entities(),
    )
}

/// Convert a value to a uniform word representation for interface dispatch.
pub(crate) fn value_to_word(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    pointer_type: Type,
    heap_alloc_ref: Option<FuncRef>,
    arena: &TypeArena,
    entity_registry: &EntityRegistry,
) -> Result<Value, String> {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let value_size = type_id_size(value.type_id, pointer_type, entity_registry, arena);
    let needs_box = value_size > word_bytes;

    if needs_box {
        // If the Cranelift type is already a pointer and the Vole type needs boxing,
        // then the value is already a pointer to boxed data (e.g., from external functions
        // returning unions). Just return it directly - don't double-box.
        if value.ty == pointer_type {
            return Ok(value.value);
        }
        let Some(heap_alloc_ref) = heap_alloc_ref else {
            return Err(
                CodegenError::missing_resource("heap allocator for interface boxing").into(),
            );
        };
        let size_val = builder.ins().iconst(pointer_type, value_size as i64);
        let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
        let alloc_ptr = builder.inst_results(alloc_call)[0];
        builder
            .ins()
            .store(MemFlags::new(), value.value, alloc_ptr, 0);
        return Ok(alloc_ptr);
    }

    use vole_sema::type_arena::SemaType as ArenaType;
    let word = match arena.get(value.type_id) {
        ArenaType::Primitive(PrimitiveType::F64) => {
            builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), value.value)
        }
        ArenaType::Primitive(PrimitiveType::F32) => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            builder.ins().uextend(word_type, i32_val)
        }
        ArenaType::Primitive(PrimitiveType::Bool) => {
            // Only extend if the Cranelift value isn't already word-sized
            if value.ty == word_type {
                value.value
            } else {
                builder.ins().uextend(word_type, value.value)
            }
        }
        ArenaType::Primitive(PrimitiveType::I8) | ArenaType::Primitive(PrimitiveType::U8) => {
            if value.ty == word_type {
                value.value
            } else {
                builder.ins().uextend(word_type, value.value)
            }
        }
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => {
            if value.ty == word_type {
                value.value
            } else {
                builder.ins().uextend(word_type, value.value)
            }
        }
        ArenaType::Primitive(PrimitiveType::I32) | ArenaType::Primitive(PrimitiveType::U32) => {
            if value.ty == word_type {
                value.value
            } else {
                builder.ins().uextend(word_type, value.value)
            }
        }
        ArenaType::Primitive(PrimitiveType::I64) | ArenaType::Primitive(PrimitiveType::U64) => {
            value.value
        }
        ArenaType::Primitive(PrimitiveType::I128) => {
            let low = builder.ins().ireduce(types::I64, value.value);
            if word_type == types::I64 {
                low
            } else {
                builder.ins().uextend(word_type, low)
            }
        }
        _ => value.value,
    };

    Ok(word)
}

/// Convert a word to typed value using TypeCtx.
#[allow(dead_code)]
pub(crate) fn word_to_value_with_ctx(
    builder: &mut FunctionBuilder,
    word: Value,
    type_id: TypeId,
    type_ctx: &TypeCtx,
) -> Value {
    let arena = type_ctx.arena();
    word_to_value_type_id(
        builder,
        word,
        type_id,
        type_ctx.pointer_type,
        type_ctx.entities(),
        arena,
    )
}

/// Convert a uniform word representation back into a typed value using TypeId.
/// Convert a word-sized value to its proper Cranelift type.
pub(crate) fn word_to_value_type_id(
    builder: &mut FunctionBuilder,
    word: Value,
    type_id: TypeId,
    pointer_type: Type,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> Value {
    use vole_sema::type_arena::SemaType as ArenaType;
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let needs_unbox = type_id_size(type_id, pointer_type, entity_registry, arena) > word_bytes;

    if needs_unbox {
        // If the target Cranelift type is pointer_type (e.g., unions), the word is
        // already a pointer to the data - just return it, don't load from it.
        let target_type = type_id_to_cranelift(type_id, arena, pointer_type);
        if target_type == pointer_type {
            return word;
        }
        return builder.ins().load(target_type, MemFlags::new(), word, 0);
    }

    match arena.get(type_id) {
        ArenaType::Primitive(PrimitiveType::F64) => {
            builder.ins().bitcast(types::F64, MemFlags::new(), word)
        }
        ArenaType::Primitive(PrimitiveType::F32) => {
            let i32_val = builder.ins().ireduce(types::I32, word);
            builder.ins().bitcast(types::F32, MemFlags::new(), i32_val)
        }
        ArenaType::Primitive(PrimitiveType::Bool) => builder.ins().ireduce(types::I8, word),
        ArenaType::Primitive(PrimitiveType::I8) | ArenaType::Primitive(PrimitiveType::U8) => {
            builder.ins().ireduce(types::I8, word)
        }
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => {
            builder.ins().ireduce(types::I16, word)
        }
        ArenaType::Primitive(PrimitiveType::I32) | ArenaType::Primitive(PrimitiveType::U32) => {
            builder.ins().ireduce(types::I32, word)
        }
        ArenaType::Primitive(PrimitiveType::I64) | ArenaType::Primitive(PrimitiveType::U64) => word,
        ArenaType::Primitive(PrimitiveType::I128) => {
            let low = if word_type == types::I64 {
                word
            } else {
                builder.ins().ireduce(types::I64, word)
            };
            builder.ins().uextend(types::I128, low)
        }
        _ => word,
    }
}

/// Get the runtime tag value for an array element type.
/// These tags must match the runtime TYPE_* constants in vole_runtime::value
/// so that `tag_needs_rc` correctly identifies RC-managed elements for cleanup
/// in `array_drop`.
pub(crate) fn array_element_tag_id(ty: TypeId, arena: &TypeArena) -> i64 {
    use vole_sema::type_arena::SemaType as ArenaType;
    // Handle type uses a special TypeId sentinel, check before SemaType match
    if arena.is_handle(ty) {
        return 8; // TYPE_RNG / generic handle
    }
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::String) => 1, // TYPE_STRING
        ArenaType::Primitive(PrimitiveType::I64)
        | ArenaType::Primitive(PrimitiveType::I32)
        | ArenaType::Primitive(PrimitiveType::I16)
        | ArenaType::Primitive(PrimitiveType::I8) => 2, // TYPE_I64
        ArenaType::Primitive(PrimitiveType::F64) | ArenaType::Primitive(PrimitiveType::F32) => 3, // TYPE_F64
        ArenaType::Primitive(PrimitiveType::Bool) => 4, // TYPE_BOOL
        ArenaType::Array(_) => 5,                       // TYPE_ARRAY
        ArenaType::Function { .. } => 6,                // TYPE_CLOSURE
        ArenaType::Class { .. } => 7,                   // TYPE_INSTANCE
        _ => 2,                                         // default to integer for non-RC types
    }
}

// ============================================================================
// Unknown type (TaggedValue) helpers
// ============================================================================

/// Runtime type tags for TaggedValue (used by unknown type).
/// These correspond to vole_runtime::value constants.
pub(crate) mod unknown_tags {
    pub const TAG_STRING: u64 = 1;
    pub const TAG_I64: u64 = 2;
    pub const TAG_F64: u64 = 3;
    pub const TAG_BOOL: u64 = 4;
    pub const TAG_ARRAY: u64 = 5;
    pub const TAG_CLOSURE: u64 = 6;
    pub const TAG_INSTANCE: u64 = 7;
}

/// Get the runtime tag for boxing a value into the unknown type (TaggedValue).
/// Returns the tag that should be stored in the TaggedValue.tag field.
pub(crate) fn unknown_type_tag(ty: TypeId, arena: &TypeArena) -> u64 {
    use vole_sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::String) => unknown_tags::TAG_STRING,
        ArenaType::Primitive(PrimitiveType::I64)
        | ArenaType::Primitive(PrimitiveType::I32)
        | ArenaType::Primitive(PrimitiveType::I16)
        | ArenaType::Primitive(PrimitiveType::I8)
        | ArenaType::Primitive(PrimitiveType::U64)
        | ArenaType::Primitive(PrimitiveType::U32)
        | ArenaType::Primitive(PrimitiveType::U16)
        | ArenaType::Primitive(PrimitiveType::U8) => unknown_tags::TAG_I64,
        ArenaType::Primitive(PrimitiveType::F64) | ArenaType::Primitive(PrimitiveType::F32) => {
            unknown_tags::TAG_F64
        }
        ArenaType::Primitive(PrimitiveType::Bool) => unknown_tags::TAG_BOOL,
        ArenaType::Array(_) | ArenaType::FixedArray { .. } => unknown_tags::TAG_ARRAY,
        ArenaType::Function { .. } => unknown_tags::TAG_CLOSURE,
        ArenaType::Class { .. } => unknown_tags::TAG_INSTANCE,
        // For other types (nil, done, tuples, unions, etc.), default to I64 representation
        _ => unknown_tags::TAG_I64,
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
