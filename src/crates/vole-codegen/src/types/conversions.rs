// types/conversions.rs
//
// Type conversion and resolution utilities for code generation.

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::AnalyzedProgram;
use vole_frontend::Interner;
use vole_identity::{ModuleId, NameId, TypeId, VirTypeId};
use vole_runtime::native_registry::NativeType;

use super::codegen_state::TypeMetadataMap;
use crate::ops::{sextend_const, uextend_const};

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
    /// The VIR type of this value (proper VirTypeId from VirTypeTable).
    pub type_id: VirTypeId,
    /// Lifecycle state for reference-counted values.
    pub rc_lifecycle: RcLifecycle,
    /// Debug-only flag: set by `mark_consumed()` to catch accidental RC ops
    /// on values whose ownership has already been transferred to a container.
    #[cfg(debug_assertions)]
    consumed: bool,
}

impl CompiledValue {
    /// Create a compiled value (not an RC temporary).
    pub fn new(value: Value, ty: Type, type_id: VirTypeId) -> Self {
        Self {
            value,
            ty,
            type_id,
            rc_lifecycle: RcLifecycle::Untracked,
            #[cfg(debug_assertions)]
            consumed: false,
        }
    }

    /// Create a compiled value marked as an RC temporary that needs cleanup.
    pub fn owned(value: Value, ty: Type, type_id: VirTypeId) -> Self {
        Self {
            value,
            ty,
            type_id,
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
            rc_lifecycle: RcLifecycle::Untracked,
            #[cfg(debug_assertions)]
            consumed: false,
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

/// Convert a compiled value to a target Cranelift type
pub(crate) fn convert_to_type(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    target: Type,
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
        if val.type_id.is_unsigned_int() {
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
