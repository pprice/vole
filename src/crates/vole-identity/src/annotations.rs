// annotations.rs
//
// Sema-computed annotations that flow from sema to VIR to codegen.
//
// These types carry no sema logic — they are pure data enums whose only
// dependency is `TypeId`.  They live in vole-identity so that vole-vir
// can reference them without depending on vole-sema.

use crate::{TypeId, VirTypeId};

/// Result of compile-time analysis for type checks (`is` expressions and type patterns).
///
/// Used by sema to record whether a runtime type check can be eliminated at compile time,
/// or to provide the tag value when a runtime check is needed.
/// Uses `TypeId` (sema's type representation).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsCheckResult {
    /// The check always succeeds (e.g., `x is Int` when x is `Int`).
    AlwaysTrue,
    /// The check always fails (e.g., `x is Int` when x is `String`).
    AlwaysFalse,
    /// Runtime check needed — compare against this union variant tag.
    CheckTag(u32),
    /// Runtime check needed for unknown type — compare against this type's tag.
    /// The `TypeId` indicates what type we're checking for at runtime.
    CheckUnknown(TypeId),
}

/// VIR-level result of an `is` type-check, pre-computed by sema and lowered
/// into VIR nodes.
///
/// Mirrors [`IsCheckResult`] but uses `VirTypeId` (post-lowering type identity)
/// instead of `TypeId`.  The `CheckUnknown` variant carries two IDs:
/// a compat-layer `VirTypeId` (for sema round-trip) and a native `VirTypeId`
/// (for VIR-side rederivation after monomorphization).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirIsCheckResult {
    /// The check always succeeds (e.g. `x is Int` when x is `Int`).
    AlwaysTrue,
    /// The check always fails (e.g. `x is Int` when x is `String`).
    AlwaysFalse,
    /// Runtime check needed: compare against this union variant tag.
    CheckTag(u32),
    /// Runtime check needed for unknown type: compare against this type's
    /// runtime tag.  The first `VirTypeId` is the compat-layer ID; the second
    /// is the native VIR type ID for the tested type.
    CheckUnknown(VirTypeId, VirTypeId),
}

/// Union storage strategy annotation.
///
/// Sema records this per-node so codegen can select the correct memory layout
/// for union-typed values without re-detecting tag collisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnionStorageKind {
    /// Each variant has a unique runtime tag — store inline as (tag, payload).
    Inline,
    /// Tag collision — store as a heap-boxed union buffer pointer.
    Heap,
}

/// Array element storage strategy, pre-computed from the element type.
///
/// Tells codegen how to encode/decode array elements without re-detecting
/// struct, wide, or union types at compile time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArrayStoreStrategy {
    /// Scalar (i8..i64, u8..u64, f32, f64, bool, nil, string, class ptr, etc.).
    /// Store via `convert_to_i64_for_storage`, decode via type-appropriate
    /// ireduce / bitcast.
    DirectScalar,

    /// Value-type struct — must be copied to heap before storing the pointer.
    HeapCopyStruct,

    /// Wide type (i128) — box via `Wide128Box`, unbox via `Wide128Unbox`.
    WideBox,

    /// Union with unique runtime tags — store inline as (variant_tag, payload).
    UnionInline,

    /// Union with tag collisions — store as heap-boxed union buffer pointer.
    UnionBoxed,

    /// The element type is `unknown` — the dynamic tagged-value path.
    Unknown,

    /// Unresolved — used in generic templates before monomorphization.
    /// Codegen falls back to type-based detection.
    Unresolved,
}

/// Element value conversion strategy for decoding iterator/array elements.
///
/// Pre-computed from the element's VIR type so codegen can convert raw i64
/// values (from array storage or `iter_next`) to the correct Cranelift type
/// without type-branching.
///
/// Shared between `VirIterKind` variants and `ArrayStoreStrategy::DirectScalar`
/// decode paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirElemConversion {
    /// Value is already i64 / pointer-width — no conversion needed.
    ///
    /// Applies to: i64, u64, string, class, array, interface, function,
    /// struct (pointer), nil (i8 but stored as i64), unknown, handle, etc.
    Identity,

    /// Bitcast i64 to f64.
    BitcastF64,

    /// Ireduce i64 to i32, then bitcast to f32.
    BitcastF32,

    /// Ireduce i64 to a narrower integer type.
    ///
    /// `bits` is the target width (8, 16, or 32).
    /// Applies to: i8, u8, bool (8), i16, u16 (16), i32, u32 (32).
    ReduceInt { bits: u8 },

    /// Wide type (i128 or f128) — call `Wide128Unbox`, then reinterpret.
    ///
    /// Codegen derives the specific `WideType` from the element's VirTypeId.
    WideUnbox,

    /// Unresolved — used in generic templates before monomorphization.
    /// Codegen falls back to type-based detection.
    Unresolved,
}

/// String interpolation conversion strategy.
///
/// Sema computes the conversion needed for each sub-expression in an
/// interpolated string.  Codegen reads this to emit the correct
/// type-to-string call without re-detecting types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringConversion {
    /// Already a string — no conversion needed.
    Identity,
    /// i64 (or smaller integer widths that sext to i64) -> string
    I64ToString,
    /// i128 -> string
    I128ToString,
    /// f32 -> string
    F32ToString,
    /// f64 -> string
    F64ToString,
    /// f128 -> string (passed as i128 bits)
    F128ToString,
    /// bool -> string
    BoolToString,
    /// nil -> string (always "nil")
    NilToString,
    /// Array -> string
    ArrayToString,
    /// Optional (union with nil) -> branches on tag, converts inner value.
    /// `nil_index` is the tag index for nil in the union variants.
    /// `variants` is the full variant type list for codegen layout.
    /// `inner_conversion` is the conversion for the non-nil variant.
    OptionalToString {
        nil_index: usize,
        variants: Vec<TypeId>,
        inner_conversion: Box<StringConversion>,
    },
    /// General union -> branches on tag, converts each variant.
    /// Each entry is `(variant_type_id, conversion)`.
    UnionToString {
        variants: Vec<(TypeId, StringConversion)>,
    },
    /// Placeholder for generic lowering mode.
    ///
    /// Used when converting `"${x}"` where `x: T` (a type parameter) to a
    /// string.  The concrete conversion strategy is unknown until
    /// monomorphization substitutes `T` with a concrete type.
    Generic { type_id: TypeId },
}

/// Word-encoding strategy for value-to-word / word-to-value conversions.
///
/// Pre-computed from the VIR type so that codegen can dispatch mechanically
/// without re-querying type structure.  Used for interface dispatch boxing
/// (packing a typed value into a uniform pointer-width word and back).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoxingStrategy {
    /// Value is already word-sized or pointer-typed — no conversion.
    ///
    /// Applies to: i64, u64, string, handle, class, array, interface,
    /// function, struct (pointer-passed), union, optional, fallible, tuple,
    /// fixed array, range, unknown, error, iterator, meta type,
    /// void, never.
    Identity,

    /// Zero-extend a smaller integer to word width; ireduce back.
    ///
    /// `from_bits` is the source width (8, 16, or 32).
    /// Applies to: bool, i8, u8, i16, u16, i32, u32.
    Uextend { from_bits: u8 },

    /// Bitcast f64 to i64 (to-word) / i64 to f64 (from-word).
    BitcastF64,

    /// Bitcast f32 to i32 then uextend to word (to-word);
    /// ireduce word to i32 then bitcast to f32 (from-word).
    BitcastF32Extend,

    /// Value is oversized (> word bytes) and its Cranelift type is NOT
    /// pointer_type, so it must be heap-allocated for boxing.
    ///
    /// `size` is the byte count to allocate.
    /// to-word: heap-alloc `size` bytes, store value, return pointer.
    /// from-word: load value from pointer.
    ///
    /// Applies to: i128, f128.
    HeapBox { size: u32 },
}

/// A constant value that can be stored in a module.
///
/// This is the public-facing constant type used by the module system and codegen.
/// It stores the raw value without numeric suffix metadata.
///
/// The optimizer internally uses a richer `ConstValue` type (in `optimizer::constant_folding`)
/// that carries an optional `NumericSuffix` for type-preserving folds. `From` conversions
/// exist between the two types.
///
/// ```ignore
/// // In math.vole:
/// let PI = 3.14159
/// let MAX_SIZE = 1024
/// ```
#[derive(Debug, Clone)]
pub enum ConstantValue {
    I64(i64),
    F64(f64),
    Bool(bool),
    String(String),
}

// Manual PartialEq: compare f64 by bits so NaN == NaN, matching Hash and satisfying Eq.
impl PartialEq for ConstantValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstantValue::I64(a), ConstantValue::I64(b)) => a == b,
            (ConstantValue::F64(a), ConstantValue::F64(b)) => a.to_bits() == b.to_bits(),
            (ConstantValue::Bool(a), ConstantValue::Bool(b)) => a == b,
            (ConstantValue::String(a), ConstantValue::String(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ConstantValue {}

// Manual Hash implementation because f64 doesn't implement Hash
impl std::hash::Hash for ConstantValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            ConstantValue::I64(v) => v.hash(state),
            ConstantValue::F64(v) => v.to_bits().hash(state),
            ConstantValue::Bool(v) => v.hash(state),
            ConstantValue::String(v) => v.hash(state),
        }
    }
}
