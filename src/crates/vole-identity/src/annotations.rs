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
