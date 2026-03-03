// src/codegen/rc_state.rs
//
// Unified RC state computation for reference-counted types.
//
// This module provides a single enum (RcState) that captures all the different
// ways a type can be reference-counted, along with a compute function that
// analyzes a type once and returns the appropriate state.
//
// All RC queries go through `CodegenContext::rc_state(type_id)` which caches
// the result per TypeId. Accessors on RcState:
// - needs_cleanup() -> bool
// - is_capture() -> bool
// - shallow_offsets() -> Option<&[i32]>
// - deep_offsets() -> Option<&[i32]>
// - union_variants() -> Option<&[(u8, bool)]>

/// Reference counting state for a type.
///
/// Each variant captures a distinct RC management strategy:
/// - `None`: Type is not reference-counted (primitives, sentinels, etc.)
/// - `Simple`: Type is directly RC-managed (string, array, function, class, etc.)
/// - `Composite`: Type contains RC fields at specific byte offsets (struct, tuple, fixed array)
/// - `Union`: Type is a union where some variants are RC-managed
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RcState {
    /// Type is not reference-counted.
    None,

    /// Type is a simple RC value (single pointer to RcHeader-managed heap object).
    ///
    /// `is_capture` indicates whether this type qualifies for capture RC management
    /// in closures (string, array, function, class - but not handles or iterators).
    Simple { is_capture: bool },

    /// Type is a composite (struct, tuple, fixed array) with RC fields.
    ///
    /// - `shallow_offsets`: Byte offsets of direct RC fields (one level deep)
    /// - `deep_offsets`: Byte offsets of all RC fields, including nested struct fields
    /// - `union_fields`: Inline union fields that need tag-based conditional RC cleanup.
    ///   Each entry is (byte_offset, rc_variant_tags) where rc_variant_tags has the same
    ///   format as `RcState::Union::rc_variants`.
    ///
    /// For non-struct composites (tuple, fixed array), shallow and deep are identical.
    /// For structs with nested struct fields, deep includes offsets within those nested structs.
    Composite {
        shallow_offsets: Vec<i32>,
        deep_offsets: Vec<i32>,
        union_fields: Vec<(i32, Vec<(u8, bool)>)>,
    },

    /// Type is a union with some RC variants.
    ///
    /// Each entry is (tag_index, is_interface) where:
    /// - `tag_index`: The variant's tag byte value (0-255)
    /// - `is_interface`: Whether the variant is an interface type (fat pointer)
    Union { rc_variants: Vec<(u8, bool)> },
}

impl RcState {
    /// Returns true if this type itself requires RC cleanup (rc_inc/rc_dec).
    ///
    /// This returns true ONLY for simple RC types:
    /// - `Simple`: Direct RC types (String, Array, Class, etc.)
    ///
    /// This returns false for:
    /// - `None`: Non-RC types
    /// - `Composite`: Structs/tuples with RC fields (stack-allocated; fields managed individually)
    /// - `Union`: Unions with RC variants (unions themselves are NOT rc_inc/dec'd;
    ///   cleanup of RC variants is handled by union-specific RC cleanup logic)
    #[inline]
    pub fn needs_cleanup(&self) -> bool {
        matches!(self, RcState::Simple { .. })
    }

    /// Returns true if this is a capture-eligible RC type.
    ///
    /// Capture-eligible types are simple RC types (String, Array, Function, Class)
    /// that can be captured by closures with special RC management.
    /// Handles and iterators are RC but not capture-eligible.
    #[inline]
    pub fn is_capture(&self) -> bool {
        matches!(self, RcState::Simple { is_capture: true })
    }

    /// Returns the shallow RC field offsets for composite types.
    ///
    /// Shallow offsets are direct RC fields at the top level of the struct/tuple.
    /// Returns `None` for non-composite types.
    #[inline]
    pub fn shallow_offsets(&self) -> Option<&[i32]> {
        match self {
            RcState::Composite {
                shallow_offsets, ..
            } => Some(shallow_offsets),
            RcState::None | RcState::Simple { .. } | RcState::Union { .. } => None,
        }
    }

    /// Returns the deep RC field offsets for composite types.
    ///
    /// Deep offsets include all RC fields, including those in nested structs.
    /// For non-struct composites (tuple, fixed array), this equals shallow offsets.
    /// Returns `None` for non-composite types.
    #[inline]
    pub fn deep_offsets(&self) -> Option<&[i32]> {
        match self {
            RcState::Composite { deep_offsets, .. } => Some(deep_offsets),
            RcState::None | RcState::Simple { .. } | RcState::Union { .. } => None,
        }
    }

    /// Returns inline union fields in composite types that need tag-based RC cleanup.
    ///
    /// Each entry is (byte_offset, rc_variant_tags) where the union is stored
    /// inline at `byte_offset` within the struct.
    /// Returns an empty slice for non-composite types or composites without union fields.
    #[inline]
    pub fn composite_union_fields(&self) -> &[(i32, Vec<(u8, bool)>)] {
        match self {
            RcState::Composite { union_fields, .. } => union_fields,
            _ => &[],
        }
    }

    /// Returns the RC variant information for union types.
    ///
    /// Each entry is (tag_index, is_interface) where:
    /// - `tag_index`: The variant's tag byte value
    /// - `is_interface`: Whether the variant is an interface (fat pointer)
    ///
    /// Returns `None` for non-union types.
    #[inline]
    pub fn union_variants(&self) -> Option<&[(u8, bool)]> {
        match self {
            RcState::Union { rc_variants } => Some(rc_variants),
            RcState::None | RcState::Simple { .. } | RcState::Composite { .. } => None,
        }
    }
}
