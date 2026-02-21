// src/sema/analyzer/type_helpers.rs
//
// Type construction and manipulation helpers.

#![allow(unused)] // Some methods used conditionally

use super::*;
use crate::expression_data::StringConversion;
use crate::type_arena::TypeId as ArenaTypeId;

// ========== Sequence type info ==========
//
// Enum for unified array/fixed-array/tuple unwrapping.

/// Information about a sequence type (array, fixed-array, or tuple).
/// Used by `unwrap_sequence_id` to return unified information.
#[derive(Debug, Clone)]
pub(crate) enum SequenceInfo {
    /// Dynamic array with element type
    Array(ArenaTypeId),
    /// Fixed-size array with element type and size
    FixedArray(ArenaTypeId, usize),
    /// Tuple with element types
    Tuple(Vec<ArenaTypeId>),
}

impl SequenceInfo {
    /// Get the element type for indexing.
    /// For arrays/fixed-arrays, returns the element type.
    /// For tuples, returns the first element type (common case for 2-tuples with same types).
    #[inline]
    pub(crate) fn element_type(&self) -> ArenaTypeId {
        match self {
            SequenceInfo::Array(elem) | SequenceInfo::FixedArray(elem, _) => *elem,
            SequenceInfo::Tuple(elems) => elems.first().copied().unwrap_or(ArenaTypeId::INVALID),
        }
    }
}

impl Analyzer {
    /// Create a primitive TypeId (uses reserved constants - no arena access)
    #[inline]
    pub(crate) fn ty_prim_id(&self, p: PrimitiveType) -> ArenaTypeId {
        match p {
            PrimitiveType::I8 => ArenaTypeId::I8,
            PrimitiveType::I16 => ArenaTypeId::I16,
            PrimitiveType::I32 => ArenaTypeId::I32,
            PrimitiveType::I64 => ArenaTypeId::I64,
            PrimitiveType::I128 => ArenaTypeId::I128,
            PrimitiveType::U8 => ArenaTypeId::U8,
            PrimitiveType::U16 => ArenaTypeId::U16,
            PrimitiveType::U32 => ArenaTypeId::U32,
            PrimitiveType::U64 => ArenaTypeId::U64,
            PrimitiveType::F32 => ArenaTypeId::F32,
            PrimitiveType::F64 => ArenaTypeId::F64,
            PrimitiveType::F128 => ArenaTypeId::F128,
            PrimitiveType::Bool => ArenaTypeId::BOOL,
            PrimitiveType::String => ArenaTypeId::STRING,
        }
    }

    /// Create i64 TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_i64_id(&self) -> ArenaTypeId {
        ArenaTypeId::I64
    }

    /// Create i32 TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_i32_id(&self) -> ArenaTypeId {
        ArenaTypeId::I32
    }

    /// Create f64 TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_f64_id(&self) -> ArenaTypeId {
        ArenaTypeId::F64
    }

    /// Create bool TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_bool_id(&self) -> ArenaTypeId {
        ArenaTypeId::BOOL
    }

    /// Create string TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_string_id(&self) -> ArenaTypeId {
        ArenaTypeId::STRING
    }

    /// Create void TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_void_id(&self) -> ArenaTypeId {
        ArenaTypeId::VOID
    }

    /// Create nil TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_nil_id(&self) -> ArenaTypeId {
        ArenaTypeId::NIL
    }

    /// Create done TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_done_id(&self) -> ArenaTypeId {
        ArenaTypeId::DONE
    }

    /// Create range TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_range_id(&self) -> ArenaTypeId {
        ArenaTypeId::RANGE
    }

    /// Create metatype TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_type_id(&self) -> ArenaTypeId {
        ArenaTypeId::METATYPE
    }

    /// Create an array TypeId
    #[inline]
    pub(crate) fn ty_array_id(&self, element_id: ArenaTypeId) -> ArenaTypeId {
        self.type_arena_mut().array(element_id)
    }

    /// Create a fixed-size array TypeId
    #[inline]
    pub(crate) fn ty_fixed_array_id(&self, element_id: ArenaTypeId, size: usize) -> ArenaTypeId {
        self.type_arena_mut().fixed_array(element_id, size)
    }

    /// Create a tuple TypeId
    #[inline]
    pub(crate) fn ty_tuple_id(&self, element_ids: Vec<ArenaTypeId>) -> ArenaTypeId {
        self.type_arena_mut().tuple(element_ids)
    }

    /// Create an optional TypeId (T | nil)
    #[inline]
    pub(crate) fn ty_optional_id(&self, inner_id: ArenaTypeId) -> ArenaTypeId {
        self.type_arena_mut().optional(inner_id)
    }

    /// Create an invalid/error TypeId (no arena access)
    #[inline]
    pub(crate) fn ty_invalid_id(&self) -> ArenaTypeId {
        ArenaTypeId::INVALID
    }

    /// Create an invalid/error TypeId with tracing
    #[inline]
    pub(crate) fn ty_invalid_traced_id(&self, reason: &str) -> ArenaTypeId {
        tracing::warn!(reason, "creating invalid type");
        ArenaTypeId::INVALID
    }

    // ========== TypeId comparison helpers ==========
    //
    // These check if a TypeId matches a well-known type.
    // With reserved TypeIds, these are simple constant comparisons - no arena access needed.

    /// Check if TypeId is void (no arena access)
    #[inline]
    pub(crate) fn is_void_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::VOID
    }

    /// Check if TypeId is nil (no arena access)
    #[inline]
    pub(crate) fn is_nil_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::NIL
    }

    /// Check if TypeId is bool (no arena access)
    #[inline]
    pub(crate) fn is_bool_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::BOOL
    }

    /// Check if TypeId can be used in boolean context (bool or numeric)
    #[inline]
    pub(crate) fn is_bool_compatible_id(&self, id: ArenaTypeId) -> bool {
        self.is_bool_id(id) || self.is_numeric_id(id)
    }

    /// Check if TypeId is metatype (no arena access)
    #[inline]
    pub(crate) fn is_metatype_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::METATYPE
    }

    /// Check if TypeId is invalid (no arena access)
    #[inline]
    pub(crate) fn is_invalid_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::INVALID
    }

    /// Check if TypeId is a numeric type (no arena access)
    #[inline]
    pub(crate) fn is_numeric_id(&self, id: ArenaTypeId) -> bool {
        id.is_numeric()
    }

    /// Check if TypeId is string type (no arena access)
    #[inline]
    pub(crate) fn is_string_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::STRING
    }

    /// Check if TypeId is f64 type (no arena access)
    #[inline]
    pub(crate) fn is_f64_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::F64
    }

    /// Check if TypeId is i64 type (no arena access)
    #[inline]
    pub(crate) fn is_i64_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::I64
    }

    /// Check if TypeId is an integer type (any size, no arena access)
    #[inline]
    pub(crate) fn is_integer_id(&self, id: ArenaTypeId) -> bool {
        id.is_integer()
    }

    /// Check if TypeId is a range type (no arena access)
    #[inline]
    pub(crate) fn is_range_id(&self, id: ArenaTypeId) -> bool {
        id == ArenaTypeId::RANGE
    }

    /// Check if TypeId is an array type
    #[inline]
    pub(crate) fn is_array_id(&self, id: ArenaTypeId) -> bool {
        use crate::type_arena::SemaType;
        matches!(self.type_arena().get(id), SemaType::Array(_))
    }

    // ========== TypeId unwrapping helpers ==========
    //
    // These extract inner types from compound TypeIds.

    /// Get array element type if this is an array
    #[inline]
    pub(crate) fn unwrap_array_id(&self, id: ArenaTypeId) -> Option<ArenaTypeId> {
        self.type_arena().unwrap_array(id)
    }

    /// Get fixed array element type and size if this is a fixed array
    #[inline]
    pub(crate) fn unwrap_fixed_array_id(&self, id: ArenaTypeId) -> Option<(ArenaTypeId, usize)> {
        self.type_arena().unwrap_fixed_array(id)
    }

    /// Get tuple element types if this is a tuple
    #[inline]
    pub(crate) fn unwrap_tuple_id(&self, id: ArenaTypeId) -> Option<Vec<ArenaTypeId>> {
        self.type_arena().unwrap_tuple(id).map(|v| v.to_vec())
    }

    /// Get runtime iterator element type if this is a runtime iterator
    #[inline]
    pub(crate) fn unwrap_runtime_iterator_id(&self, id: ArenaTypeId) -> Option<ArenaTypeId> {
        self.type_arena().unwrap_runtime_iterator(id)
    }

    /// Get inner type if this is an optional type (T | nil) with exactly one non-nil variant.
    /// For multi-variant optionals (A | B | nil), use `unwrap_optional_non_nil_id` instead.
    #[inline]
    pub(crate) fn unwrap_optional_id(&self, id: ArenaTypeId) -> Option<ArenaTypeId> {
        self.type_arena().unwrap_optional(id)
    }

    /// Get the non-nil type from an optional union (union containing nil).
    /// For a single-variant optional `T | nil`, returns `T`.
    /// For a multi-variant optional `A | B | nil`, returns `A | B` (a new union).
    /// Returns `None` if the type is not an optional (union containing nil).
    pub(crate) fn unwrap_optional_non_nil_id(&self, id: ArenaTypeId) -> Option<ArenaTypeId> {
        let non_nil_variants = self.type_arena().unwrap_optional_non_nil_variants(id)?;
        if non_nil_variants.len() == 1 {
            Some(non_nil_variants[0])
        } else {
            Some(self.type_arena_mut().union(non_nil_variants))
        }
    }

    /// Check if TypeId is an optional type (any union containing nil)
    #[inline]
    pub(crate) fn is_optional_id(&self, id: ArenaTypeId) -> bool {
        self.type_arena().is_optional(id)
    }

    /// Get fallible (success, error) types if this is a fallible type
    #[inline]
    pub(crate) fn unwrap_fallible_id(&self, id: ArenaTypeId) -> Option<(ArenaTypeId, ArenaTypeId)> {
        self.type_arena().unwrap_fallible(id)
    }

    /// Check if TypeId is a fallible type
    #[inline]
    pub(crate) fn is_fallible_id(&self, id: ArenaTypeId) -> bool {
        self.type_arena().unwrap_fallible(id).is_some()
    }

    /// Check if TypeId is a runtime iterator type
    #[inline]
    pub(crate) fn is_runtime_iterator_id(&self, id: ArenaTypeId) -> bool {
        self.type_arena().unwrap_runtime_iterator(id).is_some()
    }

    // ========== Sequence type helpers ==========
    //
    // Unified helpers for array/fixed-array/tuple unwrapping.

    /// Unwrap a sequence type (array, fixed-array, or tuple) into unified info.
    /// Returns None if the type is not a sequence type.
    pub(crate) fn unwrap_sequence_id(&self, id: ArenaTypeId) -> Option<SequenceInfo> {
        if let Some(elem_id) = self.unwrap_array_id(id) {
            Some(SequenceInfo::Array(elem_id))
        } else if let Some((elem_id, size)) = self.unwrap_fixed_array_id(id) {
            Some(SequenceInfo::FixedArray(elem_id, size))
        } else {
            self.unwrap_tuple_id(id).map(SequenceInfo::Tuple)
        }
    }

    /// Get the element type of an indexable type (array or fixed-array only).
    /// Returns None if the type is not indexable for assignment (tuples excluded).
    /// This is a simpler helper for assignment contexts where tuples are not valid targets.
    #[inline]
    pub(crate) fn unwrap_indexable_element_id(&self, id: ArenaTypeId) -> Option<ArenaTypeId> {
        if let Some(elem_id) = self.unwrap_array_id(id) {
            Some(elem_id)
        } else if let Some((elem_id, _)) = self.unwrap_fixed_array_id(id) {
            Some(elem_id)
        } else {
            None
        }
    }

    // =========================================================================
    // Type narrowing helpers (for `is` operator flow analysis)
    // =========================================================================

    /// Extract narrowing info from an `x is T` condition.
    /// Returns Some((symbol, tested_type, original_type)) if the condition is `x is T`
    /// where x is a simple identifier.
    pub(crate) fn extract_is_narrowing_info(
        &mut self,
        condition: &Expr,
        interner: &Interner,
    ) -> Option<(Symbol, ArenaTypeId, Option<ArenaTypeId>)> {
        if let ExprKind::Is(is_expr) = &condition.kind
            && let ExprKind::Identifier(sym) = &is_expr.value.kind
        {
            let tested_type_id = self.resolve_type_id(&is_expr.type_expr, interner);
            let original_type_id = self.get_variable_type_id(*sym);
            return Some((*sym, tested_type_id, original_type_id));
        }
        None
    }

    /// Compute the narrowed type for an else-branch when condition was `x is T`.
    /// Returns the type with T removed from the union, or None if not a union.
    pub(crate) fn compute_else_narrowed_type(
        &mut self,
        tested_type_id: ArenaTypeId,
        original_type_id: ArenaTypeId,
    ) -> Option<ArenaTypeId> {
        let union_variants: Option<Vec<ArenaTypeId>> = {
            let arena = self.type_arena();
            arena.unwrap_union(original_type_id).map(|v| v.to_vec())
        };

        if let Some(variants) = union_variants {
            // Remove tested type from union
            let remaining: Vec<_> = variants
                .iter()
                .filter(|&&v| v != tested_type_id)
                .copied()
                .collect();

            if remaining.len() == 1 {
                // Single type remaining - narrow to that
                Some(remaining[0])
            } else if remaining.len() > 1 {
                // Multiple types remaining - narrow to smaller union
                Some(self.type_arena_mut().union(remaining))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Convert a NumericSuffix to the corresponding ArenaTypeId.
    pub(crate) fn suffix_to_type_id(&self, suffix: NumericSuffix) -> ArenaTypeId {
        match suffix {
            NumericSuffix::U8 => ArenaTypeId::U8,
            NumericSuffix::U16 => ArenaTypeId::U16,
            NumericSuffix::U32 => ArenaTypeId::U32,
            NumericSuffix::U64 => ArenaTypeId::U64,
            NumericSuffix::I8 => ArenaTypeId::I8,
            NumericSuffix::I16 => ArenaTypeId::I16,
            NumericSuffix::I32 => ArenaTypeId::I32,
            NumericSuffix::I64 => ArenaTypeId::I64,
            NumericSuffix::I128 => ArenaTypeId::I128,
            NumericSuffix::F32 => ArenaTypeId::F32,
            NumericSuffix::F64 => ArenaTypeId::F64,
            NumericSuffix::F128 => ArenaTypeId::F128,
        }
    }

    /// Get a human-readable range string for a numeric suffix type.
    pub(crate) fn type_range_str(suffix: NumericSuffix) -> String {
        match suffix {
            NumericSuffix::U8 => "0..255".to_string(),
            NumericSuffix::U16 => "0..65535".to_string(),
            NumericSuffix::U32 => "0..4294967295".to_string(),
            NumericSuffix::U64 => "0..18446744073709551615".to_string(),
            NumericSuffix::I8 => "-128..127".to_string(),
            NumericSuffix::I16 => "-32768..32767".to_string(),
            NumericSuffix::I32 => "-2147483648..2147483647".to_string(),
            NumericSuffix::I64 => "-9223372036854775808..9223372036854775807".to_string(),
            NumericSuffix::I128 => "i128 range".to_string(),
            NumericSuffix::F32 => "f32 range".to_string(),
            NumericSuffix::F64 => "f64 range".to_string(),
            NumericSuffix::F128 => "f128 range".to_string(),
        }
    }

    // =========================================================================
    // String interpolation conversion classification
    // =========================================================================

    /// Classify the string conversion needed for a value of the given type.
    ///
    /// Determines the correct runtime conversion based on the type. The result
    /// is stored in the NodeMap so codegen can apply the conversion via
    /// `apply_string_conversion` without re-detecting types.
    pub(crate) fn classify_string_conversion(&self, type_id: ArenaTypeId) -> StringConversion {
        // Already a string
        if type_id == ArenaTypeId::STRING {
            return StringConversion::Identity;
        }

        // Array
        if self.is_array_id(type_id) {
            return StringConversion::ArrayToString;
        }

        // Nil
        if type_id.is_nil() {
            return StringConversion::NilToString;
        }

        // Union types (optional or general)
        let arena = self.type_arena();
        if let Some(variants) = arena.unwrap_union(type_id) {
            let variants_vec: Vec<ArenaTypeId> = variants.to_vec();
            let nil_idx = variants_vec.iter().position(|v| v.is_nil());
            drop(arena); // release borrow before recursive calls

            if let Some(nil_idx) = nil_idx {
                return self.classify_optional_conversion(&variants_vec, nil_idx);
            }
            return self.classify_union_conversion(&variants_vec);
        }
        drop(arena);

        // Primitive types
        self.classify_primitive_conversion(type_id)
    }

    /// Classify conversion for an optional (union with nil variant).
    fn classify_optional_conversion(
        &self,
        variants: &[ArenaTypeId],
        nil_idx: usize,
    ) -> StringConversion {
        // Find the non-nil variant's type and classify its conversion
        let inner_type = variants
            .iter()
            .find(|v| !v.is_nil())
            .copied()
            .expect("INTERNAL: optional union must have non-nil variant");

        let inner_conversion = self.classify_string_conversion(inner_type);

        StringConversion::OptionalToString {
            nil_index: nil_idx,
            variants: variants.to_vec(),
            inner_conversion: Box::new(inner_conversion),
        }
    }

    /// Classify conversion for a general (non-optional) union.
    fn classify_union_conversion(&self, variants: &[ArenaTypeId]) -> StringConversion {
        let variant_conversions: Vec<(ArenaTypeId, StringConversion)> = variants
            .iter()
            .map(|&v| (v, self.classify_string_conversion(v)))
            .collect();

        StringConversion::UnionToString {
            variants: variant_conversions,
        }
    }

    /// Classify conversion for a primitive (non-composite) type.
    fn classify_primitive_conversion(&self, type_id: ArenaTypeId) -> StringConversion {
        match type_id {
            ArenaTypeId::F64 => StringConversion::F64ToString,
            ArenaTypeId::F32 => StringConversion::F32ToString,
            ArenaTypeId::F128 => StringConversion::F128ToString,
            ArenaTypeId::I128 => StringConversion::I128ToString,
            ArenaTypeId::BOOL => StringConversion::BoolToString,
            _ if type_id.is_integer() => StringConversion::I64ToString,
            // Fallback: treat as i64 (matches codegen's default)
            _ => StringConversion::I64ToString,
        }
    }

    /// Fast lookup of well-known interface TypeDefIds by name.
    /// Returns the cached TypeDefId for Stringable/Iterator/Iterable etc. without
    /// going through the full resolve_type_str_or_interface path.
    ///
    /// These are lazily cached on first use by resolving through the normal
    /// resolver path once and then storing the result in AnalyzerContext.
    pub(crate) fn lookup_well_known_interface(&self, name: &str) -> Option<TypeDefId> {
        let cache = self.ctx.well_known_cache.borrow();
        match name {
            "Stringable" => cache.stringable,
            "Iterator" => cache.iterator,
            "Iterable" => cache.iterable,
            "Equatable" => cache.equatable,
            "Comparable" => cache.comparable,
            "Hashable" => cache.hashable,
            "Transferable" => cache.transferable,
            _ => None,
        }
    }

    /// Resolve an interface by name, using the well-known cache for known names.
    /// Falls back to full resolution for unknown names.
    pub(crate) fn resolve_well_known_or_full(
        &self,
        name: &str,
        interner: &Interner,
    ) -> Option<TypeDefId> {
        self.lookup_well_known_interface(name).or_else(|| {
            self.resolver(interner)
                .resolve_type_str_or_interface(name, &self.entity_registry())
        })
    }

    /// Populate the well-known interface cache by resolving each name once
    /// through the normal resolver path. Called after prelude loading and
    /// signature collection to ensure the EntityRegistry is fully populated.
    pub(crate) fn populate_well_known_cache(&self, interner: &Interner) {
        use super::context::WellKnownCache;
        let resolve = |name: &str| {
            self.resolver(interner)
                .resolve_type_str_or_interface(name, &self.entity_registry())
        };
        let cache = WellKnownCache {
            stringable: resolve("Stringable"),
            iterator: resolve("Iterator"),
            iterable: resolve("Iterable"),
            equatable: resolve("Equatable"),
            comparable: resolve("Comparable"),
            hashable: resolve("Hashable"),
            transferable: resolve("Transferable"),
        };
        *self.ctx.well_known_cache.borrow_mut() = cache;
    }
}
