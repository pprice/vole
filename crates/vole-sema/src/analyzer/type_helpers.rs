// src/sema/analyzer/type_helpers.rs
//
// Type construction and manipulation helpers.

#![allow(unused)] // Some methods used conditionally

use super::*;
use crate::type_arena::TypeId as ArenaTypeId;

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

    /// Get inner type if this is an optional type (T | nil)
    #[inline]
    pub(crate) fn unwrap_optional_id(&self, id: ArenaTypeId) -> Option<ArenaTypeId> {
        self.type_arena().unwrap_optional(id)
    }

    /// Check if TypeId is an optional type (T | nil)
    #[inline]
    pub(crate) fn is_optional_id(&self, id: ArenaTypeId) -> bool {
        self.type_arena().unwrap_optional(id).is_some()
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
}
