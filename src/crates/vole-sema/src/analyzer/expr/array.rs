use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use crate::types::PlaceholderKind;

impl Analyzer {
    /// Check array literal expression.
    pub(super) fn check_array_literal_expr(
        &mut self,
        elements: &[Expr],
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        if elements.is_empty() {
            // Empty array needs type annotation or we use unknown placeholder
            let unknown_id = self
                .type_arena_mut()
                .placeholder(PlaceholderKind::Inference);
            Ok(self.ty_array_id(unknown_id))
        } else {
            // Infer types for all elements (TypeId-based)
            let elem_type_ids: Vec<ArenaTypeId> = elements
                .iter()
                .map(|e| self.check_expr(e, interner))
                .collect::<Result<Vec<_>, _>>()?;

            // Check if all elements have compatible types (homogeneous -> Array)
            // or different types (heterogeneous -> Tuple)
            let first_ty_id = elem_type_ids[0];
            let is_homogeneous = elem_type_ids
                .iter()
                .skip(1)
                .all(|&ty_id| self.types_compatible_id(ty_id, first_ty_id, interner));

            if is_homogeneous {
                // All same type -> dynamic array
                Ok(self.ty_array_id(first_ty_id))
            } else {
                // Different types -> tuple
                Ok(self.ty_tuple_id(elem_type_ids))
            }
        }
    }

    /// Check repeat literal expression ([expr; count]).
    pub(super) fn check_repeat_literal_expr(
        &mut self,
        element: &Expr,
        count: usize,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let elem_ty_id = self.check_expr(element, interner)?;
        Ok(self.ty_fixed_array_id(elem_ty_id, count))
    }

    /// Check range expression (start..end).
    pub(super) fn check_range_expr(
        &mut self,
        range: &RangeExpr,
        expr_span: Span,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let start_ty_id = self.check_expr(&range.start, interner)?;
        let end_ty_id = self.check_expr(&range.end, interner)?;

        if !self.is_integer_id(start_ty_id) || !self.is_integer_id(end_ty_id) {
            self.type_error_pair_id("integer", start_ty_id, end_ty_id, expr_span);
        }
        Ok(ArenaTypeId::RANGE)
    }
}
