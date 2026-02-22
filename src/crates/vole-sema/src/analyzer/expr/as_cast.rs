use super::super::*;
use crate::analysis_cache::IsCheckResult;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::ast::{AsCastExpr, AsCastKind};

impl Analyzer {
    /// Check `as?` / `as!` cast expression.
    ///
    /// Reuses the same `IsCheckResult` logic as `is` expressions for codegen,
    /// but the result type differs:
    /// - `as? T` returns `T | nil` (nullable T)
    /// - `as! T` returns `T`
    pub(super) fn check_as_cast_expr(
        &mut self,
        expr: &Expr,
        as_cast: &AsCastExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let tested_type_id = self.resolve_type_id(&as_cast.type_expr, interner);

        // For literals, use bidirectional type inference so `42 as? i32` works
        let value_type_id = if as_cast.value.is_literal() {
            let inferred_id = self.infer_literal_type_id(&as_cast.value, tested_type_id, interner);
            self.record_expr_type_id(&as_cast.value, inferred_id);
            inferred_id
        } else {
            self.check_expr(&as_cast.value, interner)?
        };

        // Compute IsCheckResult for codegen (same logic as is_expr)
        let union_variants = self.type_arena().unwrap_union(value_type_id).cloned();
        let is_check_result = if value_type_id.is_unknown() {
            IsCheckResult::CheckUnknown(tested_type_id)
        } else if let Some(variants) = &union_variants {
            if let Some(index) = variants.iter().position(|&v| v == tested_type_id) {
                IsCheckResult::CheckTag(index as u32)
            } else {
                IsCheckResult::AlwaysFalse
            }
        } else if value_type_id == tested_type_id {
            IsCheckResult::AlwaysTrue
        } else {
            IsCheckResult::AlwaysFalse
        };
        self.record_is_check_result(expr.id, is_check_result);

        // Report error if tested type is not a variant of the union
        if let Some(variants) = union_variants
            && !variants.contains(&tested_type_id)
        {
            let tested = self.type_display_id(tested_type_id);
            let union_type = self.type_display_id(value_type_id);
            self.add_error(
                SemanticError::IsNotVariant {
                    tested,
                    union_type,
                    span: as_cast.type_span.into(),
                },
                as_cast.type_span,
            );
        }

        // Result type depends on cast kind
        match as_cast.kind {
            AsCastKind::Safe => {
                // as? T returns T | nil
                Ok(self.type_arena_mut().optional(tested_type_id))
            }
            AsCastKind::Unsafe => {
                // as! T returns T
                Ok(tested_type_id)
            }
        }
    }
}
