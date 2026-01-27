use super::super::*;
use crate::analysis_cache::IsCheckResult;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check `is` expression (value is Type).
    /// Computes IsCheckResult for codegen.
    pub(super) fn check_is_expr(
        &mut self,
        expr: &Expr,
        is_expr: &IsExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let tested_type_id = self.resolve_type_id(&is_expr.type_expr, interner);

        // For literals, use bidirectional type inference so `42 is i32` works
        // For non-literals, just check normally (no type coercion)
        let value_type_id = if is_expr.value.is_literal() {
            // Try to infer literal's type from tested type (won't error on mismatch)
            let inferred_id = self.infer_literal_type_id(&is_expr.value, tested_type_id, interner);
            // Record the inferred type so codegen uses it
            self.record_expr_type_id(&is_expr.value, inferred_id);
            inferred_id
        } else {
            self.check_expr(&is_expr.value, interner)?
        };

        // Compute IsCheckResult for codegen
        let union_variants = self.type_arena().unwrap_union(value_type_id).cloned();
        let is_check_result = if let Some(variants) = &union_variants {
            // Union type: find which variant the tested type matches
            if let Some(index) = variants.iter().position(|&v| v == tested_type_id) {
                IsCheckResult::CheckTag(index as u32)
            } else {
                // Error: tested type is not a variant (will be reported below)
                IsCheckResult::AlwaysFalse
            }
        } else {
            // Non-union type: check direct type equality
            if value_type_id == tested_type_id {
                IsCheckResult::AlwaysTrue
            } else {
                IsCheckResult::AlwaysFalse
            }
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
                    span: is_expr.type_span.into(),
                },
                is_expr.type_span,
            );
        }

        // Result is always bool
        Ok(ArenaTypeId::BOOL)
    }
}
