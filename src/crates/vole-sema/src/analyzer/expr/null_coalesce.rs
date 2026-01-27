use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check null coalesce expression (value ?? default).
    pub(super) fn check_null_coalesce_expr(
        &mut self,
        nc: &NullCoalesceExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let value_type_id = self.check_expr(&nc.value, interner)?;

        // Value must be an optional (union containing Nil)
        if !self.is_optional_id(value_type_id) {
            let found = self.type_display_id(value_type_id);
            self.add_error(
                SemanticError::NullCoalesceNotOptional {
                    found,
                    span: nc.value.span.into(),
                },
                nc.value.span,
            );
            return Ok(ArenaTypeId::INVALID);
        }

        // Get the non-nil type
        let unwrapped_id = self
            .unwrap_optional_id(value_type_id)
            .unwrap_or(ArenaTypeId::INVALID);

        // Default must match the unwrapped type (using TypeId version)
        let _default_type_id =
            self.check_expr_expecting_id(&nc.default, Some(unwrapped_id), interner)?;

        // Result is the non-nil type
        Ok(unwrapped_id)
    }
}
