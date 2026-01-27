use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check yield expression.
    pub(super) fn check_yield_expr(
        &mut self,
        yield_expr: &YieldExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check if we're inside a function at all
        if self.current_function_return.is_none() {
            self.add_error(
                SemanticError::YieldOutsideGenerator {
                    span: yield_expr.span.into(),
                },
                yield_expr.span,
            );
            return Ok(ArenaTypeId::VOID);
        }

        // Check if we're inside a generator function (Iterator<T> return type)
        let Some(element_type) = self.current_generator_element_type else {
            // Not a generator - report error with actual return type
            let return_type = self
                .current_function_return
                .expect("yield only valid inside function");
            let found = self.type_display_id(return_type);
            self.add_error(
                SemanticError::YieldInNonGenerator {
                    found,
                    span: yield_expr.span.into(),
                },
                yield_expr.span,
            );
            return Ok(ArenaTypeId::VOID);
        };

        // Type check the yield expression against the Iterator element type (TypeId-based)
        let yield_type_id =
            self.check_expr_expecting_id(&yield_expr.value, Some(element_type), interner)?;

        // Check type compatibility
        if !self.types_compatible_id(yield_type_id, element_type, interner) {
            let expected = self.type_display_id(element_type);
            let found = self.type_display_id(yield_type_id);
            self.add_error(
                SemanticError::YieldTypeMismatch {
                    expected,
                    found,
                    span: yield_expr.value.span.into(),
                },
                yield_expr.value.span,
            );
        }

        // yield expression returns Void (its value is the yielded element, but
        // the expression itself doesn't produce a value in the control flow)
        Ok(ArenaTypeId::VOID)
    }
}
