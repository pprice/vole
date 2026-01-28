use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check block expression.
    pub(super) fn check_block_expr(
        &mut self,
        block: &BlockExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Type check all statements
        for stmt in &block.stmts {
            // TODO(v-bd6c): Aggregate ReturnInfo from statements
            let _ = self.check_stmt(stmt, interner)?;
        }

        // Block evaluates to its trailing expression, if present
        if let Some(trailing) = &block.trailing_expr {
            self.check_expr(trailing, interner)
        } else {
            Ok(ArenaTypeId::VOID)
        }
    }

    /// Check if expression.
    pub(super) fn check_if_expr(
        &mut self,
        if_expr: &IfExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Type check the condition (must be bool) using TypeId
        let cond_ty_id = self.check_expr(&if_expr.condition, interner)?;
        if !self.is_bool_id(cond_ty_id) {
            self.type_error_id("bool", cond_ty_id, if_expr.condition.span);
        }

        // Extract narrowing info for `x is T` conditions
        let narrowing_info = self.extract_is_narrowing_info(&if_expr.condition, interner);

        // Save current overrides
        let saved_overrides = self.type_overrides.clone();

        // Type check then branch with narrowing if applicable
        if let Some((sym, narrowed_type_id, _)) = &narrowing_info {
            self.type_overrides.insert(*sym, *narrowed_type_id);
        }
        let then_ty_id = self.check_expr(&if_expr.then_branch, interner)?;

        // Restore overrides for else branch
        self.type_overrides = saved_overrides.clone();

        // If expression requires else branch
        let Some(else_branch) = &if_expr.else_branch else {
            self.type_overrides = saved_overrides;
            self.add_error(
                SemanticError::IfExprMissingElse {
                    span: if_expr.span.into(),
                },
                if_expr.span,
            );
            return Ok(ArenaTypeId::INVALID);
        };

        // Apply else-branch narrowing: if x is T, else branch has x: (original - T)
        if let Some((sym, tested_type_id, Some(original_type_id))) = &narrowing_info
            && let Some(else_narrowed) =
                self.compute_else_narrowed_type(*tested_type_id, *original_type_id)
        {
            self.type_overrides.insert(*sym, else_narrowed);
        }

        let else_ty_id = self.check_expr(else_branch, interner)?;

        // Restore original overrides
        self.type_overrides = saved_overrides;

        // Compute the join (least upper bound) of both branch types
        // Special cases for top/bottom types:
        // - If either branch is `never` (bottom), result is the other branch's type
        // - If either branch is `unknown` (top), result is `unknown`
        if then_ty_id.is_never() {
            return Ok(else_ty_id);
        }
        if else_ty_id.is_never() {
            return Ok(then_ty_id);
        }
        if then_ty_id.is_unknown() || else_ty_id.is_unknown() {
            return Ok(ArenaTypeId::UNKNOWN);
        }

        // Both branches must have compatible types
        if !self.types_compatible_id(then_ty_id, else_ty_id, interner) {
            self.add_type_mismatch_id(then_ty_id, else_ty_id, else_branch.span);
            Ok(ArenaTypeId::INVALID)
        } else {
            Ok(then_ty_id)
        }
    }

    /// Check when expression.
    pub(super) fn check_when_expr(
        &mut self,
        when_expr: &WhenExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // When expressions must have at least one arm
        if when_expr.arms.is_empty() {
            self.add_error(
                SemanticError::WhenExprEmpty {
                    span: when_expr.span.into(),
                },
                when_expr.span,
            );
            return Ok(ArenaTypeId::INVALID);
        }

        // Check that there's a wildcard arm
        let has_wildcard = when_expr.arms.iter().any(|arm| arm.condition.is_none());
        if !has_wildcard {
            self.add_error(
                SemanticError::WhenExprNotExhaustive {
                    span: when_expr.span.into(),
                },
                when_expr.span,
            );
            return Ok(ArenaTypeId::INVALID);
        }

        // Check all conditions are bool and all bodies have the same type
        let mut result_type = ArenaTypeId::INVALID;

        // Save overrides once before processing arms
        let saved_overrides = self.type_overrides.clone();

        for (i, arm) in when_expr.arms.iter().enumerate() {
            // Check condition (if not wildcard) and extract narrowing info
            let narrowing_info = if let Some(ref cond) = arm.condition {
                let cond_ty = self.check_expr(cond, interner)?;
                if cond_ty != self.ty_bool_id() && cond_ty != ArenaTypeId::INVALID {
                    let found_str = self.type_display_id(cond_ty);
                    self.add_error(
                        SemanticError::WhenConditionNotBool {
                            found: found_str,
                            span: cond.span.into(),
                        },
                        cond.span,
                    );
                }
                // Extract narrowing info for `x is T` conditions
                self.extract_is_narrowing_info(cond, interner)
            } else {
                None
            };

            // Apply narrowing for this arm's body
            if let Some((sym, narrowed_type_id, _)) = &narrowing_info {
                self.type_overrides.insert(*sym, *narrowed_type_id);
            }

            // Check body with narrowed type
            let body_ty = self.check_expr(&arm.body, interner)?;

            // Restore overrides for next arm
            self.type_overrides = saved_overrides.clone();

            if i == 0 {
                result_type = body_ty;
            } else if body_ty != ArenaTypeId::INVALID && result_type != ArenaTypeId::INVALID {
                // Compute join of types, handling top/bottom types
                if result_type.is_never() {
                    // Previous result was never, take this arm's type
                    result_type = body_ty;
                } else if body_ty.is_never() {
                    // This arm is never, keep previous result
                    // (do nothing)
                } else if result_type.is_unknown() || body_ty.is_unknown() {
                    // Either is unknown, result is unknown
                    result_type = ArenaTypeId::UNKNOWN;
                } else if !self.types_compatible_id(result_type, body_ty, interner) {
                    self.add_type_mismatch_id(result_type, body_ty, arm.body.span);
                }
            }
        }

        Ok(result_type)
    }
}
