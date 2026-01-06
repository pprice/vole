use super::super::*;

impl Analyzer {
    pub(super) fn check_match_expr(
        &mut self,
        match_expr: &MatchExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // Check scrutinee type
        let scrutinee_type = self.check_expr(&match_expr.scrutinee, interner)?;

        // Get scrutinee symbol if it's an identifier (for type narrowing)
        let scrutinee_sym = if let ExprKind::Identifier(sym) = &match_expr.scrutinee.kind {
            Some(*sym)
        } else {
            None
        };

        // Check exhaustiveness - for union types with type patterns, check coverage
        let is_exhaustive = self.check_match_exhaustiveness(
            &match_expr.arms,
            &scrutinee_type,
            match_expr.span,
            interner,
        );
        if !is_exhaustive {
            self.add_error(
                SemanticError::NonExhaustiveMatch {
                    span: match_expr.span.into(),
                },
                match_expr.span,
            );
        }

        // For fallible types, require at least one error arm
        if let Type::Fallible(_) = &scrutinee_type {
            let has_error_arm = match_expr
                .arms
                .iter()
                .any(|arm| matches!(arm.pattern, Pattern::Error { .. }));
            if !has_error_arm {
                self.add_error(
                    SemanticError::MissingErrorArm {
                        span: match_expr.span.into(),
                    },
                    match_expr.span,
                );
            }
        }

        // Check each arm, collect result types
        let mut result_type: Option<Type> = None;
        let mut first_arm_span: Option<Span> = None;

        for arm in &match_expr.arms {
            // Enter new scope for arm (bindings live here)
            self.scope = Scope::with_parent(std::mem::take(&mut self.scope));

            // Save current type overrides
            let saved_overrides = self.type_overrides.clone();

            // Check pattern and get narrowing info
            let narrowed_type = self.check_pattern(&arm.pattern, &scrutinee_type, interner);

            // Apply type narrowing if scrutinee is an identifier and pattern provides narrowing
            if let (Some(sym), Some(narrow_ty)) = (scrutinee_sym, &narrowed_type) {
                self.type_overrides.insert(sym, narrow_ty.clone());
            }

            // Check guard if present (must be bool)
            if let Some(guard) = &arm.guard {
                let guard_type = self.check_expr(guard, interner)?;
                if guard_type != Type::Bool && !guard_type.is_numeric() {
                    self.add_error(
                        SemanticError::MatchGuardNotBool {
                            found: guard_type.name().to_string(),
                            span: guard.span.into(),
                        },
                        guard.span,
                    );
                }
            }

            // Check body expression
            let body_type = self.check_expr(&arm.body, interner)?;

            // Restore type overrides
            self.type_overrides = saved_overrides;

            // Unify with previous arms
            match &result_type {
                None => {
                    result_type = Some(body_type);
                    first_arm_span = Some(arm.span);
                }
                Some(expected) if *expected != body_type => {
                    self.add_error(
                        SemanticError::MatchArmTypeMismatch {
                            expected: expected.name().to_string(),
                            found: body_type.name().to_string(),
                            first_arm: first_arm_span.unwrap().into(),
                            span: arm.body.span.into(),
                        },
                        arm.body.span,
                    );
                }
                _ => {}
            }

            // Exit arm scope
            if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                self.scope = parent;
            }
        }

        Ok(result_type.unwrap_or(Type::Void))
    }
}
