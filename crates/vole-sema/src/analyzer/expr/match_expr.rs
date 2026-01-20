use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check if a pattern is a type pattern (matches a class/record/primitive type name)
    fn is_type_pattern(&self, pattern: &Pattern, interner: &Interner) -> bool {
        match pattern {
            Pattern::Identifier { name, .. } => {
                // Check if this identifier resolves to a type name
                self.resolver(interner)
                    .resolve_type(*name, &self.entity_registry)
                    .is_some()
            }
            _ => false,
        }
    }

    pub(super) fn check_match_expr(
        &mut self,
        match_expr: &MatchExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check scrutinee type
        let scrutinee_type_id = self.check_expr(&match_expr.scrutinee, interner)?;

        // Get scrutinee symbol if it's an identifier (for type narrowing)
        let scrutinee_sym = if let ExprKind::Identifier(sym) = &match_expr.scrutinee.kind {
            Some(*sym)
        } else {
            None
        };

        // Check exhaustiveness - for union types with type patterns, check coverage (TypeId version)
        let is_exhaustive = self.check_match_exhaustiveness_id(
            &match_expr.arms,
            scrutinee_type_id,
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

        // For fallible types, require at least one error arm (using TypeId)
        let is_fallible = self
            .type_arena
            .borrow()
            .unwrap_fallible(scrutinee_type_id)
            .is_some();
        if is_fallible {
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

        // Check each arm, collect result types (using TypeId)
        let mut result_type_id: Option<ArenaTypeId> = None;
        let mut first_arm_span: Option<Span> = None;

        // Track covered types for wildcard narrowing (using TypeId)
        let mut covered_type_ids: Vec<ArenaTypeId> = Vec::new();

        // Get union variants if scrutinee is a union type (for wildcard narrowing)
        let union_variants: Option<Vec<ArenaTypeId>> = {
            let arena = self.type_arena.borrow();
            arena.unwrap_union(scrutinee_type_id).map(|v| v.to_vec())
        };

        for arm in &match_expr.arms {
            // Enter new scope for arm (bindings live here)
            self.scope = Scope::with_parent(std::mem::take(&mut self.scope));

            // Save current type overrides
            let saved_overrides = self.type_overrides.clone();

            // Check pattern and get narrowing info (using TypeId version)
            let narrowed_type_id = self.check_pattern_id(&arm.pattern, scrutinee_type_id, interner);

            // For wildcard patterns on union types, compute remaining type
            let effective_narrowed_id = if matches!(arm.pattern, Pattern::Wildcard(_))
                || matches!(arm.pattern, Pattern::Identifier { .. }
                    if !self.is_type_pattern(&arm.pattern, interner))
            {
                // Wildcard or binding pattern - narrow to remaining types
                if let Some(ref variants) = union_variants {
                    let remaining: Vec<_> = variants
                        .iter()
                        .filter(|v| !covered_type_ids.contains(v))
                        .copied()
                        .collect();
                    if remaining.len() == 1 {
                        Some(remaining[0])
                    } else if remaining.len() > 1 {
                        Some(self.type_arena.borrow_mut().union(remaining))
                    } else {
                        narrowed_type_id
                    }
                } else {
                    narrowed_type_id
                }
            } else {
                // Track this type as covered for future wildcard narrowing
                if let Some(ty_id) = narrowed_type_id {
                    covered_type_ids.push(ty_id);
                }
                narrowed_type_id
            };

            // Apply type narrowing if scrutinee is an identifier and pattern provides narrowing
            if let (Some(sym), Some(narrow_ty_id)) = (scrutinee_sym, effective_narrowed_id) {
                self.type_overrides.insert(sym, narrow_ty_id);
            }

            // Check guard if present (must be bool) using TypeId
            if let Some(guard) = &arm.guard {
                let guard_type_id = self.check_expr(guard, interner)?;
                if !self.is_bool_id(guard_type_id) && !self.is_numeric_id(guard_type_id) {
                    let found = self.type_display_id(guard_type_id);
                    self.add_error(
                        SemanticError::MatchGuardNotBool {
                            found,
                            span: guard.span.into(),
                        },
                        guard.span,
                    );
                }
            }

            // Check body expression with expected type from first arm (if known)
            let body_type_id = self.check_expr_expecting_id(&arm.body, result_type_id, interner)?;

            // Restore type overrides
            self.type_overrides = saved_overrides;

            // Unify with previous arms
            match result_type_id {
                None => {
                    result_type_id = Some(body_type_id);
                    first_arm_span = Some(arm.span);
                }
                Some(expected_id) if expected_id != body_type_id => {
                    let expected_str = self.type_display_id(expected_id);
                    let found = self.type_display_id(body_type_id);
                    self.add_error(
                        SemanticError::MatchArmTypeMismatch {
                            expected: expected_str,
                            found,
                            first_arm: first_arm_span
                                .expect("first_arm_span set when result_type became Some")
                                .into(),
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

        Ok(result_type_id.unwrap_or(ArenaTypeId::VOID))
    }
}
