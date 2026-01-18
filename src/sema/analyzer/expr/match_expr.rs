use super::super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::LegacyType;

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
        // Convert to LegacyType for exhaustiveness/pattern checking (still needed for some paths)
        let scrutinee_type = self.type_arena.borrow().to_type(scrutinee_type_id);

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

        // Check each arm, collect result types
        let mut result_type: Option<LegacyType> = None;
        let mut first_arm_span: Option<Span> = None;

        // Track covered types for wildcard narrowing
        let mut covered_types: Vec<LegacyType> = Vec::new();

        for arm in &match_expr.arms {
            // Enter new scope for arm (bindings live here)
            self.scope = Scope::with_parent(std::mem::take(&mut self.scope));

            // Save current type overrides
            let saved_overrides = self.type_overrides.clone();

            // Check pattern and get narrowing info
            let narrowed_type = self.check_pattern(&arm.pattern, &scrutinee_type, interner);

            // For wildcard patterns on union types, compute remaining type
            let effective_narrowed = if matches!(arm.pattern, Pattern::Wildcard(_))
                || matches!(arm.pattern, Pattern::Identifier { .. }
                    if !self.is_type_pattern(&arm.pattern, interner))
            {
                // Wildcard or binding pattern - narrow to remaining types
                if let LegacyType::Union(variants) = &scrutinee_type {
                    let remaining: Vec<_> = variants
                        .iter()
                        .filter(|v| !covered_types.contains(v))
                        .cloned()
                        .collect();
                    if remaining.len() == 1 {
                        Some(remaining[0].clone())
                    } else if remaining.len() > 1 {
                        Some(LegacyType::Union(remaining.into()))
                    } else {
                        narrowed_type
                    }
                } else {
                    narrowed_type
                }
            } else {
                // Track this type as covered for future wildcard narrowing
                if let Some(ref ty) = narrowed_type {
                    covered_types.push(ty.clone());
                }
                narrowed_type
            };

            // Apply type narrowing if scrutinee is an identifier and pattern provides narrowing
            if let (Some(sym), Some(narrow_ty)) = (scrutinee_sym, &effective_narrowed) {
                let narrow_ty_id = self.type_arena.borrow_mut().from_type(narrow_ty);
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
            let body_type = self.check_expr_expecting(&arm.body, result_type.as_ref(), interner)?;

            // Restore type overrides
            self.type_overrides = saved_overrides;

            // Unify with previous arms
            match &result_type {
                None => {
                    result_type = Some(body_type);
                    first_arm_span = Some(arm.span);
                }
                Some(expected) if *expected != body_type => {
                    let expected_str = self.type_display(expected);
                    let found = self.type_display(&body_type);
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

        Ok(self.type_to_id(&result_type.unwrap_or(LegacyType::Void)))
    }
}
