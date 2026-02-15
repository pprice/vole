use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::PatternKind;

impl Analyzer {
    /// Check if a pattern is a type pattern (matches a class/primitive type name)
    fn is_type_pattern(&self, pattern: &Pattern, interner: &Interner) -> bool {
        match &pattern.kind {
            PatternKind::Identifier { name } => {
                // Check if this identifier resolves to a type name
                self.resolver(interner)
                    .resolve_type(*name, &self.entity_registry())
                    .is_some()
            }
            PatternKind::Wildcard
            | PatternKind::Literal(_)
            | PatternKind::Type { .. }
            | PatternKind::Val { .. }
            | PatternKind::Success { .. }
            | PatternKind::Error { .. }
            | PatternKind::Tuple { .. }
            | PatternKind::Record { .. } => false,
        }
    }

    pub(super) fn check_match_expr(
        &mut self,
        match_expr: &MatchExpr,
        expected: Option<ArenaTypeId>,
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
            .type_arena()
            .unwrap_fallible(scrutinee_type_id)
            .is_some();
        if is_fallible {
            let has_error_arm = match_expr
                .arms
                .iter()
                .any(|arm| matches!(arm.pattern.kind, PatternKind::Error { .. }));
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

        // Track covered types for wildcard narrowing (using TypeId)
        let mut covered_type_ids: Vec<ArenaTypeId> = Vec::new();

        // Get union variants if scrutinee is a union type (for wildcard narrowing)
        let union_variants: Option<Vec<ArenaTypeId>> = {
            let arena = self.type_arena();
            arena.unwrap_union(scrutinee_type_id).map(|v| v.to_vec())
        };

        for arm in &match_expr.arms {
            // Enter new scope for arm (bindings live here)
            self.push_scope();

            // Save current type overrides
            let saved_overrides = self.env.type_overrides.clone();

            // Check pattern and get narrowing info (using TypeId version)
            let narrowed_type_id = self.check_pattern_id(&arm.pattern, scrutinee_type_id, interner);

            // For wildcard patterns on union types, compute remaining type
            let effective_narrowed_id = if matches!(arm.pattern.kind, PatternKind::Wildcard)
                || matches!(arm.pattern.kind, PatternKind::Identifier { .. }
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
                        Some(self.type_arena_mut().union(remaining))
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
                self.env.type_overrides.insert(sym, narrow_ty_id);
            }

            // Check guard if present (must be bool) using TypeId
            if let Some(guard) = &arm.guard {
                let guard_type_id = self.check_expr(guard, interner)?;
                if !self.is_bool_compatible_id(guard_type_id) {
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

            // Check body with expected type hint for bidirectional inference (literal
            // coercion, empty-array element inference, etc.). Prefer caller-provided
            // expected (let binding / return), fall back to previous arms' type.
            let hint = expected.or(result_type_id).filter(|id| !id.is_never());
            let errors_before = self.diagnostics.errors.len();
            let mut body_type_id =
                self.check_expr_expecting_id_in_arm(&arm.body, hint, interner)?;

            // When the hint (from a previous arm, not the caller) caused type-mismatch
            // errors, this arm genuinely produces a different type. Discard the errors
            // and re-infer without the hint so the natural type flows into the union.
            let hint_caused_errors = self.diagnostics.errors.len() > errors_before;
            if hint_caused_errors && expected.is_none() {
                self.diagnostics.errors.truncate(errors_before);
                body_type_id = self.check_expr_in_arm(&arm.body, interner)?;
            }

            // Restore type overrides
            self.env.type_overrides = saved_overrides;

            // Unify with previous arms, handling top/bottom types
            match result_type_id {
                None => {
                    result_type_id = Some(body_type_id);
                }
                Some(expected_id) if expected_id != body_type_id => {
                    // Handle never type (bottom): never unifies with any type
                    if expected_id.is_never() {
                        result_type_id = Some(body_type_id);
                    } else if body_type_id.is_never() {
                        // This arm is never, keep previous result (do nothing)
                    } else if expected_id.is_unknown() || body_type_id.is_unknown() {
                        // Either is unknown, result is unknown
                        result_type_id = Some(ArenaTypeId::UNKNOWN);
                    } else {
                        // Arms have different types — construct a union
                        result_type_id =
                            Some(self.type_arena_mut().union(vec![expected_id, body_type_id]));
                    }
                }
                _ => {}
            }

            // Exit arm scope
            self.pop_scope();
        }

        Ok(result_type_id.unwrap_or(ArenaTypeId::VOID))
    }
}
