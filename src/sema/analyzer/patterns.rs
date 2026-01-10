// src/sema/analyzer/patterns.rs

use super::*;

impl Analyzer {
    /// Check a pattern against the scrutinee type.
    /// Returns the narrowed type if this pattern narrows the scrutinee (e.g., type patterns).
    pub(crate) fn check_pattern(
        &mut self,
        pattern: &Pattern,
        scrutinee_type: &Type,
        interner: &Interner,
    ) -> Option<Type> {
        match pattern {
            Pattern::Wildcard(_) => {
                // Wildcard always matches, nothing to check, no narrowing
                None
            }
            Pattern::Literal(expr) => {
                // Check literal type matches scrutinee type
                if let Ok(lit_type) = self.check_expr(expr, interner)
                    && !self.types_compatible(&lit_type, scrutinee_type, interner)
                    && !self.types_compatible(scrutinee_type, &lit_type, interner)
                {
                    let expected = self.type_display(scrutinee_type);
                    let found = self.type_display(&lit_type);
                    self.add_error(
                        SemanticError::PatternTypeMismatch {
                            expected,
                            found,
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                None
            }
            Pattern::Identifier { name, span } => {
                // Check if this identifier is a known class or record type via EntityRegistry
                let type_id_opt = self.entity_registry.type_by_symbol(
                    *name,
                    interner,
                    &self.name_table,
                    self.current_module,
                );

                if let Some(type_id) = type_id_opt {
                    let type_def = self.entity_registry.get_type(type_id);
                    match type_def.kind {
                        TypeDefKind::Class => {
                            if let Some(class_type) = self
                                .entity_registry
                                .build_class_type(type_id, &self.name_table)
                            {
                                let pattern_type = Type::Class(class_type);
                                self.check_type_pattern_compatibility(
                                    &pattern_type,
                                    scrutinee_type,
                                    *span,
                                    interner,
                                );
                                Some(pattern_type)
                            } else {
                                // Regular identifier binding pattern (fallback)
                                self.scope.define(
                                    *name,
                                    Variable {
                                        ty: scrutinee_type.clone(),
                                        mutable: false,
                                    },
                                );
                                None
                            }
                        }
                        TypeDefKind::Record => {
                            if let Some(record_type) = self
                                .entity_registry
                                .build_record_type(type_id, &self.name_table)
                            {
                                let pattern_type = Type::Record(record_type);
                                self.check_type_pattern_compatibility(
                                    &pattern_type,
                                    scrutinee_type,
                                    *span,
                                    interner,
                                );
                                Some(pattern_type)
                            } else {
                                // Regular identifier binding pattern (fallback)
                                self.scope.define(
                                    *name,
                                    Variable {
                                        ty: scrutinee_type.clone(),
                                        mutable: false,
                                    },
                                );
                                None
                            }
                        }
                        _ => {
                            // Regular identifier binding pattern for other type kinds
                            self.scope.define(
                                *name,
                                Variable {
                                    ty: scrutinee_type.clone(),
                                    mutable: false,
                                },
                            );
                            None
                        }
                    }
                } else {
                    // Regular identifier binding pattern
                    self.scope.define(
                        *name,
                        Variable {
                            ty: scrutinee_type.clone(),
                            mutable: false,
                        },
                    );
                    None
                }
            }
            Pattern::Type { type_expr, span } => {
                let pattern_type = self.resolve_type(type_expr, interner);
                self.check_type_pattern_compatibility(
                    &pattern_type,
                    scrutinee_type,
                    *span,
                    interner,
                );
                Some(pattern_type)
            }
            Pattern::Val { name, span } => {
                // Val pattern compares against existing variable's value
                if let Some(var) = self.scope.get(*name) {
                    let var_ty = var.ty.clone();
                    // Check type compatibility
                    if !self.types_compatible(&var_ty, scrutinee_type, interner)
                        && !self.types_compatible(scrutinee_type, &var_ty, interner)
                    {
                        let expected = self.type_display(scrutinee_type);
                        let found = self.type_display(&var_ty);
                        self.add_error(
                            SemanticError::PatternTypeMismatch {
                                expected,
                                found,
                                span: (*span).into(),
                            },
                            *span,
                        );
                    }
                } else {
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: interner.resolve(*name).to_string(),
                            span: (*span).into(),
                        },
                        *span,
                    );
                }
                // Val patterns don't narrow types
                None
            }
            Pattern::Success { inner, span } => {
                // Success pattern only valid when matching on fallible type
                let success_type = match scrutinee_type {
                    Type::Fallible(ft) => (*ft.success_type).clone(),
                    _ => {
                        let found = self.type_display(scrutinee_type);
                        self.add_error(
                            SemanticError::SuccessPatternOnNonFallible {
                                found,
                                span: (*span).into(),
                            },
                            *span,
                        );
                        return None;
                    }
                };

                // If there's an inner pattern, check it against success type
                if let Some(inner_pattern) = inner {
                    self.check_pattern(inner_pattern, &success_type, interner)
                } else {
                    // Bare success - no narrowing
                    None
                }
            }
            Pattern::Error { inner, span } => {
                // Error pattern only valid when matching on fallible type
                let error_type = match scrutinee_type {
                    Type::Fallible(ft) => (*ft.error_type).clone(),
                    _ => {
                        let found = self.type_display(scrutinee_type);
                        self.add_error(
                            SemanticError::ErrorPatternOnNonFallible {
                                found,
                                span: (*span).into(),
                            },
                            *span,
                        );
                        return None;
                    }
                };

                // If there's an inner pattern, check it against error type
                if let Some(inner_pattern) = inner {
                    self.check_pattern(inner_pattern, &error_type, interner)
                } else {
                    // Bare error - no narrowing
                    None
                }
            }
            Pattern::Tuple { elements, span } => {
                // Tuple pattern - check against tuple type
                if let Type::Tuple(elem_types) = scrutinee_type {
                    if elements.len() != elem_types.len() {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("tuple of {} elements", elem_types.len()),
                                found: format!("tuple pattern with {} elements", elements.len()),
                                span: (*span).into(),
                            },
                            *span,
                        );
                        return None;
                    }
                    // Check each element pattern against its type
                    for (pattern, elem_type) in elements.iter().zip(elem_types.iter()) {
                        self.check_pattern(pattern, elem_type, interner);
                    }
                    None // No type narrowing for tuple patterns
                } else {
                    let found = self.type_display(scrutinee_type);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "tuple".to_string(),
                            found,
                            span: (*span).into(),
                        },
                        *span,
                    );
                    None
                }
            }
        }
    }

    /// Check if a match expression is exhaustive
    pub(crate) fn check_match_exhaustiveness(
        &mut self,
        arms: &[MatchArm],
        scrutinee_type: &Type,
        _span: Span,
        interner: &Interner,
    ) -> bool {
        // Check for catch-all patterns (wildcard or identifier binding)
        let has_catch_all = arms.iter().any(|arm| {
            match &arm.pattern {
                Pattern::Wildcard(_) => true,
                Pattern::Identifier { name, .. } => {
                    // Only a catch-all if NOT a known type name
                    let is_type = self
                        .entity_registry
                        .type_by_symbol(*name, interner, &self.name_table, self.current_module)
                        .is_some();
                    !is_type
                }
                _ => false,
            }
        });

        if has_catch_all {
            return true;
        }

        // For union types, check if all variants are covered by type patterns
        if let Type::Union(variants) = scrutinee_type {
            let mut covered: Vec<bool> = vec![false; variants.len()];

            for arm in arms {
                let pattern_type = match &arm.pattern {
                    Pattern::Type { type_expr, .. } => Some(self.resolve_type(type_expr, interner)),
                    Pattern::Identifier { name, .. } => {
                        // Look up via EntityRegistry
                        self.entity_registry
                            .type_by_symbol(*name, interner, &self.name_table, self.current_module)
                            .and_then(|type_id| {
                                let type_def = self.entity_registry.get_type(type_id);
                                match type_def.kind {
                                    TypeDefKind::Class => self
                                        .entity_registry
                                        .build_class_type(type_id, &self.name_table)
                                        .map(Type::Class),
                                    TypeDefKind::Record => self
                                        .entity_registry
                                        .build_record_type(type_id, &self.name_table)
                                        .map(Type::Record),
                                    _ => None,
                                }
                            })
                    }
                    _ => None,
                };

                if let Some(ref pt) = pattern_type {
                    for (i, variant) in variants.iter().enumerate() {
                        if variant == pt {
                            covered[i] = true;
                        }
                    }
                }
            }

            return covered.iter().all(|&c| c);
        }

        // For non-union types without catch-all, not exhaustive
        false
    }

    /// Check that a type pattern is compatible with the scrutinee type
    fn check_type_pattern_compatibility(
        &mut self,
        pattern_type: &Type,
        scrutinee_type: &Type,
        span: Span,
        interner: &Interner,
    ) {
        // For union types, the pattern type must be one of the variants
        if let Type::Union(variants) = scrutinee_type {
            if !variants.iter().any(|v| v == pattern_type) {
                let expected = self.type_display(scrutinee_type);
                let found = self.type_display(pattern_type);
                self.add_error(
                    SemanticError::PatternTypeMismatch {
                        expected,
                        found,
                        span: span.into(),
                    },
                    span,
                );
            }
        } else if scrutinee_type != pattern_type
            && !self.types_compatible(pattern_type, scrutinee_type, interner)
        {
            // For non-union types, pattern must match or be compatible
            let expected = self.type_display(scrutinee_type);
            let found = self.type_display(pattern_type);
            self.add_error(
                SemanticError::PatternTypeMismatch {
                    expected,
                    found,
                    span: span.into(),
                },
                span,
            );
        }
    }
}
