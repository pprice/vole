// src/sema/analyzer/patterns.rs

use super::*;
use crate::analysis_cache::IsCheckResult;
use crate::type_arena::TypeId as ArenaTypeId;
use crate::types::StructFieldId;
use vole_frontend::PatternKind;

impl Analyzer {
    /// Check pattern and return TypeId directly.
    pub(crate) fn check_pattern_id(
        &mut self,
        pattern: &Pattern,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        match &pattern.kind {
            PatternKind::Wildcard => {
                // Wildcard always matches, nothing to check, no narrowing
                None
            }
            PatternKind::Literal(expr) => {
                // Check literal type matches scrutinee type
                if let Ok(lit_type_id) = self.check_expr(expr, interner)
                    && !self.types_compatible_id(lit_type_id, scrutinee_type_id, interner)
                    && !self.types_compatible_id(scrutinee_type_id, lit_type_id, interner)
                {
                    let expected = self.type_display_id(scrutinee_type_id);
                    let found = self.type_display_id(lit_type_id);
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
            PatternKind::Identifier { name } => {
                let span = pattern.span;
                // Check if this identifier is a known class or record type via Resolver
                let type_id_opt = self
                    .resolver(interner)
                    .resolve_type(*name, &self.entity_registry());

                if let Some(type_def_id) = type_id_opt {
                    let kind = {
                        let registry = self.entity_registry();
                        registry.get_type(type_def_id).kind
                    };
                    match kind {
                        TypeDefKind::Class => {
                            // Build class type as TypeId directly
                            let pattern_type_id = {
                                let mut arena = self.type_arena_mut();
                                arena.class(type_def_id, vec![])
                            };
                            self.check_type_pattern_compatibility_id(
                                pattern_type_id,
                                scrutinee_type_id,
                                span,
                                interner,
                            );

                            // Compute IsCheckResult for codegen
                            let is_check_result = self.compute_type_pattern_check_result(
                                pattern_type_id,
                                scrutinee_type_id,
                            );
                            self.record_is_check_result(pattern.id, is_check_result);

                            Some(pattern_type_id)
                        }
                        TypeDefKind::Record => {
                            // Build record type as TypeId directly
                            let pattern_type_id = {
                                let mut arena = self.type_arena_mut();
                                arena.record(type_def_id, vec![])
                            };
                            self.check_type_pattern_compatibility_id(
                                pattern_type_id,
                                scrutinee_type_id,
                                span,
                                interner,
                            );

                            // Compute IsCheckResult for codegen
                            let is_check_result = self.compute_type_pattern_check_result(
                                pattern_type_id,
                                scrutinee_type_id,
                            );
                            self.record_is_check_result(pattern.id, is_check_result);

                            Some(pattern_type_id)
                        }
                        _ => {
                            // Regular identifier binding pattern for other type kinds
                            self.scope.define(
                                *name,
                                Variable {
                                    ty: scrutinee_type_id,
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
                            ty: scrutinee_type_id,
                            mutable: false,
                        },
                    );
                    None
                }
            }
            PatternKind::Type { type_expr } => {
                let span = pattern.span;
                // Resolve type and check compatibility using TypeId
                let pattern_type_id = self.resolve_type_id(type_expr, interner);
                self.check_type_pattern_compatibility_id(
                    pattern_type_id,
                    scrutinee_type_id,
                    span,
                    interner,
                );

                // Compute IsCheckResult for codegen
                let is_check_result =
                    self.compute_type_pattern_check_result(pattern_type_id, scrutinee_type_id);
                self.record_is_check_result(pattern.id, is_check_result);

                Some(pattern_type_id)
            }
            PatternKind::Val { name } => {
                let span = pattern.span;
                // Val pattern compares against existing variable's value
                let var_ty_id = self.scope.get(*name).map(|v| v.ty);
                if let Some(var_ty_id) = var_ty_id {
                    // Check type compatibility using TypeId
                    if !self.types_compatible_id(var_ty_id, scrutinee_type_id, interner)
                        && !self.types_compatible_id(scrutinee_type_id, var_ty_id, interner)
                    {
                        let expected = self.type_display_id(scrutinee_type_id);
                        let found = self.type_display_id(var_ty_id);
                        self.add_error(
                            SemanticError::PatternTypeMismatch {
                                expected,
                                found,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                } else {
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: interner.resolve(*name).to_string(),
                            span: span.into(),
                        },
                        span,
                    );
                }
                // Val patterns don't narrow types
                None
            }
            PatternKind::Success { inner } => {
                let span = pattern.span;
                // Success pattern only valid when matching on fallible type
                let fallible_info = self.type_arena().unwrap_fallible(scrutinee_type_id);
                let Some((success_type_id, _error_type_id)) = fallible_info else {
                    let found = self.type_display_id(scrutinee_type_id);
                    self.add_error(
                        SemanticError::SuccessPatternOnNonFallible {
                            found,
                            span: span.into(),
                        },
                        span,
                    );
                    return None;
                };

                // If there's an inner pattern, check it against success type
                if let Some(inner_pattern) = inner {
                    self.check_pattern_id(inner_pattern, success_type_id, interner)
                } else {
                    // Bare success - no narrowing
                    None
                }
            }
            PatternKind::Error { inner } => {
                let span = pattern.span;
                // Error pattern only valid when matching on fallible type
                let fallible_info = self.type_arena().unwrap_fallible(scrutinee_type_id);
                let Some((_success_type_id, error_type_id)) = fallible_info else {
                    let found = self.type_display_id(scrutinee_type_id);
                    self.add_error(
                        SemanticError::ErrorPatternOnNonFallible {
                            found,
                            span: span.into(),
                        },
                        span,
                    );
                    return None;
                };

                // If there's an inner pattern, check it against error type
                if let Some(inner_pattern) = inner {
                    self.check_pattern_id(inner_pattern, error_type_id, interner)
                } else {
                    // Bare error - no narrowing
                    None
                }
            }
            PatternKind::Tuple { elements } => {
                let span = pattern.span;
                // Tuple pattern - check against tuple type
                let tuple_elements = self
                    .type_arena()
                    .unwrap_tuple(scrutinee_type_id)
                    .map(|v| v.to_vec());
                if let Some(elem_type_ids) = tuple_elements {
                    if elements.len() != elem_type_ids.len() {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("tuple of {} elements", elem_type_ids.len()),
                                found: format!("tuple pattern with {} elements", elements.len()),
                                span: span.into(),
                            },
                            span,
                        );
                        return None;
                    }
                    // Check each element pattern against its type
                    for (pat, elem_type_id) in elements.iter().zip(elem_type_ids.iter()) {
                        self.check_pattern_id(pat, *elem_type_id, interner);
                    }
                    None // No type narrowing for tuple patterns
                } else {
                    self.type_error_id("tuple", scrutinee_type_id, span);
                    None
                }
            }
            PatternKind::Record { type_name, fields } => {
                let span = pattern.span;
                // Typed record pattern: TypeName { x, y }
                if let Some(name) = type_name {
                    // Look up the type via Resolver
                    let type_id_opt = self
                        .resolver(interner)
                        .resolve_type(*name, &self.entity_registry());

                    if let Some(type_id) = type_id_opt {
                        // Extract kind and generic_info upfront to avoid holding borrow
                        let (kind, generic_info) = {
                            let registry = self.entity_registry();
                            let type_def = registry.get_type(type_id);
                            (type_def.kind, type_def.generic_info.clone())
                        };

                        // Get fields from generic_info
                        let get_fields_from_info =
                            |gi: &crate::entity_defs::GenericTypeInfo| -> Vec<StructFieldId> {
                                gi.field_names
                                    .iter()
                                    .zip(gi.field_types.iter())
                                    .enumerate()
                                    .map(|(i, (&name_id, &ty))| StructFieldId {
                                        name_id,
                                        ty,
                                        slot: i,
                                    })
                                    .collect()
                            };

                        let (pattern_type_id, type_fields) = match kind {
                            TypeDefKind::Record => {
                                if self.entity_registry().build_record_type(type_id).is_some() {
                                    let fields_ref = generic_info
                                        .as_ref()
                                        .map(get_fields_from_info)
                                        .unwrap_or_default();
                                    let record_type_id =
                                        self.type_arena_mut().record(type_id, Vec::new());
                                    (Some(record_type_id), fields_ref)
                                } else {
                                    (None, vec![])
                                }
                            }
                            TypeDefKind::Class => {
                                if self.entity_registry().build_class_type(type_id).is_some() {
                                    let fields_ref = generic_info
                                        .as_ref()
                                        .map(get_fields_from_info)
                                        .unwrap_or_default();
                                    let class_type_id =
                                        self.type_arena_mut().class(type_id, Vec::new());
                                    (Some(class_type_id), fields_ref)
                                } else {
                                    (None, vec![])
                                }
                            }
                            TypeDefKind::ErrorType => {
                                // Error type destructuring: error Overflow { value, max }
                                // Get fields from EntityRegistry - collect field_ids first
                                let field_ids: Vec<_> =
                                    self.entity_registry().fields_on_type(type_id).collect();
                                let fields_ref: Vec<StructFieldId> = field_ids
                                    .into_iter()
                                    .map(|field_id| {
                                        let registry = self.entity_registry();
                                        let field = registry.get_field(field_id);
                                        StructFieldId {
                                            name_id: field.name_id,
                                            ty: field.ty,
                                            slot: field.slot,
                                        }
                                    })
                                    .collect();
                                let error_type_id = self.type_arena_mut().error_type(type_id);
                                (Some(error_type_id), fields_ref)
                            }
                            _ => {
                                self.add_error(
                                    SemanticError::PatternTypeMismatch {
                                        expected: "record, class, or error".to_string(),
                                        found: interner.resolve(*name).to_string(),
                                        span: (span).into(),
                                    },
                                    span,
                                );
                                (None, vec![])
                            }
                        };

                        // Check pattern fields
                        self.check_record_pattern_fields_id(fields, &type_fields, span, interner);

                        // Check compatibility with scrutinee
                        if let Some(pattern_type_id) = pattern_type_id {
                            self.check_type_pattern_compatibility_id(
                                pattern_type_id,
                                scrutinee_type_id,
                                span,
                                interner,
                            );

                            // Compute IsCheckResult for codegen
                            let is_check_result = self.compute_type_pattern_check_result(
                                pattern_type_id,
                                scrutinee_type_id,
                            );
                            self.record_is_check_result(pattern.id, is_check_result);

                            Some(pattern_type_id)
                        } else {
                            None
                        }
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(*name).to_string(),
                                span: (span).into(),
                            },
                            span,
                        );
                        None
                    }
                } else {
                    // Anonymous record pattern - check against scrutinee's fields
                    self.check_anonymous_record_pattern_id(
                        fields,
                        scrutinee_type_id,
                        span,
                        interner,
                    );
                    None
                }
            }
        }
    }

    /// Check type pattern compatibility (TypeId version)
    fn check_type_pattern_compatibility_id(
        &mut self,
        pattern_type_id: ArenaTypeId,
        scrutinee_type_id: ArenaTypeId,
        span: Span,
        interner: &Interner,
    ) {
        // Check if pattern type is compatible with scrutinee
        if !self.types_compatible_id(pattern_type_id, scrutinee_type_id, interner)
            && !self.types_compatible_id(scrutinee_type_id, pattern_type_id, interner)
        {
            let expected = self.type_display_id(scrutinee_type_id);
            let found = self.type_display_id(pattern_type_id);
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

    /// Compute IsCheckResult for a type pattern.
    /// Determines whether the check can be resolved at compile time or needs a runtime tag check.
    fn compute_type_pattern_check_result(
        &self,
        pattern_type_id: ArenaTypeId,
        scrutinee_type_id: ArenaTypeId,
    ) -> IsCheckResult {
        let union_variants = self.type_arena().unwrap_union(scrutinee_type_id).cloned();
        if let Some(variants) = union_variants {
            // Union type: find which variant the pattern type matches
            if let Some(index) = variants.iter().position(|&v| v == pattern_type_id) {
                IsCheckResult::CheckTag(index as u32)
            } else {
                // Pattern type is not a variant - always false
                IsCheckResult::AlwaysFalse
            }
        } else {
            // Non-union type: check direct type equality
            if scrutinee_type_id == pattern_type_id {
                IsCheckResult::AlwaysTrue
            } else {
                IsCheckResult::AlwaysFalse
            }
        }
    }

    /// Check record pattern fields against type fields (TypeId version)
    fn check_record_pattern_fields_id(
        &mut self,
        pattern_fields: &[RecordFieldPattern],
        type_fields: &[StructFieldId],
        span: Span,
        interner: &Interner,
    ) {
        for field_pat in pattern_fields {
            let field_name_str = interner.resolve(field_pat.field_name);
            // Find field in type
            let field_type_id = type_fields.iter().find_map(|f| {
                self.name_table()
                    .last_segment_str(f.name_id)
                    .filter(|s| *s == field_name_str)
                    .map(|_| f.ty)
            });
            if let Some(field_type_id) = field_type_id {
                // Bind the variable (binding may be different from field_name if renamed)
                self.scope.define(
                    field_pat.binding,
                    Variable {
                        ty: field_type_id,
                        mutable: false,
                    },
                );
            } else {
                // Unknown field in pattern
                self.add_error(
                    SemanticError::UnknownField {
                        ty: "record".to_string(),
                        field: field_name_str.to_string(),
                        span: span.into(),
                    },
                    span,
                );
            }
        }
    }

    /// Check anonymous record pattern against scrutinee's fields (TypeId version)
    fn check_anonymous_record_pattern_id(
        &mut self,
        pattern_fields: &[RecordFieldPattern],
        scrutinee_type_id: ArenaTypeId,
        span: Span,
        interner: &Interner,
    ) {
        // Try to get fields from the scrutinee type (record or class)
        let type_def_info = {
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            arena
                .unwrap_nominal(scrutinee_type_id)
                .filter(|(_, _, kind)| matches!(kind, NominalKind::Class | NominalKind::Record))
                .map(|(id, _, _)| id)
        };

        if let Some(type_def_id) = type_def_info {
            // Clone generic_info to avoid holding borrow
            let generic_info = {
                let registry = self.entity_registry();
                registry.get_type(type_def_id).generic_info.clone()
            };
            // Get fields from generic_info
            let type_fields: Vec<StructFieldId> = generic_info
                .as_ref()
                .map(|gi| {
                    gi.field_names
                        .iter()
                        .zip(gi.field_types.iter())
                        .enumerate()
                        .map(|(i, (&name_id, &ty))| StructFieldId {
                            name_id,
                            ty,
                            slot: i,
                        })
                        .collect()
                })
                .unwrap_or_default();

            self.check_record_pattern_fields_id(pattern_fields, &type_fields, span, interner);
        } else {
            // Not a record/class type
            let found = self.type_display_id(scrutinee_type_id);
            self.add_error(
                SemanticError::PatternTypeMismatch {
                    expected: "record or class".to_string(),
                    found,
                    span: span.into(),
                },
                span,
            );
        }
    }

    /// Check if a match expression is exhaustive (TypeId version)
    pub(crate) fn check_match_exhaustiveness_id(
        &mut self,
        arms: &[MatchArm],
        scrutinee_type_id: ArenaTypeId,
        _span: Span,
        interner: &Interner,
    ) -> bool {
        // Check for catch-all patterns (wildcard or identifier binding)
        let has_catch_all = arms.iter().any(|arm| {
            match &arm.pattern.kind {
                PatternKind::Wildcard => true,
                PatternKind::Identifier { name } => {
                    // Only a catch-all if NOT a known type name
                    let is_type = self
                        .resolver(interner)
                        .resolve_type(*name, &self.entity_registry())
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
        let union_variants: Option<Vec<ArenaTypeId>> = {
            let arena = self.type_arena();
            arena.unwrap_union(scrutinee_type_id).map(|v| v.to_vec())
        };

        if let Some(variants) = union_variants {
            let mut covered: Vec<bool> = vec![false; variants.len()];

            for arm in arms {
                let pattern_type_id = self.get_pattern_type_id(&arm.pattern, interner);

                if let Some(pt_id) = pattern_type_id {
                    for (i, &variant_id) in variants.iter().enumerate() {
                        if variant_id == pt_id {
                            covered[i] = true;
                        }
                    }
                }
            }

            return covered.iter().all(|&c| c);
        }

        // For non-union types, check if any pattern covers the exact type
        for arm in arms {
            let pattern_type_id = self.get_pattern_type_id(&arm.pattern, interner);
            if let Some(pt_id) = pattern_type_id
                && pt_id == scrutinee_type_id
            {
                return true;
            }
        }

        false
    }

    /// Extract the TypeId that a pattern matches against, if it's a type pattern
    fn get_pattern_type_id(
        &mut self,
        pattern: &Pattern,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        match &pattern.kind {
            PatternKind::Type { type_expr } => Some(self.resolve_type_id(type_expr, interner)),
            PatternKind::Identifier { name } => {
                // Look up via Resolver - get type_def_id first to drop ResolverGuard
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type(*name, &self.entity_registry());
                type_def_id.and_then(|type_def_id| {
                    let kind = self.entity_registry().get_type(type_def_id).kind;
                    match kind {
                        TypeDefKind::Class => {
                            self.type_arena_mut().class(type_def_id, vec![]).into()
                        }
                        TypeDefKind::Record => {
                            self.type_arena_mut().record(type_def_id, vec![]).into()
                        }
                        _ => None,
                    }
                })
            }
            PatternKind::Record {
                type_name: Some(name),
                ..
            } => {
                // Typed record pattern: Point { x, y } covers type Point
                // Get type_def_id first to drop ResolverGuard
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type(*name, &self.entity_registry());
                type_def_id.and_then(|type_def_id| {
                    let kind = self.entity_registry().get_type(type_def_id).kind;
                    match kind {
                        TypeDefKind::Class => {
                            self.type_arena_mut().class(type_def_id, vec![]).into()
                        }
                        TypeDefKind::Record => {
                            self.type_arena_mut().record(type_def_id, vec![]).into()
                        }
                        _ => None,
                    }
                })
            }
            _ => None,
        }
    }
}
