// src/sema/analyzer/patterns.rs

use super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::StructFieldId;

impl Analyzer {
    /// Check pattern and return TypeId directly (TypeId version).
    /// Handles most pattern types natively, falls back to DisplayType version for complex patterns.
    pub(crate) fn check_pattern_id(
        &mut self,
        pattern: &Pattern,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        match pattern {
            Pattern::Wildcard(_) => {
                // Wildcard always matches, nothing to check, no narrowing
                None
            }
            Pattern::Literal(expr) => {
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
            Pattern::Identifier { name, span } => {
                // Check if this identifier is a known class or record type via Resolver
                let type_id_opt = self
                    .resolver(interner)
                    .resolve_type(*name, &self.entity_registry);

                if let Some(type_def_id) = type_id_opt {
                    let type_def = self.entity_registry.get_type(type_def_id);
                    match type_def.kind {
                        TypeDefKind::Class => {
                            // Build class type as TypeId directly
                            let pattern_type_id = {
                                let mut arena = self.type_arena.borrow_mut();
                                arena.class(type_def_id, vec![])
                            };
                            self.check_type_pattern_compatibility_id(
                                pattern_type_id,
                                scrutinee_type_id,
                                *span,
                                interner,
                            );
                            Some(pattern_type_id)
                        }
                        TypeDefKind::Record => {
                            // Build record type as TypeId directly
                            let pattern_type_id = {
                                let mut arena = self.type_arena.borrow_mut();
                                arena.record(type_def_id, vec![])
                            };
                            self.check_type_pattern_compatibility_id(
                                pattern_type_id,
                                scrutinee_type_id,
                                *span,
                                interner,
                            );
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
            Pattern::Type { type_expr, span } => {
                // Resolve type and check compatibility using TypeId
                let pattern_type_id = self.resolve_type_id(type_expr, interner);
                self.check_type_pattern_compatibility_id(
                    pattern_type_id,
                    scrutinee_type_id,
                    *span,
                    interner,
                );
                Some(pattern_type_id)
            }
            Pattern::Val { name, span } => {
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
                let fallible_info = self.type_arena.borrow().unwrap_fallible(scrutinee_type_id);
                let Some((success_type_id, _error_type_id)) = fallible_info else {
                    let found = self.type_display_id(scrutinee_type_id);
                    self.add_error(
                        SemanticError::SuccessPatternOnNonFallible {
                            found,
                            span: (*span).into(),
                        },
                        *span,
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
            Pattern::Error { inner, span } => {
                // Error pattern only valid when matching on fallible type
                let fallible_info = self.type_arena.borrow().unwrap_fallible(scrutinee_type_id);
                let Some((_success_type_id, error_type_id)) = fallible_info else {
                    let found = self.type_display_id(scrutinee_type_id);
                    self.add_error(
                        SemanticError::ErrorPatternOnNonFallible {
                            found,
                            span: (*span).into(),
                        },
                        *span,
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
            Pattern::Tuple { elements, span } => {
                // Tuple pattern - check against tuple type
                let tuple_elements = self
                    .type_arena
                    .borrow()
                    .unwrap_tuple(scrutinee_type_id)
                    .map(|v| v.to_vec());
                if let Some(elem_type_ids) = tuple_elements {
                    if elements.len() != elem_type_ids.len() {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("tuple of {} elements", elem_type_ids.len()),
                                found: format!("tuple pattern with {} elements", elements.len()),
                                span: (*span).into(),
                            },
                            *span,
                        );
                        return None;
                    }
                    // Check each element pattern against its type
                    for (pattern, elem_type_id) in elements.iter().zip(elem_type_ids.iter()) {
                        self.check_pattern_id(pattern, *elem_type_id, interner);
                    }
                    None // No type narrowing for tuple patterns
                } else {
                    self.type_error_id("tuple", scrutinee_type_id, *span);
                    None
                }
            }
            Pattern::Record {
                type_name,
                fields,
                span,
            } => {
                // Typed record pattern: TypeName { x, y }
                if let Some(name) = type_name {
                    // Look up the type via Resolver
                    let type_id_opt = self
                        .resolver(interner)
                        .resolve_type(*name, &self.entity_registry);

                    if let Some(type_id) = type_id_opt {
                        let type_def = self.entity_registry.get_type(type_id);
                        // Get fields from generic_info
                        let get_fields_id =
                            |type_def: &crate::sema::entity_defs::TypeDef| -> Vec<StructFieldId> {
                                type_def
                                    .generic_info
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
                                    .unwrap_or_default()
                            };

                        let (pattern_type_id, type_fields) = match type_def.kind {
                            TypeDefKind::Record => {
                                if self.entity_registry.build_record_type(type_id).is_some() {
                                    let fields_ref = get_fields_id(type_def);
                                    let record_type_id =
                                        self.type_arena.borrow_mut().record(type_id, Vec::new());
                                    (Some(record_type_id), fields_ref)
                                } else {
                                    (None, vec![])
                                }
                            }
                            TypeDefKind::Class => {
                                if self.entity_registry.build_class_type(type_id).is_some() {
                                    let fields_ref = get_fields_id(type_def);
                                    let class_type_id =
                                        self.type_arena.borrow_mut().class(type_id, Vec::new());
                                    (Some(class_type_id), fields_ref)
                                } else {
                                    (None, vec![])
                                }
                            }
                            TypeDefKind::ErrorType => {
                                // Error type destructuring: error Overflow { value, max }
                                // Get fields from EntityRegistry
                                let fields_ref: Vec<StructFieldId> = self
                                    .entity_registry
                                    .fields_on_type(type_id)
                                    .map(|field_id| {
                                        let field = self.entity_registry.get_field(field_id);
                                        StructFieldId {
                                            name_id: field.name_id,
                                            ty: field.ty,
                                            slot: field.slot,
                                        }
                                    })
                                    .collect();
                                let error_type_id =
                                    self.type_arena.borrow_mut().error_type(type_id);
                                (Some(error_type_id), fields_ref)
                            }
                            _ => {
                                self.add_error(
                                    SemanticError::PatternTypeMismatch {
                                        expected: "record, class, or error".to_string(),
                                        found: interner.resolve(*name).to_string(),
                                        span: (*span).into(),
                                    },
                                    *span,
                                );
                                (None, vec![])
                            }
                        };

                        // Check pattern fields
                        self.check_record_pattern_fields_id(fields, &type_fields, *span, interner);

                        // Check compatibility with scrutinee
                        if let Some(pattern_type_id) = pattern_type_id {
                            self.check_type_pattern_compatibility_id(
                                pattern_type_id,
                                scrutinee_type_id,
                                *span,
                                interner,
                            );
                            Some(pattern_type_id)
                        } else {
                            None
                        }
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(*name).to_string(),
                                span: (*span).into(),
                            },
                            *span,
                        );
                        None
                    }
                } else {
                    // Anonymous record pattern - check against scrutinee's fields
                    self.check_anonymous_record_pattern_id(
                        fields,
                        scrutinee_type_id,
                        *span,
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
                self.name_table
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
            let arena = self.type_arena.borrow();
            if let Some((type_def_id, _args)) = arena.unwrap_record(scrutinee_type_id) {
                Some(type_def_id)
            } else if let Some((type_def_id, _args)) = arena.unwrap_class(scrutinee_type_id) {
                Some(type_def_id)
            } else {
                None
            }
        };

        if let Some(type_def_id) = type_def_info {
            let type_def = self.entity_registry.get_type(type_def_id);
            // Get fields from generic_info
            let type_fields: Vec<StructFieldId> = type_def
                .generic_info
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
            match &arm.pattern {
                Pattern::Wildcard(_) => true,
                Pattern::Identifier { name, .. } => {
                    // Only a catch-all if NOT a known type name
                    let is_type = self
                        .resolver(interner)
                        .resolve_type(*name, &self.entity_registry)
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
            let arena = self.type_arena.borrow();
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
        match pattern {
            Pattern::Type { type_expr, .. } => Some(self.resolve_type_id(type_expr, interner)),
            Pattern::Identifier { name, .. } => {
                // Look up via Resolver
                self.resolver(interner)
                    .resolve_type(*name, &self.entity_registry)
                    .and_then(|type_def_id| {
                        let type_def = self.entity_registry.get_type(type_def_id);
                        match type_def.kind {
                            TypeDefKind::Class => self
                                .type_arena
                                .borrow_mut()
                                .class(type_def_id, vec![])
                                .into(),
                            TypeDefKind::Record => self
                                .type_arena
                                .borrow_mut()
                                .record(type_def_id, vec![])
                                .into(),
                            _ => None,
                        }
                    })
            }
            Pattern::Record {
                type_name: Some(name),
                ..
            } => {
                // Typed record pattern: Point { x, y } covers type Point
                self.resolver(interner)
                    .resolve_type(*name, &self.entity_registry)
                    .and_then(|type_def_id| {
                        let type_def = self.entity_registry.get_type(type_def_id);
                        match type_def.kind {
                            TypeDefKind::Class => self
                                .type_arena
                                .borrow_mut()
                                .class(type_def_id, vec![])
                                .into(),
                            TypeDefKind::Record => self
                                .type_arena
                                .borrow_mut()
                                .record(type_def_id, vec![])
                                .into(),
                            _ => None,
                        }
                    })
            }
            _ => None,
        }
    }
}
