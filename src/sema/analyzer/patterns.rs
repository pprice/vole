// src/sema/analyzer/patterns.rs

use super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::{LegacyType, NominalType};

impl Analyzer {
    /// Check pattern and return TypeId directly.
    /// This is the Phase 2 entry point - callers should migrate to this.
    #[allow(unused)] // Phase 2 infrastructure
    pub(crate) fn check_pattern_id(
        &mut self,
        pattern: &Pattern,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        let scrutinee_type = self.id_to_type(scrutinee_type_id);
        self.check_pattern(pattern, &scrutinee_type, interner)
            .map(|ty| self.type_to_id(&ty))
    }

    /// Check a pattern against the scrutinee type.
    /// Returns the narrowed type if this pattern narrows the scrutinee (e.g., type patterns).
    #[tracing::instrument(skip(self, interner), fields(scrutinee = %self.type_display(scrutinee_type)))]
    pub(crate) fn check_pattern(
        &mut self,
        pattern: &Pattern,
        scrutinee_type: &LegacyType,
        interner: &Interner,
    ) -> Option<LegacyType> {
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
                // Check if this identifier is a known class or record type via Resolver
                let type_id_opt = self
                    .resolver(interner)
                    .resolve_type(*name, &self.entity_registry);

                if let Some(type_id) = type_id_opt {
                    let type_def = self.entity_registry.get_type(type_id);
                    match type_def.kind {
                        TypeDefKind::Class => {
                            if let Some(class_type) = self.entity_registry.build_class_type(type_id)
                            {
                                let pattern_type =
                                    LegacyType::Nominal(NominalType::Class(class_type));
                                self.check_type_pattern_compatibility(
                                    &pattern_type,
                                    scrutinee_type,
                                    *span,
                                    interner,
                                );
                                Some(pattern_type)
                            } else {
                                // Regular identifier binding pattern (fallback)
                                let ty_id = self.type_arena.borrow_mut().from_type(scrutinee_type);
                                self.scope.define(
                                    *name,
                                    Variable {
                                        ty: ty_id,
                                        mutable: false,
                                    },
                                );
                                None
                            }
                        }
                        TypeDefKind::Record => {
                            if let Some(record_type) =
                                self.entity_registry.build_record_type(type_id)
                            {
                                let pattern_type =
                                    LegacyType::Nominal(NominalType::Record(record_type));
                                self.check_type_pattern_compatibility(
                                    &pattern_type,
                                    scrutinee_type,
                                    *span,
                                    interner,
                                );
                                Some(pattern_type)
                            } else {
                                // Regular identifier binding pattern (fallback)
                                let ty_id = self.type_arena.borrow_mut().from_type(scrutinee_type);
                                self.scope.define(
                                    *name,
                                    Variable {
                                        ty: ty_id,
                                        mutable: false,
                                    },
                                );
                                None
                            }
                        }
                        _ => {
                            // Regular identifier binding pattern for other type kinds
                            let ty_id = self.type_arena.borrow_mut().from_type(scrutinee_type);
                            self.scope.define(
                                *name,
                                Variable {
                                    ty: ty_id,
                                    mutable: false,
                                },
                            );
                            None
                        }
                    }
                } else {
                    // Regular identifier binding pattern
                    let ty_id = self.type_arena.borrow_mut().from_type(scrutinee_type);
                    self.scope.define(
                        *name,
                        Variable {
                            ty: ty_id,
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
                    let var_ty = self.type_arena.borrow().to_type(var.ty);
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
                    LegacyType::Fallible(ft) => (*ft.success_type).clone(),
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
                    LegacyType::Fallible(ft) => (*ft.error_type).clone(),
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
                if let LegacyType::Tuple(elem_types) = scrutinee_type {
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
                    self.type_error("tuple", scrutinee_type, *span);
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
                        // Helper to get fields from generic_info as StructField
                        let get_fields = |type_def: &crate::sema::entity_defs::TypeDef,
                                          arena: &TypeArena|
                         -> Vec<StructField> {
                            type_def
                                .generic_info
                                .as_ref()
                                .map(|gi| {
                                    gi.field_names
                                        .iter()
                                        .zip(gi.field_types.iter())
                                        .enumerate()
                                        .filter_map(|(i, (name_id, ty))| {
                                            Some(StructField {
                                                name: self.name_table.last_segment_str(*name_id)?,
                                                ty: arena.to_type(*ty),
                                                slot: i,
                                            })
                                        })
                                        .collect()
                                })
                                .unwrap_or_default()
                        };
                        let (pattern_type, type_fields) = match type_def.kind {
                            TypeDefKind::Record => {
                                if let Some(record_type) =
                                    self.entity_registry.build_record_type(type_id)
                                {
                                    let fields_ref =
                                        get_fields(type_def, &self.type_arena.borrow());
                                    (
                                        Some(LegacyType::Nominal(NominalType::Record(record_type))),
                                        fields_ref,
                                    )
                                } else {
                                    (None, vec![])
                                }
                            }
                            TypeDefKind::Class => {
                                if let Some(class_type) =
                                    self.entity_registry.build_class_type(type_id)
                                {
                                    let fields_ref =
                                        get_fields(type_def, &self.type_arena.borrow());
                                    (
                                        Some(LegacyType::Nominal(NominalType::Class(class_type))),
                                        fields_ref,
                                    )
                                } else {
                                    (None, vec![])
                                }
                            }
                            TypeDefKind::ErrorType => {
                                // Error type destructuring: error Overflow { value, max }
                                // Get fields from EntityRegistry (like classes/records)
                                let arena = self.type_arena.borrow();
                                let fields_ref: Vec<StructField> = self
                                    .entity_registry
                                    .fields_on_type(type_id)
                                    .filter_map(|field_id| {
                                        let field = self.entity_registry.get_field(field_id);
                                        Some(StructField {
                                            name: self
                                                .name_table
                                                .last_segment_str(field.name_id)?,
                                            ty: arena.to_type(field.ty),
                                            slot: field.slot,
                                        })
                                    })
                                    .collect();
                                let error_info = ErrorTypeInfo {
                                    type_def_id: type_id,
                                };
                                (
                                    Some(LegacyType::Nominal(NominalType::Error(error_info))),
                                    fields_ref,
                                )
                            }
                            _ => {
                                self.add_error(
                                    SemanticError::TypeMismatch {
                                        expected: "record, class, or error type".to_string(),
                                        found: interner.resolve(*name).to_string(),
                                        span: (*span).into(),
                                    },
                                    *span,
                                );
                                return None;
                            }
                        };

                        if let Some(ref pt) = pattern_type {
                            // Check compatibility with scrutinee
                            self.check_type_pattern_compatibility(
                                pt,
                                scrutinee_type,
                                *span,
                                interner,
                            );

                            // Bind each field
                            for field_pattern in fields {
                                let field_name_str = interner.resolve(field_pattern.field_name);
                                if let Some(field) =
                                    type_fields.iter().find(|f| f.name == field_name_str)
                                {
                                    let ty_id = self.type_arena.borrow_mut().from_type(&field.ty);
                                    self.scope.define(
                                        field_pattern.binding,
                                        Variable {
                                            ty: ty_id,
                                            mutable: false,
                                        },
                                    );
                                } else {
                                    self.add_error(
                                        SemanticError::UnknownField {
                                            ty: interner.resolve(*name).to_string(),
                                            field: field_name_str.to_string(),
                                            span: field_pattern.span.into(),
                                        },
                                        field_pattern.span,
                                    );
                                }
                            }
                        }
                        pattern_type
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
                    // Untyped record pattern in match - bind fields from scrutinee type
                    // Get fields from EntityRegistry via type_def_id
                    let type_fields: Option<Vec<StructField>> = match scrutinee_type {
                        LegacyType::Nominal(NominalType::Record(r)) => {
                            let type_def = self.entity_registry.get_type(r.type_def_id);
                            let arena = self.type_arena.borrow();
                            type_def.generic_info.as_ref().map(|gi| {
                                gi.field_names
                                    .iter()
                                    .zip(gi.field_types.iter())
                                    .enumerate()
                                    .filter_map(|(i, (name_id, ty))| {
                                        Some(StructField {
                                            name: self.name_table.last_segment_str(*name_id)?,
                                            ty: arena.to_type(*ty),
                                            slot: i,
                                        })
                                    })
                                    .collect()
                            })
                        }
                        LegacyType::Nominal(NominalType::Class(c)) => {
                            let type_def = self.entity_registry.get_type(c.type_def_id);
                            let arena = self.type_arena.borrow();
                            type_def.generic_info.as_ref().map(|gi| {
                                gi.field_names
                                    .iter()
                                    .zip(gi.field_types.iter())
                                    .enumerate()
                                    .filter_map(|(i, (name_id, ty))| {
                                        Some(StructField {
                                            name: self.name_table.last_segment_str(*name_id)?,
                                            ty: arena.to_type(*ty),
                                            slot: i,
                                        })
                                    })
                                    .collect()
                            })
                        }
                        _ => {
                            self.type_error("record or class", scrutinee_type, *span);
                            None
                        }
                    };

                    if let Some(type_fields) = type_fields {
                        let type_name_str = match scrutinee_type {
                            LegacyType::Nominal(NominalType::Record(r)) => {
                                let type_def = self.entity_registry.get_type(r.type_def_id);
                                self.name_table.display(type_def.name_id)
                            }
                            LegacyType::Nominal(NominalType::Class(c)) => {
                                let type_def = self.entity_registry.get_type(c.type_def_id);
                                self.name_table.display(type_def.name_id)
                            }
                            _ => "unknown".to_string(),
                        };
                        for field_pattern in fields {
                            let field_name_str = interner.resolve(field_pattern.field_name);
                            if let Some(field) =
                                type_fields.iter().find(|f| f.name == field_name_str)
                            {
                                let ty_id = self.type_arena.borrow_mut().from_type(&field.ty);
                                self.scope.define(
                                    field_pattern.binding,
                                    Variable {
                                        ty: ty_id,
                                        mutable: false,
                                    },
                                );
                            } else {
                                self.add_error(
                                    SemanticError::UnknownField {
                                        ty: type_name_str.clone(),
                                        field: field_name_str.to_string(),
                                        span: field_pattern.span.into(),
                                    },
                                    field_pattern.span,
                                );
                            }
                        }
                    }
                    None
                }
            }
        }
    }

    /// Check if a match expression is exhaustive
    pub(crate) fn check_match_exhaustiveness(
        &mut self,
        arms: &[MatchArm],
        scrutinee_type: &LegacyType,
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
        if let LegacyType::Union(variants) = scrutinee_type {
            let mut covered: Vec<bool> = vec![false; variants.len()];

            for arm in arms {
                let pattern_type = self.get_pattern_type(&arm.pattern, interner);

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

        // For non-union types, check if any pattern covers the exact type
        for arm in arms {
            let pattern_type = self.get_pattern_type(&arm.pattern, interner);
            if let Some(pt) = pattern_type
                && pt == *scrutinee_type
            {
                return true;
            }
        }

        false
    }

    /// Extract the type that a pattern matches against, if it's a type pattern
    fn get_pattern_type(&mut self, pattern: &Pattern, interner: &Interner) -> Option<LegacyType> {
        match pattern {
            Pattern::Type { type_expr, .. } => Some(self.resolve_type(type_expr, interner)),
            Pattern::Identifier { name, .. } => {
                // Look up via Resolver
                self.resolver(interner)
                    .resolve_type(*name, &self.entity_registry)
                    .and_then(|type_id| {
                        let type_def = self.entity_registry.get_type(type_id);
                        match type_def.kind {
                            TypeDefKind::Class => self
                                .entity_registry
                                .build_class_type(type_id)
                                .map(|c| LegacyType::Nominal(NominalType::Class(c))),
                            TypeDefKind::Record => self
                                .entity_registry
                                .build_record_type(type_id)
                                .map(|r| LegacyType::Nominal(NominalType::Record(r))),
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
                    .and_then(|type_id| {
                        let type_def = self.entity_registry.get_type(type_id);
                        match type_def.kind {
                            TypeDefKind::Class => self
                                .entity_registry
                                .build_class_type(type_id)
                                .map(|c| LegacyType::Nominal(NominalType::Class(c))),
                            TypeDefKind::Record => self
                                .entity_registry
                                .build_record_type(type_id)
                                .map(|r| LegacyType::Nominal(NominalType::Record(r))),
                            _ => None,
                        }
                    })
            }
            _ => None,
        }
    }

    /// Check that a type pattern is compatible with the scrutinee type
    fn check_type_pattern_compatibility(
        &mut self,
        pattern_type: &LegacyType,
        scrutinee_type: &LegacyType,
        span: Span,
        interner: &Interner,
    ) {
        // For union types, the pattern type must be one of the variants
        if let LegacyType::Union(variants) = scrutinee_type {
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
