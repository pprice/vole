use super::super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::{LegacyType, NominalType};

impl Analyzer {
    pub(super) fn check_assign_expr(
        &mut self,
        expr: &Expr,
        assign: &AssignExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // First, determine the expected type from the target (bidirectional type checking)
        let (target_ty_id, is_mutable, target_valid) = match &assign.target {
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    (var.ty, var.mutable, true)
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    (ArenaTypeId::INVALID, false, false)
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty_id = self.check_expr(object, interner)?;
                let obj_ty = self.id_to_type(obj_ty_id);
                let field_name = interner.resolve(*field);

                match &obj_ty {
                    LegacyType::Nominal(NominalType::Class(c)) => {
                        // Look up field via EntityRegistry
                        let type_def = self.entity_registry.get_type(c.type_def_id);
                        let type_name = self
                            .name_table
                            .last_segment_str(type_def.name_id)
                            .unwrap_or_else(|| "class".to_string());

                        if let Some(ref generic_info) = type_def.generic_info {
                            if let Some(idx) = generic_info.field_names.iter().position(|name_id| {
                                self.name_table.last_segment_str(*name_id).as_deref()
                                    == Some(field_name)
                            }) {
                                // Substitute type args via arena if any
                                let field_type_id = generic_info.field_types[idx];
                                let resolved_type_id = if c.type_args.is_empty() {
                                    field_type_id
                                } else {
                                    let mut arena = self.type_arena.borrow_mut();
                                    let subs_id: hashbrown::HashMap<_, _> = generic_info
                                        .type_params
                                        .iter()
                                        .zip(c.type_args.iter())
                                        .map(|(tp, arg)| (tp.name_id, arena.from_type(arg)))
                                        .collect();
                                    arena.substitute(field_type_id, &subs_id)
                                };
                                (resolved_type_id, true, true)
                            } else {
                                self.add_error(
                                    SemanticError::UnknownField {
                                        ty: type_name,
                                        field: field_name.to_string(),
                                        span: (*field_span).into(),
                                    },
                                    *field_span,
                                );
                                (ArenaTypeId::INVALID, false, false)
                            }
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: type_name,
                                    field: field_name.to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            (ArenaTypeId::INVALID, false, false)
                        }
                    }
                    LegacyType::Nominal(NominalType::Record(r)) => {
                        // Records are immutable - reject field assignment
                        let type_def = self.entity_registry.get_type(r.type_def_id);
                        self.add_error(
                            SemanticError::RecordFieldMutation {
                                record: self
                                    .name_table
                                    .last_segment_str(type_def.name_id)
                                    .unwrap_or_else(|| "record".to_string()),
                                field: interner.resolve(*field).to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                        (ArenaTypeId::INVALID, false, false)
                    }
                    _ => {
                        if !obj_ty_id.is_invalid() {
                            let ty = self.type_display(&obj_ty);
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty,
                                    field: interner.resolve(*field).to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                        }
                        (ArenaTypeId::INVALID, false, false)
                    }
                }
            }
            AssignTarget::Index { object, index } => {
                // Type-check object as array
                let obj_type_id = self.check_expr(object, interner)?;
                let idx_type_id = self.check_expr(index, interner)?;

                // Check index is integer using TypeId
                if !self.is_integer_id(idx_type_id) {
                    let found = self.type_display_id(idx_type_id);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found,
                            span: index.span.into(),
                        },
                        index.span,
                    );
                }

                // Get element type using TypeId
                if let Some(elem_id) = self.unwrap_array_id(obj_type_id) {
                    (elem_id, true, true)
                } else if let Some((elem_id, _)) = self.unwrap_fixed_array_id(obj_type_id) {
                    (elem_id, true, true)
                } else {
                    if !obj_type_id.is_invalid() {
                        let found = self.type_display_id(obj_type_id);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "array".to_string(),
                                found,
                                span: object.span.into(),
                            },
                            object.span,
                        );
                    }
                    (ArenaTypeId::INVALID, false, false)
                }
            }
        };

        // Now check the value expression with expected type context
        let expected_ty = if target_valid && !target_ty_id.is_invalid() {
            Some(self.id_to_type(target_ty_id))
        } else {
            None
        };
        let value_ty = self.check_expr_expecting(&assign.value, expected_ty.as_ref(), interner)?;

        // Handle mutability and capture checks for variable targets
        if let AssignTarget::Variable(sym) = &assign.target
            && target_valid
        {
            // Check if this is a mutation of a captured variable
            if self.in_lambda() && !self.is_lambda_local(*sym) {
                // Record as capture and mark as mutated
                self.record_capture(*sym, is_mutable);
                self.mark_capture_mutated(*sym);
            }

            if !is_mutable {
                let name = interner.resolve(*sym);
                self.add_error(
                    SemanticError::ImmutableAssignment {
                        name: name.to_string(),
                        span: expr.span.into(),
                        declaration: expr.span.into(), // TODO: track declaration span
                    },
                    expr.span,
                );
            }
        }

        // Check type compatibility
        if target_valid {
            let value_ty_id = self.type_to_id(&value_ty);
            if !self.types_compatible_id(value_ty_id, target_ty_id, interner) {
                self.add_type_mismatch_id(target_ty_id, value_ty_id, assign.value.span);
            }
        }

        Ok(target_ty_id)
    }

    pub(super) fn check_compound_assign_expr(
        &mut self,
        expr: &Expr,
        compound: &CompoundAssignExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Get target type and check mutability
        let target_type_id = match &compound.target {
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    let is_mutable = var.mutable;
                    let var_ty = var.ty;

                    // Check if this is a mutation of a captured variable
                    if self.in_lambda() && !self.is_lambda_local(*sym) {
                        self.record_capture(*sym, is_mutable);
                        self.mark_capture_mutated(*sym);
                    }

                    if !is_mutable {
                        let name = interner.resolve(*sym);
                        self.add_error(
                            SemanticError::ImmutableAssignment {
                                name: name.to_string(),
                                span: expr.span.into(),
                                declaration: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                    var_ty
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(ArenaTypeId::INVALID);
                }
            }
            AssignTarget::Index { object, index } => {
                // Type-check object as array using TypeId
                let obj_type_id = self.check_expr(object, interner)?;
                let idx_type_id = self.check_expr(index, interner)?;

                // Check index is integer using TypeId
                if !self.is_integer_id(idx_type_id) {
                    let found = self.type_display_id(idx_type_id);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found,
                            span: index.span.into(),
                        },
                        index.span,
                    );
                }

                // Get element type using TypeId
                if let Some(elem_id) = self.unwrap_array_id(obj_type_id) {
                    elem_id
                } else if let Some((elem_id, _)) = self.unwrap_fixed_array_id(obj_type_id) {
                    elem_id
                } else {
                    if !obj_type_id.is_invalid() {
                        let found = self.type_display_id(obj_type_id);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "array".to_string(),
                                found,
                                span: object.span.into(),
                            },
                            object.span,
                        );
                    }
                    ArenaTypeId::INVALID
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty_id = self.check_expr(object, interner)?;
                let obj_ty = self.id_to_type(obj_ty_id);
                let field_name = interner.resolve(*field);

                match &obj_ty {
                    LegacyType::Nominal(NominalType::Class(c)) => {
                        // Look up field via EntityRegistry
                        let type_def = self.entity_registry.get_type(c.type_def_id);
                        let type_name = self
                            .name_table
                            .last_segment_str(type_def.name_id)
                            .unwrap_or_else(|| "class".to_string());

                        if let Some(ref generic_info) = type_def.generic_info {
                            if let Some(idx) = generic_info.field_names.iter().position(|name_id| {
                                self.name_table.last_segment_str(*name_id).as_deref()
                                    == Some(field_name)
                            }) {
                                // Substitute type args via arena if any
                                let field_type_id = generic_info.field_types[idx];
                                if c.type_args.is_empty() {
                                    field_type_id
                                } else {
                                    let mut arena = self.type_arena.borrow_mut();
                                    let subs_id: hashbrown::HashMap<_, _> = generic_info
                                        .type_params
                                        .iter()
                                        .zip(c.type_args.iter())
                                        .map(|(tp, arg)| (tp.name_id, arena.from_type(arg)))
                                        .collect();
                                    arena.substitute(field_type_id, &subs_id)
                                }
                            } else {
                                self.add_error(
                                    SemanticError::UnknownField {
                                        ty: type_name,
                                        field: field_name.to_string(),
                                        span: (*field_span).into(),
                                    },
                                    *field_span,
                                );
                                ArenaTypeId::INVALID
                            }
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: type_name,
                                    field: field_name.to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            ArenaTypeId::INVALID
                        }
                    }
                    LegacyType::Nominal(NominalType::Record(r)) => {
                        // Records are immutable - reject field assignment
                        let type_def = self.entity_registry.get_type(r.type_def_id);
                        self.add_error(
                            SemanticError::RecordFieldMutation {
                                record: self
                                    .name_table
                                    .last_segment_str(type_def.name_id)
                                    .unwrap_or_else(|| "record".to_string()),
                                field: field_name.to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                        ArenaTypeId::INVALID
                    }
                    _ => {
                        if !obj_ty_id.is_invalid() {
                            let ty = self.type_display(&obj_ty);
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty,
                                    field: interner.resolve(*field).to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                        }
                        ArenaTypeId::INVALID
                    }
                }
            }
        };

        // Type-check the value expression with expected type context
        let expected = if !target_type_id.is_invalid() {
            Some(self.id_to_type(target_type_id))
        } else {
            None
        };
        let value_type = self.check_expr_expecting(&compound.value, expected.as_ref(), interner)?;
        let value_type_id = self.type_to_id(&value_type);

        // Check operator compatibility - compound assignment operators are arithmetic
        // For +=, -=, *=, /=, %= both operands must be numeric
        if !target_type_id.is_invalid()
            && !value_type_id.is_invalid()
            && (!target_type_id.is_numeric() || !value_type_id.is_numeric())
        {
            let found = self.type_display_pair_id(target_type_id, value_type_id);
            self.add_error(
                SemanticError::TypeMismatch {
                    expected: "numeric".to_string(),
                    found,
                    span: expr.span.into(),
                },
                expr.span,
            );
        }

        Ok(target_type_id)
    }
}
