use super::super::*;

impl Analyzer {
    pub(super) fn check_assign_expr(
        &mut self,
        expr: &Expr,
        assign: &AssignExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // First, determine the expected type from the target (bidirectional type checking)
        let (target_ty, is_mutable, target_valid) = match &assign.target {
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    (var.ty.clone(), var.mutable, true)
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    (Type::invalid("propagate"), false, false)
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty = self.check_expr(object, interner)?;
                let field_name = interner.resolve(*field);

                match &obj_ty {
                    Type::Class(c) => {
                        if let Some(field_def) = c.fields.iter().find(|f| f.name == field_name) {
                            (field_def.ty.clone(), true, true)
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: self
                                        .name_table
                                        .last_segment_str(c.name_id)
                                        .unwrap_or_else(|| "class".to_string()),
                                    field: field_name.to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            (Type::invalid("propagate"), false, false)
                        }
                    }
                    Type::Record(r) => {
                        // Records are immutable - reject field assignment
                        self.add_error(
                            SemanticError::RecordFieldMutation {
                                record: self
                                    .name_table
                                    .last_segment_str(r.name_id)
                                    .unwrap_or_else(|| "record".to_string()),
                                field: interner.resolve(*field).to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                        (Type::invalid("propagate"), false, false)
                    }
                    _ => {
                        if !obj_ty.is_invalid() {
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
                        (Type::invalid("propagate"), false, false)
                    }
                }
            }
            AssignTarget::Index { object, index } => {
                // Type-check object as array
                let obj_type = self.check_expr(object, interner)?;
                let idx_type = self.check_expr(index, interner)?;

                // Check index is integer
                if !matches!(
                    idx_type,
                    Type::I32 | Type::I64 | Type::U8 | Type::U16 | Type::U32 | Type::U64
                ) {
                    let found = self.type_display(&idx_type);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found,
                            span: index.span.into(),
                        },
                        index.span,
                    );
                }

                // Get element type
                match obj_type {
                    Type::Array(elem_ty) => (*elem_ty, true, true),
                    Type::FixedArray { element, .. } => (*element, true, true),
                    _ => {
                        if !obj_type.is_invalid() {
                            let found = self.type_display(&obj_type);
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "array".to_string(),
                                    found,
                                    span: object.span.into(),
                                },
                                object.span,
                            );
                        }
                        (Type::invalid("propagate"), false, false)
                    }
                }
            }
        };

        // Now check the value expression with expected type context
        let expected_ty = if target_valid && !target_ty.is_invalid() {
            Some(&target_ty)
        } else {
            None
        };
        let value_ty = self.check_expr_expecting(&assign.value, expected_ty, interner)?;

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

        // Check type compatibility (for non-literal types that couldn't be inferred)
        if target_valid && !self.types_compatible(&value_ty, &target_ty, interner) {
            self.add_type_mismatch(&target_ty, &value_ty, assign.value.span);
        }

        Ok(target_ty)
    }

    pub(super) fn check_compound_assign_expr(
        &mut self,
        expr: &Expr,
        compound: &CompoundAssignExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // Get target type and check mutability
        let target_type = match &compound.target {
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    let is_mutable = var.mutable;
                    let var_ty = var.ty.clone();

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
                    return Ok(Type::invalid("propagate"));
                }
            }
            AssignTarget::Index { object, index } => {
                // Type-check object as array
                let obj_type = self.check_expr(object, interner)?;
                let idx_type = self.check_expr(index, interner)?;

                // Check index is integer
                if !matches!(
                    idx_type,
                    Type::I32 | Type::I64 | Type::U8 | Type::U16 | Type::U32 | Type::U64
                ) {
                    let found = self.type_display(&idx_type);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found,
                            span: index.span.into(),
                        },
                        index.span,
                    );
                }

                // Get element type
                match obj_type {
                    Type::Array(elem_ty) => *elem_ty,
                    Type::FixedArray { element, .. } => *element,
                    _ => {
                        if !obj_type.is_invalid() {
                            let found = self.type_display(&obj_type);
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "array".to_string(),
                                    found,
                                    span: object.span.into(),
                                },
                                object.span,
                            );
                        }
                        Type::invalid("propagate")
                    }
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty = self.check_expr(object, interner)?;
                let field_name = interner.resolve(*field);

                match &obj_ty {
                    Type::Class(c) => {
                        if let Some(field_def) = c.fields.iter().find(|f| f.name == field_name) {
                            field_def.ty.clone()
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: self
                                        .name_table
                                        .last_segment_str(c.name_id)
                                        .unwrap_or_else(|| "class".to_string()),
                                    field: field_name.to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            Type::invalid("propagate")
                        }
                    }
                    Type::Record(r) => {
                        // Records are immutable - reject field assignment
                        self.add_error(
                            SemanticError::RecordFieldMutation {
                                record: self
                                    .name_table
                                    .last_segment_str(r.name_id)
                                    .unwrap_or_else(|| "record".to_string()),
                                field: field_name.to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                        Type::invalid("propagate")
                    }
                    _ => {
                        if !obj_ty.is_invalid() {
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
                        Type::invalid("propagate")
                    }
                }
            }
        };

        // Type-check the value expression with expected type context
        let expected = if !target_type.is_invalid() {
            Some(&target_type)
        } else {
            None
        };
        let value_type = self.check_expr_expecting(&compound.value, expected, interner)?;

        // Check operator compatibility - compound assignment operators are arithmetic
        // For +=, -=, *=, /=, %= both operands must be numeric
        if !target_type.is_invalid()
            && !value_type.is_invalid()
            && (!target_type.is_numeric() || !value_type.is_numeric())
        {
            let found = self.type_display_pair(&target_type, &value_type);
            self.add_error(
                SemanticError::TypeMismatch {
                    expected: "numeric".to_string(),
                    found,
                    span: expr.span.into(),
                },
                expr.span,
            );
        }

        Ok(target_type)
    }
}
