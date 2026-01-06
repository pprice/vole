use super::super::*;

impl Analyzer {
    pub(super) fn check_assign_expr(
        &mut self,
        expr: &Expr,
        assign: &AssignExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let value_ty = self.check_expr(&assign.value, interner)?;

        match &assign.target {
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    let is_mutable = var.mutable;
                    let var_ty = var.ty.clone();

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
                    if !self.types_compatible(&value_ty, &var_ty, interner) {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: var_ty.name().to_string(),
                                found: value_ty.name().to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                    Ok(var_ty)
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::Error)
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty = self.check_expr(object, interner)?;

                match &obj_ty {
                    Type::Class(c) => {
                        if let Some(field_def) = c.fields.iter().find(|f| f.name == *field) {
                            if !self.types_compatible(&value_ty, &field_def.ty, interner) {
                                self.add_error(
                                    SemanticError::TypeMismatch {
                                        expected: field_def.ty.name().to_string(),
                                        found: value_ty.name().to_string(),
                                        span: assign.value.span.into(),
                                    },
                                    assign.value.span,
                                );
                            }
                            Ok(field_def.ty.clone())
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: interner.resolve(c.name).to_string(),
                                    field: interner.resolve(*field).to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    Type::Record(r) => {
                        // Records are immutable - reject field assignment
                        self.add_error(
                            SemanticError::RecordFieldMutation {
                                record: interner.resolve(r.name).to_string(),
                                field: interner.resolve(*field).to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                        Ok(Type::Error)
                    }
                    _ => {
                        if obj_ty != Type::Error {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: obj_ty.name().to_string(),
                                    field: interner.resolve(*field).to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                        }
                        Ok(Type::Error)
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
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: idx_type.name().to_string(),
                            span: index.span.into(),
                        },
                        index.span,
                    );
                }

                // Get element type and check assignment compatibility
                match obj_type {
                    Type::Array(elem_ty) => {
                        if !self.types_compatible(&value_ty, &elem_ty, interner) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: elem_ty.name().to_string(),
                                    found: value_ty.name().to_string(),
                                    span: assign.value.span.into(),
                                },
                                assign.value.span,
                            );
                        }
                        Ok(*elem_ty)
                    }
                    _ => {
                        if obj_type != Type::Error {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "array".to_string(),
                                    found: obj_type.name().to_string(),
                                    span: object.span.into(),
                                },
                                object.span,
                            );
                        }
                        Ok(Type::Error)
                    }
                }
            }
        }
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
                    return Ok(Type::Error);
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
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: idx_type.name().to_string(),
                            span: index.span.into(),
                        },
                        index.span,
                    );
                }

                // Get element type
                match obj_type {
                    Type::Array(elem_ty) => *elem_ty,
                    _ => {
                        if obj_type != Type::Error {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "array".to_string(),
                                    found: obj_type.name().to_string(),
                                    span: object.span.into(),
                                },
                                object.span,
                            );
                        }
                        Type::Error
                    }
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty = self.check_expr(object, interner)?;

                match &obj_ty {
                    Type::Class(c) => {
                        if let Some(field_def) = c.fields.iter().find(|f| f.name == *field) {
                            field_def.ty.clone()
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: interner.resolve(c.name).to_string(),
                                    field: interner.resolve(*field).to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            Type::Error
                        }
                    }
                    Type::Record(r) => {
                        // Records are immutable - reject field assignment
                        self.add_error(
                            SemanticError::RecordFieldMutation {
                                record: interner.resolve(r.name).to_string(),
                                field: interner.resolve(*field).to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                        Type::Error
                    }
                    _ => {
                        if obj_ty != Type::Error {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: obj_ty.name().to_string(),
                                    field: interner.resolve(*field).to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                        }
                        Type::Error
                    }
                }
            }
        };

        // Type-check the value expression
        let value_type = self.check_expr(&compound.value, interner)?;

        // Check operator compatibility - compound assignment operators are arithmetic
        // For +=, -=, *=, /=, %= both operands must be numeric
        if target_type != Type::Error
            && value_type != Type::Error
            && (!target_type.is_numeric() || !value_type.is_numeric())
        {
            self.add_error(
                SemanticError::TypeMismatch {
                    expected: "numeric".to_string(),
                    found: format!("{} and {}", target_type.name(), value_type.name()),
                    span: expr.span.into(),
                },
                expr.span,
            );
        }

        Ok(target_type)
    }
}
