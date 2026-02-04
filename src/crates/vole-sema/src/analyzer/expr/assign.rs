use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;

impl Analyzer {
    pub(super) fn check_assign_expr(
        &mut self,
        expr: &Expr,
        assign: &AssignExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // First, determine the expected type from the target (bidirectional type checking)
        let (target_ty_id, is_mutable, declaration_span, target_valid) = match &assign.target {
            AssignTarget::Discard => {
                // Discard pattern: _ = expr
                // Just type-check the RHS for errors, then return VOID
                let _value_ty_id = self.check_expr(&assign.value, interner)?;
                return Ok(ArenaTypeId::VOID);
            }
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    (var.ty, var.mutable, Some(var.declaration_span), true)
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    (ArenaTypeId::INVALID, false, None, false)
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty_id = self.check_expr(object, interner)?;
                let field_name = interner.resolve(*field);

                let struct_info = {
                    let arena = self.type_arena();
                    arena
                        .unwrap_nominal(obj_ty_id)
                        .filter(|(_, _, kind)| kind.is_class_or_struct())
                        .map(|(id, args, _kind)| (id, args.clone()))
                };

                if let Some((type_def_id, type_args_id)) = struct_info {
                    let name_id = self.entity_registry().name_id(type_def_id);
                    let generic_info = self.entity_registry().type_generic_info(type_def_id);
                    let type_name = self
                        .name_table()
                        .last_segment_str(name_id)
                        .unwrap_or_else(|| "class".to_string());

                    if let Some(ref generic_info) = generic_info {
                        if let Some(idx) = generic_info.field_names.iter().position(|name_id| {
                            self.name_table().last_segment_str(*name_id).as_deref()
                                == Some(field_name)
                        }) {
                            // Substitute type args via arena if any
                            let field_type_id = generic_info.field_types[idx];
                            let resolved_type_id = if type_args_id.is_empty() {
                                field_type_id
                            } else {
                                // Use type_args_id directly (already TypeIds)
                                let subs_id: FxHashMap<_, _> = generic_info
                                    .type_params
                                    .iter()
                                    .zip(type_args_id.iter())
                                    .map(|(tp, &type_id)| (tp.name_id, type_id))
                                    .collect();
                                self.type_arena_mut().substitute(field_type_id, &subs_id)
                            };
                            (resolved_type_id, true, None, true)
                        } else {
                            self.add_error(
                                SemanticError::UnknownField {
                                    ty: type_name,
                                    field: field_name.to_string(),
                                    span: (*field_span).into(),
                                },
                                *field_span,
                            );
                            (ArenaTypeId::INVALID, false, None, false)
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
                        (ArenaTypeId::INVALID, false, None, false)
                    }
                } else {
                    if !obj_ty_id.is_invalid() {
                        let ty = self.type_display_id(obj_ty_id);
                        self.add_error(
                            SemanticError::UnknownField {
                                ty,
                                field: field_name.to_string(),
                                span: (*field_span).into(),
                            },
                            *field_span,
                        );
                    }
                    (ArenaTypeId::INVALID, false, None, false)
                }
            }
            AssignTarget::Index { object, index } => {
                // Type-check object as array
                let obj_type_id = self.check_expr(object, interner)?;
                let idx_type_id = self.check_expr(index, interner)?;

                // Check index is integer using TypeId
                // Skip if index type is INVALID (prior error)
                if !idx_type_id.is_invalid() && !self.is_integer_id(idx_type_id) {
                    self.type_error_id("integer", idx_type_id, index.span);
                }

                // Get element type using TypeId
                if let Some(elem_id) = self.unwrap_indexable_element_id(obj_type_id) {
                    (elem_id, true, None, true)
                } else {
                    // obj_type_id check already in type_error_id helper
                    self.type_error_id("array", obj_type_id, object.span);
                    (ArenaTypeId::INVALID, false, None, false)
                }
            }
        };

        // Now check the value expression with expected type context (using TypeId version)
        let expected_ty_id = if target_valid && !target_ty_id.is_invalid() {
            Some(target_ty_id)
        } else {
            None
        };
        let value_ty_id = self.check_expr_expecting_id(&assign.value, expected_ty_id, interner)?;

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
                // Use the stored declaration span if available, otherwise fall back to expr span
                let decl_span = declaration_span.unwrap_or(expr.span);
                self.add_error(
                    SemanticError::ImmutableAssignment {
                        name: name.to_string(),
                        span: expr.span.into(),
                        declaration: decl_span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check type compatibility
        if target_valid && !self.types_compatible_id(value_ty_id, target_ty_id, interner) {
            self.add_type_mismatch_id(target_ty_id, value_ty_id, assign.value.span);
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
            AssignTarget::Discard => {
                // Compound assignment to discard is invalid - you can't read from _
                self.add_error(
                    SemanticError::UndefinedVariable {
                        name: "_".to_string(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
                return Ok(ArenaTypeId::INVALID);
            }
            AssignTarget::Variable(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    let is_mutable = var.mutable;
                    let var_ty = var.ty;
                    let decl_span = var.declaration_span;

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
                                declaration: decl_span.into(),
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
                // Skip if index type is INVALID (prior error)
                if !idx_type_id.is_invalid() && !self.is_integer_id(idx_type_id) {
                    self.type_error_id("integer", idx_type_id, index.span);
                }

                // Get element type using TypeId
                if let Some(elem_id) = self.unwrap_indexable_element_id(obj_type_id) {
                    elem_id
                } else {
                    // obj_type_id check already in type_error_id helper
                    self.type_error_id("array", obj_type_id, object.span);
                    ArenaTypeId::INVALID
                }
            }
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => {
                let obj_ty_id = self.check_expr(object, interner)?;
                let field_name = interner.resolve(*field);

                let struct_info = {
                    let arena = self.type_arena();
                    arena
                        .unwrap_nominal(obj_ty_id)
                        .filter(|(_, _, kind)| kind.is_class_or_struct())
                        .map(|(id, args, _kind)| (id, args.clone()))
                };

                if let Some((type_def_id, type_args_id)) = struct_info {
                    let name_id = self.entity_registry().name_id(type_def_id);
                    let generic_info = self.entity_registry().type_generic_info(type_def_id);
                    let type_name = self
                        .name_table()
                        .last_segment_str(name_id)
                        .unwrap_or_else(|| "class".to_string());

                    if let Some(ref generic_info) = generic_info {
                        if let Some(idx) = generic_info.field_names.iter().position(|name_id| {
                            self.name_table().last_segment_str(*name_id).as_deref()
                                == Some(field_name)
                        }) {
                            // Substitute type args via arena if any
                            let field_type_id = generic_info.field_types[idx];
                            if type_args_id.is_empty() {
                                field_type_id
                            } else {
                                // Use type_args_id directly (already TypeIds)
                                let subs_id: FxHashMap<_, _> = generic_info
                                    .type_params
                                    .iter()
                                    .zip(type_args_id.iter())
                                    .map(|(tp, &type_id)| (tp.name_id, type_id))
                                    .collect();
                                self.type_arena_mut().substitute(field_type_id, &subs_id)
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
                } else {
                    if !obj_ty_id.is_invalid() {
                        let ty = self.type_display_id(obj_ty_id);
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
        };

        // Type-check the value expression with expected type context (using TypeId version)
        let expected_id = if !target_type_id.is_invalid() {
            Some(target_type_id)
        } else {
            None
        };
        let value_type_id = self.check_expr_expecting_id(&compound.value, expected_id, interner)?;

        // Check operator compatibility - compound assignment operators are arithmetic
        // For +=, -=, *=, /=, %= both operands must be numeric
        // type_error_pair_id handles INVALID check internally
        if !target_type_id.is_numeric() || !value_type_id.is_numeric() {
            self.type_error_pair_id("numeric", target_type_id, value_type_id, expr.span);
        }

        Ok(target_type_id)
    }
}
