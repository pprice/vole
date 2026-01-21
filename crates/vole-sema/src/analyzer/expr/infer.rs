use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use crate::types::PlaceholderKind;

impl Analyzer {
    /// Check expression and return TypeId.
    /// This is THE entry point for expression type checking.
    pub(crate) fn check_expr(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let type_id = self.check_expr_inner(expr, interner)?;
        tracing::trace!(
            line = expr.span.line,
            inferred_type = %self.type_display_id(type_id),
            "type inferred"
        );
        Ok(self.record_expr_type_id(expr, type_id))
    }

    fn check_expr_inner(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(_) => Ok(ArenaTypeId::I64), // Default to i64 for now
            ExprKind::FloatLiteral(_) => Ok(ArenaTypeId::F64),
            ExprKind::BoolLiteral(_) => Ok(ArenaTypeId::BOOL),
            ExprKind::StringLiteral(_) => Ok(ArenaTypeId::STRING),
            ExprKind::InterpolatedString(_) => Ok(ArenaTypeId::STRING),
            ExprKind::TypeLiteral(_) => Ok(ArenaTypeId::METATYPE), // Type values have metatype `type`

            ExprKind::Identifier(sym) => {
                // Check for 'self' usage in static method
                let name_str = interner.resolve(*sym);
                if name_str == "self"
                    && let Some(ref method_name) = self.current_static_method
                {
                    self.add_error(
                        SemanticError::SelfInStaticMethod {
                            method: method_name.clone(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(ArenaTypeId::INVALID);
                }

                // Use get_variable_type to respect flow-sensitive narrowing
                if let Some(ty_id) = self.get_variable_type_id(*sym) {
                    // Check if this is a capture (inside lambda, not a local)
                    if self.in_lambda() && !self.is_lambda_local(*sym) {
                        // Look up variable info to get mutability
                        if let Some(var) = self.scope.get(*sym) {
                            self.record_capture(*sym, var.mutable);
                        }
                    }
                    Ok(ty_id)
                } else if let Some(func_type) = self.get_function_type(*sym, interner) {
                    // Identifier refers to a function - treat it as a function value
                    // Use the pre-interned TypeId fields from FunctionType
                    let params_id = &func_type.params_id;
                    let return_id = func_type.return_type_id;
                    Ok(self.type_arena_mut().function(
                        params_id.clone(),
                        return_id,
                        func_type.is_closure,
                    ))
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(ArenaTypeId::INVALID)
                }
            }

            ExprKind::Binary(bin) => {
                let left_ty = self.check_expr(&bin.left, interner)?;
                let right_ty = self.check_expr(&bin.right, interner)?;

                match bin.op {
                    BinaryOp::Add => {
                        // Handle string concatenation: string + Stringable
                        if left_ty == ArenaTypeId::STRING {
                            // Left is string - check if right implements Stringable
                            if right_ty == ArenaTypeId::STRING {
                                // string + string is always valid
                                Ok(ArenaTypeId::STRING)
                            } else if self.satisfies_stringable_id(right_ty, interner) {
                                // Right implements Stringable, so string + X is valid
                                Ok(ArenaTypeId::STRING)
                            } else {
                                // Right doesn't implement Stringable
                                self.type_error_id("Stringable", right_ty, bin.right.span);
                                Ok(ArenaTypeId::INVALID)
                            }
                        } else if left_ty.is_numeric() && right_ty.is_numeric() {
                            // Numeric addition
                            if left_ty == ArenaTypeId::F64 || right_ty == ArenaTypeId::F64 {
                                Ok(ArenaTypeId::F64)
                            } else if left_ty == ArenaTypeId::I64 || right_ty == ArenaTypeId::I64 {
                                Ok(ArenaTypeId::I64)
                            } else {
                                Ok(ArenaTypeId::I32)
                            }
                        } else {
                            self.type_error_pair_id(
                                "numeric or string",
                                left_ty,
                                right_ty,
                                expr.span,
                            );
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                    BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // Return wider type
                            if left_ty == ArenaTypeId::F64 || right_ty == ArenaTypeId::F64 {
                                Ok(ArenaTypeId::F64)
                            } else if left_ty == ArenaTypeId::I64 || right_ty == ArenaTypeId::I64 {
                                Ok(ArenaTypeId::I64)
                            } else {
                                Ok(ArenaTypeId::I32)
                            }
                        } else {
                            self.type_error_pair_id("numeric", left_ty, right_ty, expr.span);
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Le
                    | BinaryOp::Ge => Ok(ArenaTypeId::BOOL),
                    BinaryOp::And | BinaryOp::Or => {
                        if left_ty == ArenaTypeId::BOOL && right_ty == ArenaTypeId::BOOL {
                            Ok(ArenaTypeId::BOOL)
                        } else {
                            self.type_error_pair_id("bool", left_ty, right_ty, expr.span);
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
                        if left_ty.is_integer() && right_ty.is_integer() {
                            if left_ty == ArenaTypeId::I64 || right_ty == ArenaTypeId::I64 {
                                Ok(ArenaTypeId::I64)
                            } else {
                                Ok(ArenaTypeId::I32)
                            }
                        } else {
                            self.type_error_pair_id("integer", left_ty, right_ty, expr.span);
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                }
            }

            ExprKind::Unary(un) => {
                let operand_ty = self.check_expr(&un.operand, interner)?;
                match un.op {
                    UnaryOp::Neg => {
                        if operand_ty.is_numeric() {
                            Ok(operand_ty)
                        } else {
                            self.type_error_id("numeric", operand_ty, expr.span);
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                    UnaryOp::Not => {
                        if operand_ty == ArenaTypeId::BOOL {
                            Ok(ArenaTypeId::BOOL)
                        } else {
                            self.type_error_id("bool", operand_ty, expr.span);
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                    UnaryOp::BitNot => {
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.type_error_id("integer", operand_ty, expr.span);
                            Ok(ArenaTypeId::INVALID)
                        }
                    }
                }
            }

            ExprKind::Call(call) => self.check_call_expr(expr, call, interner),

            ExprKind::Assign(assign) => self.check_assign_expr(expr, assign, interner),

            ExprKind::CompoundAssign(compound) => {
                self.check_compound_assign_expr(expr, compound, interner)
            }

            ExprKind::Grouping(inner) => self.check_expr(inner, interner),

            ExprKind::ArrayLiteral(elements) => {
                if elements.is_empty() {
                    // Empty array needs type annotation or we use unknown placeholder
                    let unknown_id = self
                        .type_arena_mut()
                        .placeholder(PlaceholderKind::Inference);
                    Ok(self.ty_array_id(unknown_id))
                } else {
                    // Infer types for all elements (TypeId-based)
                    let elem_type_ids: Vec<ArenaTypeId> = elements
                        .iter()
                        .map(|e| self.check_expr(e, interner))
                        .collect::<Result<Vec<_>, _>>()?;

                    // Check if all elements have compatible types (homogeneous → Array)
                    // or different types (heterogeneous → Tuple)
                    let first_ty_id = elem_type_ids[0];
                    let is_homogeneous = elem_type_ids
                        .iter()
                        .skip(1)
                        .all(|&ty_id| self.types_compatible_id(ty_id, first_ty_id, interner));

                    if is_homogeneous {
                        // All same type → dynamic array
                        Ok(self.ty_array_id(first_ty_id))
                    } else {
                        // Different types → tuple
                        Ok(self.ty_tuple_id(elem_type_ids))
                    }
                }
            }

            ExprKind::RepeatLiteral { element, count } => {
                // [expr; N] creates a fixed-size array
                let elem_ty_id = self.check_expr(element, interner)?;
                Ok(self.ty_fixed_array_id(elem_ty_id, *count))
            }

            ExprKind::Index(idx) => {
                let obj_ty_id = self.check_expr(&idx.object, interner)?;
                let index_ty_id = self.check_expr(&idx.index, interner)?;

                // Index must be integer (using TypeId check)
                if !self.is_integer_id(index_ty_id) {
                    self.type_error_id("integer", index_ty_id, idx.index.span);
                }

                // Object must be array, tuple, or fixed array
                // Use arena to inspect the TypeId
                if let Some(elem_id) = self.unwrap_array_id(obj_ty_id) {
                    Ok(elem_id)
                } else if let Some((elem_id, _)) = self.unwrap_fixed_array_id(obj_ty_id) {
                    Ok(elem_id)
                } else if let Some(elem_ids) = self.unwrap_tuple_id(obj_ty_id) {
                    // For tuples, try to get element type from constant index
                    if let ExprKind::IntLiteral(i) = &idx.index.kind {
                        let i = *i as usize;
                        if i < elem_ids.len() {
                            Ok(elem_ids[i])
                        } else {
                            self.add_error(
                                SemanticError::IndexOutOfBounds {
                                    index: i,
                                    len: elem_ids.len(),
                                    span: idx.index.span.into(),
                                },
                                idx.index.span,
                            );
                            Ok(ArenaTypeId::INVALID)
                        }
                    } else {
                        // Non-constant index - return first element type (common case: 2-tuples)
                        Ok(elem_ids.first().copied().unwrap_or(ArenaTypeId::INVALID))
                    }
                } else {
                    if !obj_ty_id.is_invalid() {
                        self.type_error_id("array", obj_ty_id, idx.object.span);
                    }
                    Ok(ArenaTypeId::INVALID)
                }
            }

            ExprKind::Range(range) => {
                let start_ty_id = self.check_expr(&range.start, interner)?;
                let end_ty_id = self.check_expr(&range.end, interner)?;

                if !self.is_integer_id(start_ty_id) || !self.is_integer_id(end_ty_id) {
                    self.type_error_pair_id("integer", start_ty_id, end_ty_id, expr.span);
                }
                Ok(ArenaTypeId::RANGE)
            }

            ExprKind::Match(match_expr) => self.check_match_expr(match_expr, interner),

            ExprKind::Nil => Ok(ArenaTypeId::NIL),

            ExprKind::Done => Ok(ArenaTypeId::DONE),

            ExprKind::NullCoalesce(nc) => {
                let value_type_id = self.check_expr(&nc.value, interner)?;

                // Value must be an optional (union containing Nil)
                if !self.is_optional_id(value_type_id) {
                    let found = self.type_display_id(value_type_id);
                    self.add_error(
                        SemanticError::NullCoalesceNotOptional {
                            found,
                            span: nc.value.span.into(),
                        },
                        nc.value.span,
                    );
                    return Ok(ArenaTypeId::INVALID);
                }

                // Get the non-nil type
                let unwrapped_id = self
                    .unwrap_optional_id(value_type_id)
                    .unwrap_or(ArenaTypeId::INVALID);

                // Default must match the unwrapped type (using TypeId version)
                let _default_type_id =
                    self.check_expr_expecting_id(&nc.default, Some(unwrapped_id), interner)?;

                // Result is the non-nil type
                Ok(unwrapped_id)
            }

            ExprKind::Is(is_expr) => {
                let tested_type_id = self.resolve_type_id(&is_expr.type_expr, interner);

                // For literals, use bidirectional type inference so `42 is i32` works
                // For non-literals, just check normally (no type coercion)
                let value_type_id = if is_expr.value.is_literal() {
                    // Try to infer literal's type from tested type (won't error on mismatch)
                    let inferred_id =
                        self.infer_literal_type_id(&is_expr.value, tested_type_id, interner);
                    // Record the inferred type so codegen uses it
                    self.record_expr_type_id(&is_expr.value, inferred_id);
                    inferred_id
                } else {
                    self.check_expr(&is_expr.value, interner)?
                };
                let union_variants = self.type_arena().unwrap_union(value_type_id).cloned();
                if let Some(variants) = union_variants
                    && !variants.contains(&tested_type_id)
                {
                    let tested = self.type_display_id(tested_type_id);
                    let union_type = self.type_display_id(value_type_id);
                    self.add_error(
                        SemanticError::IsNotVariant {
                            tested,
                            union_type,
                            span: is_expr.type_span.into(),
                        },
                        is_expr.type_span,
                    );
                }

                // Result is always bool
                Ok(ArenaTypeId::BOOL)
            }

            ExprKind::Lambda(lambda) => {
                // For now, analyze without expected type context
                // (Context will be passed when we have assignment/call context)
                Ok(self.analyze_lambda(lambda, None, interner))
            }

            ExprKind::StructLiteral(struct_lit) => {
                self.check_struct_literal_expr(expr, struct_lit, interner)
            }

            ExprKind::FieldAccess(field_access) => {
                self.check_field_access_expr(field_access, interner)
            }

            ExprKind::OptionalChain(opt_chain) => {
                self.check_optional_chain_expr(opt_chain, interner)
            }

            ExprKind::MethodCall(method_call) => {
                self.check_method_call_expr(expr, method_call, interner)
            }

            ExprKind::Try(inner) => {
                // analyze_try now returns TypeId directly
                self.analyze_try(inner, interner)
            }

            ExprKind::Import(path) => {
                // analyze_module returns TypeId directly
                self.analyze_module(path, expr.span, interner)
                    .map_err(|_| self.errors.clone())
            }

            ExprKind::Yield(yield_expr) => {
                // Check if we're inside a function at all
                if self.current_function_return.is_none() {
                    self.add_error(
                        SemanticError::YieldOutsideGenerator {
                            span: yield_expr.span.into(),
                        },
                        yield_expr.span,
                    );
                    return Ok(ArenaTypeId::VOID);
                }

                // Check if we're inside a generator function (Iterator<T> return type)
                let Some(element_type) = self.current_generator_element_type else {
                    // Not a generator - report error with actual return type
                    let return_type = self
                        .current_function_return
                        .expect("yield only valid inside function");
                    let found = self.type_display_id(return_type);
                    self.add_error(
                        SemanticError::YieldInNonGenerator {
                            found,
                            span: yield_expr.span.into(),
                        },
                        yield_expr.span,
                    );
                    return Ok(ArenaTypeId::VOID);
                };

                // Type check the yield expression against the Iterator element type (TypeId-based)
                let yield_type_id =
                    self.check_expr_expecting_id(&yield_expr.value, Some(element_type), interner)?;

                // Check type compatibility
                if !self.types_compatible_id(yield_type_id, element_type, interner) {
                    let expected = self.type_display_id(element_type);
                    let found = self.type_display_id(yield_type_id);
                    self.add_error(
                        SemanticError::YieldTypeMismatch {
                            expected,
                            found,
                            span: yield_expr.value.span.into(),
                        },
                        yield_expr.value.span,
                    );
                }

                // yield expression returns Void (its value is the yielded element, but
                // the expression itself doesn't produce a value in the control flow)
                Ok(ArenaTypeId::VOID)
            }

            ExprKind::Block(block) => {
                // Type check all statements
                for stmt in &block.stmts {
                    self.check_stmt(stmt, interner)?;
                }

                // Block evaluates to its trailing expression, if present
                if let Some(trailing) = &block.trailing_expr {
                    self.check_expr(trailing, interner)
                } else {
                    Ok(ArenaTypeId::VOID)
                }
            }

            ExprKind::If(if_expr) => {
                // Type check the condition (must be bool) using TypeId
                let cond_ty_id = self.check_expr(&if_expr.condition, interner)?;
                if !self.is_bool_id(cond_ty_id) {
                    self.type_error_id("bool", cond_ty_id, if_expr.condition.span);
                }

                // Type check then branch (TypeId-based)
                let then_ty_id = self.check_expr(&if_expr.then_branch, interner)?;

                // If expression requires else branch
                let Some(else_branch) = &if_expr.else_branch else {
                    self.add_error(
                        SemanticError::IfExprMissingElse {
                            span: if_expr.span.into(),
                        },
                        if_expr.span,
                    );
                    return Ok(ArenaTypeId::INVALID);
                };

                let else_ty_id = self.check_expr(else_branch, interner)?;

                // Both branches must have compatible types
                if !self.types_compatible_id(then_ty_id, else_ty_id, interner) {
                    self.add_type_mismatch_id(then_ty_id, else_ty_id, else_branch.span);
                    Ok(ArenaTypeId::INVALID)
                } else {
                    Ok(then_ty_id)
                }
            }
        }
    }

    /// Infer a literal's type from a type hint for bidirectional type inference.
    /// Takes a TypeId hint and returns the hint if the literal can be that type,
    /// otherwise returns the default type for the literal.
    pub(crate) fn infer_literal_type_id(
        &mut self,
        expr: &Expr,
        hint: ArenaTypeId,
        _interner: &Interner,
    ) -> ArenaTypeId {
        match &expr.kind {
            ExprKind::IntLiteral(value) => {
                // Use TypeArena's literal_fits_id which handles primitives and unions
                if self.type_arena().literal_fits_id(*value, hint) {
                    hint
                } else {
                    self.ty_i64_id() // Default
                }
            }
            ExprKind::FloatLiteral(_) => {
                if hint == ArenaTypeId::F32 || hint == ArenaTypeId::F64 {
                    hint
                } else {
                    self.ty_f64_id() // Default
                }
            }
            // Bool, String, and Nil have only one possible type
            ExprKind::BoolLiteral(_) => self.ty_bool_id(),
            ExprKind::StringLiteral(_) => self.ty_string_id(),
            ExprKind::Nil => self.ty_nil_id(),
            // Not a literal - this shouldn't happen if is_literal() was checked
            _ => self.ty_invalid_traced_id("fallback"),
        }
    }
}
