use super::super::*;

impl Analyzer {
    pub(crate) fn check_expr(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let ty = self.check_expr_inner(expr, interner)?;
        self.record_expr_type(expr, ty.clone());
        tracing::trace!(
            line = expr.span.line,
            inferred_type = %self.type_display(&ty),
            "type inferred"
        );
        Ok(ty)
    }

    fn check_expr_inner(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(_) => Ok(Type::I64), // Default to i64 for now
            ExprKind::FloatLiteral(_) => Ok(Type::F64),
            ExprKind::BoolLiteral(_) => Ok(Type::Bool),
            ExprKind::StringLiteral(_) => Ok(Type::String),
            ExprKind::InterpolatedString(_) => Ok(Type::String),
            ExprKind::TypeLiteral(_) => Ok(Type::Type), // Type values have metatype `type`

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
                    return Ok(Type::Error);
                }

                // Use get_variable_type to respect flow-sensitive narrowing
                if let Some(ty) = self.get_variable_type(*sym) {
                    // Check if this is a capture (inside lambda, not a local)
                    if self.in_lambda() && !self.is_lambda_local(*sym) {
                        // Look up variable info to get mutability
                        if let Some(var) = self.scope.get(*sym) {
                            self.record_capture(*sym, var.mutable);
                        }
                    }
                    Ok(ty)
                } else if let Some(func_type) = self.get_function_type(*sym, interner) {
                    // Identifier refers to a function - treat it as a function value
                    Ok(Type::Function(func_type))
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

            ExprKind::Binary(bin) => {
                let left_ty = self.check_expr(&bin.left, interner)?;
                let right_ty = self.check_expr(&bin.right, interner)?;

                match bin.op {
                    BinaryOp::Add => {
                        // Handle string concatenation: string + Stringable
                        if matches!(left_ty, Type::String) {
                            // Left is string - check if right implements Stringable
                            if matches!(right_ty, Type::String) {
                                // string + string is always valid
                                Ok(Type::String)
                            } else if self.satisfies_stringable(&right_ty, interner) {
                                // Right implements Stringable, so string + X is valid
                                Ok(Type::String)
                            } else {
                                // Right doesn't implement Stringable
                                self.type_error("Stringable", &right_ty, bin.right.span);
                                Ok(Type::Error)
                            }
                        } else if left_ty.is_numeric() && right_ty.is_numeric() {
                            // Numeric addition
                            if left_ty == Type::F64 || right_ty == Type::F64 {
                                Ok(Type::F64)
                            } else if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.type_error_pair(
                                "numeric or string",
                                &left_ty,
                                &right_ty,
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // Return wider type
                            if left_ty == Type::F64 || right_ty == Type::F64 {
                                Ok(Type::F64)
                            } else if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.type_error_pair("numeric", &left_ty, &right_ty, expr.span);
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Le
                    | BinaryOp::Ge => Ok(Type::Bool),
                    BinaryOp::And | BinaryOp::Or => {
                        if left_ty == Type::Bool && right_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.type_error_pair("bool", &left_ty, &right_ty, expr.span);
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
                        if left_ty.is_integer() && right_ty.is_integer() {
                            if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.type_error_pair("integer", &left_ty, &right_ty, expr.span);
                            Ok(Type::Error)
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
                            self.type_error("numeric", &operand_ty, expr.span);
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => {
                        if operand_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.type_error("bool", &operand_ty, expr.span);
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.type_error("integer", &operand_ty, expr.span);
                            Ok(Type::Error)
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
                    // Empty array needs type annotation or we use Unknown
                    Ok(Type::Array(Box::new(Type::Unknown)))
                } else {
                    // Infer types for all elements
                    let elem_types: Vec<Type> = elements
                        .iter()
                        .map(|e| self.check_expr(e, interner))
                        .collect::<Result<Vec<_>, _>>()?;

                    // Check if all elements have compatible types (homogeneous → Array)
                    // or different types (heterogeneous → Tuple)
                    let first_ty = &elem_types[0];
                    let is_homogeneous = elem_types
                        .iter()
                        .skip(1)
                        .all(|ty| self.types_compatible(ty, first_ty, interner));

                    if is_homogeneous {
                        // All same type → dynamic array
                        Ok(Type::Array(Box::new(first_ty.clone())))
                    } else {
                        // Different types → tuple
                        Ok(Type::Tuple(elem_types))
                    }
                }
            }

            ExprKind::RepeatLiteral { element, count } => {
                // [expr; N] creates a fixed-size array
                let elem_ty = self.check_expr(element, interner)?;
                Ok(Type::FixedArray {
                    element: Box::new(elem_ty),
                    size: *count,
                })
            }

            ExprKind::Index(idx) => {
                let obj_ty = self.check_expr(&idx.object, interner)?;
                let index_ty = self.check_expr(&idx.index, interner)?;

                // Index must be integer
                if !index_ty.is_integer() {
                    self.type_error("integer", &index_ty, idx.index.span);
                }

                // Object must be array, tuple, or fixed array
                match obj_ty {
                    Type::Array(elem_ty) => Ok(*elem_ty),
                    Type::Tuple(ref elements) => {
                        // For tuples, try to get element type from constant index
                        if let ExprKind::IntLiteral(i) = &idx.index.kind {
                            let i = *i as usize;
                            if i < elements.len() {
                                Ok(elements[i].clone())
                            } else {
                                self.add_error(
                                    SemanticError::IndexOutOfBounds {
                                        index: i,
                                        len: elements.len(),
                                        span: idx.index.span.into(),
                                    },
                                    idx.index.span,
                                );
                                Ok(Type::Error)
                            }
                        } else {
                            // Non-constant index - return union of all element types
                            // For now, just return first element type (common case: 2-tuples)
                            Ok(elements.first().cloned().unwrap_or(Type::Unknown))
                        }
                    }
                    Type::FixedArray { element, .. } => Ok(*element),
                    _ => {
                        self.type_error("array", &obj_ty, idx.object.span);
                        Ok(Type::Error)
                    }
                }
            }

            ExprKind::Range(range) => {
                let start_ty = self.check_expr(&range.start, interner)?;
                let end_ty = self.check_expr(&range.end, interner)?;

                if !start_ty.is_integer() || !end_ty.is_integer() {
                    self.type_error_pair("integer", &start_ty, &end_ty, expr.span);
                }
                Ok(Type::Range)
            }

            ExprKind::Match(match_expr) => self.check_match_expr(match_expr, interner),

            ExprKind::Nil => Ok(Type::Nil),

            ExprKind::Done => Ok(Type::Done),

            ExprKind::NullCoalesce(nc) => {
                let value_type = self.check_expr(&nc.value, interner)?;

                // Value must be an optional (union containing Nil)
                if !value_type.is_optional() {
                    let found = self.type_display(&value_type);
                    self.add_error(
                        SemanticError::NullCoalesceNotOptional {
                            found,
                            span: nc.value.span.into(),
                        },
                        nc.value.span,
                    );
                    return Ok(Type::Error);
                }

                // Get the non-nil type
                let unwrapped = value_type.unwrap_optional().unwrap_or(Type::Error);

                // Default must match the unwrapped type
                let _default_type =
                    self.check_expr_expecting(&nc.default, Some(&unwrapped), interner)?;

                // Result is the non-nil type
                Ok(unwrapped)
            }

            ExprKind::Is(is_expr) => {
                let value_type = self.check_expr(&is_expr.value, interner)?;
                let tested_type = self.resolve_type(&is_expr.type_expr, interner);

                // Warn/error if tested type is not a variant of value's union
                if let Type::Union(variants) = &value_type
                    && !variants.contains(&tested_type)
                {
                    let tested = self.type_display(&tested_type);
                    let union_type = self.type_display(&value_type);
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
                Ok(Type::Bool)
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

            ExprKind::Try(inner) => self.analyze_try(inner, interner),

            ExprKind::Import(path) => self
                .analyze_module(path, expr.span, interner)
                .map_err(|_| self.errors.clone()),

            ExprKind::Yield(yield_expr) => {
                // Check if we're inside a function at all
                if self.current_function_return.is_none() {
                    self.add_error(
                        SemanticError::YieldOutsideGenerator {
                            span: yield_expr.span.into(),
                        },
                        yield_expr.span,
                    );
                    return Ok(Type::Void);
                }

                // Check if we're inside a generator function (Iterator<T> return type)
                let Some(element_type) = self.current_generator_element_type.clone() else {
                    // Not a generator - report error with actual return type
                    let return_type = self.current_function_return.clone().unwrap();
                    let found = self.type_display(&return_type);
                    self.add_error(
                        SemanticError::YieldInNonGenerator {
                            found,
                            span: yield_expr.span.into(),
                        },
                        yield_expr.span,
                    );
                    return Ok(Type::Void);
                };

                // Type check the yield expression against the Iterator element type
                let yield_type =
                    self.check_expr_expecting(&yield_expr.value, Some(&element_type), interner)?;

                // Check type compatibility
                if !self.types_compatible(&yield_type, &element_type, interner) {
                    let expected = self.type_display(&element_type);
                    let found = self.type_display(&yield_type);
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
                Ok(Type::Void)
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
                    Ok(Type::Void)
                }
            }

            ExprKind::If(if_expr) => {
                // Type check the condition (must be bool)
                let cond_ty = self.check_expr(&if_expr.condition, interner)?;
                if cond_ty != Type::Bool {
                    self.type_error("bool", &cond_ty, if_expr.condition.span);
                }

                // Type check then branch
                let then_ty = self.check_expr(&if_expr.then_branch, interner)?;

                // If expression requires else branch
                let Some(else_branch) = &if_expr.else_branch else {
                    self.add_error(
                        SemanticError::IfExprMissingElse {
                            span: if_expr.span.into(),
                        },
                        if_expr.span,
                    );
                    return Ok(Type::Error);
                };

                let else_ty = self.check_expr(else_branch, interner)?;

                // Both branches must have compatible types
                if !self.types_compatible(&then_ty, &else_ty, interner) {
                    let expected = self.type_display(&then_ty);
                    let found = self.type_display(&else_ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found,
                            span: else_branch.span.into(),
                        },
                        else_branch.span,
                    );
                    Ok(Type::Error)
                } else {
                    Ok(then_ty)
                }
            }
        }
    }
}
