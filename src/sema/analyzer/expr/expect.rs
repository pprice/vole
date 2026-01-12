use super::super::*;

impl Analyzer {
    /// Check expression against an expected type (bidirectional type checking)
    /// If expected is None, falls back to inference mode.
    pub(crate) fn check_expr_expecting(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let ty = self.check_expr_expecting_inner(expr, expected, interner)?;
        Ok(self.record_expr_type(expr, ty))
    }

    fn check_expr_expecting_inner(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(value) => match expected {
                // Integer literals can be assigned to unions containing a matching integer type
                // Return the concrete type, not the union, so codegen properly constructs the union
                Some(Type::Union(variants)) => {
                    if let Some(int_variant) = variants
                        .iter()
                        .find(|v| v.is_integer() && literal_fits(*value, v))
                    {
                        Ok(int_variant.clone())
                    } else {
                        let expected = self.type_display(&Type::Union(variants.clone()));
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected,
                                found: "integer literal".to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::I64) // Return a sensible default
                    }
                }
                Some(ty) if literal_fits(*value, ty) => Ok(ty.clone()),
                Some(ty) => {
                    let expected = self.type_display(ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found: "integer literal".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(ty.clone())
                }
                None => Ok(Type::I64),
            },
            ExprKind::TypeLiteral(_) => match expected {
                Some(Type::Type) | None => Ok(Type::Type),
                Some(ty) => {
                    let expected = self.type_display(ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found: "type".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::Type)
                }
            },
            ExprKind::FloatLiteral(_) => match expected {
                Some(ty) if ty == &Type::F64 => Ok(Type::F64),
                Some(ty) if ty.is_numeric() => Ok(ty.clone()),
                // Float literals can be assigned to unions containing f64
                Some(Type::Union(variants)) if variants.contains(&Type::F64) => Ok(Type::F64),
                Some(ty) => {
                    let expected = self.type_display(ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found: "f64".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::F64)
                }
                None => Ok(Type::F64),
            },
            ExprKind::Binary(bin) => match bin.op {
                // Add handles both numeric addition and string concatenation
                BinaryOp::Add => {
                    let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                    let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                    // Handle string concatenation: string + Stringable
                    if matches!(left_ty, Type::String) {
                        if matches!(right_ty, Type::String) {
                            // string + string is always valid
                            Ok(Type::String)
                        } else if self.satisfies_stringable(&right_ty, interner) {
                            // Right implements Stringable
                            Ok(Type::String)
                        } else {
                            self.type_error("Stringable", &right_ty, bin.right.span);
                            Ok(Type::invalid("propagate"))
                        }
                    } else if left_ty.is_numeric() && right_ty.is_numeric() {
                        // Numeric addition
                        if let Some(exp) = expected
                            && self.types_compatible(&left_ty, exp, interner)
                            && self.types_compatible(&right_ty, exp, interner)
                        {
                            return Ok(exp.clone());
                        }
                        if left_ty == Type::F64 || right_ty == Type::F64 {
                            Ok(Type::F64)
                        } else if left_ty == Type::I64 || right_ty == Type::I64 {
                            Ok(Type::I64)
                        } else {
                            Ok(Type::I32)
                        }
                    } else {
                        self.type_error_pair("numeric or string", &left_ty, &right_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
                // Arithmetic ops (except Add): propagate expected type to both operands
                BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                    let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                    if left_ty.is_numeric() && right_ty.is_numeric() {
                        // If we have an expected type and both sides match, use it
                        if let Some(exp) = expected
                            && self.types_compatible(&left_ty, exp, interner)
                            && self.types_compatible(&right_ty, exp, interner)
                        {
                            return Ok(exp.clone());
                        }
                        // Otherwise return wider type
                        if left_ty == Type::F64 || right_ty == Type::F64 {
                            Ok(Type::F64)
                        } else if left_ty == Type::I64 || right_ty == Type::I64 {
                            Ok(Type::I64)
                        } else {
                            Ok(Type::I32)
                        }
                    } else {
                        self.type_error_pair("numeric", &left_ty, &right_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
                // Comparison ops: infer left, check right against left
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => {
                    let left_ty = self.check_expr_expecting(&bin.left, None, interner)?;
                    self.check_expr_expecting(&bin.right, Some(&left_ty), interner)?;
                    Ok(Type::Bool)
                }
                // Logical ops: both sides must be bool
                BinaryOp::And | BinaryOp::Or => {
                    let left_ty =
                        self.check_expr_expecting(&bin.left, Some(&Type::Bool), interner)?;
                    let right_ty =
                        self.check_expr_expecting(&bin.right, Some(&Type::Bool), interner)?;
                    if left_ty == Type::Bool && right_ty == Type::Bool {
                        Ok(Type::Bool)
                    } else {
                        self.type_error_pair("bool", &left_ty, &right_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
                // Bitwise ops: both sides must be integer
                BinaryOp::BitAnd
                | BinaryOp::BitOr
                | BinaryOp::BitXor
                | BinaryOp::Shl
                | BinaryOp::Shr => {
                    let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                    let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                    if left_ty.is_integer() && right_ty.is_integer() {
                        if let Some(exp) = expected
                            && self.types_compatible(&left_ty, exp, interner)
                            && self.types_compatible(&right_ty, exp, interner)
                        {
                            return Ok(exp.clone());
                        }
                        if left_ty == Type::I64 || right_ty == Type::I64 {
                            Ok(Type::I64)
                        } else {
                            Ok(Type::I32)
                        }
                    } else {
                        self.type_error_pair("integer", &left_ty, &right_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
            },
            ExprKind::Unary(un) => match un.op {
                UnaryOp::Neg => {
                    // Special case: -INT_LITERAL should check if the negated value fits
                    // This handles cases like -2147483648 (i32::MIN) where the positive
                    // value doesn't fit but the negated value does
                    if let ExprKind::IntLiteral(value) = &un.operand.kind {
                        let negated = value.wrapping_neg();
                        if let Some(target) = expected
                            && literal_fits(negated, target)
                        {
                            return Ok(self.record_expr_type(&un.operand, target.clone()));
                        }
                        // Fall back to i64 if no expected type or doesn't fit
                        return Ok(self.record_expr_type(&un.operand, Type::I64));
                    }

                    // Propagate expected type through negation
                    let operand_ty = self.check_expr_expecting(&un.operand, expected, interner)?;
                    if operand_ty.is_numeric() {
                        Ok(operand_ty)
                    } else {
                        self.type_error("numeric", &operand_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
                UnaryOp::Not => {
                    // Not always expects and returns bool
                    let operand_ty =
                        self.check_expr_expecting(&un.operand, Some(&Type::Bool), interner)?;
                    if operand_ty == Type::Bool {
                        Ok(Type::Bool)
                    } else {
                        self.type_error("bool", &operand_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
                UnaryOp::BitNot => {
                    // Bitwise not: propagate expected type, requires integer
                    let operand_ty = self.check_expr_expecting(&un.operand, expected, interner)?;
                    if operand_ty.is_integer() {
                        Ok(operand_ty)
                    } else {
                        self.type_error("integer", &operand_ty, expr.span);
                        Ok(Type::invalid("propagate"))
                    }
                }
            },
            ExprKind::Grouping(inner) => self.check_expr_expecting(inner, expected, interner),
            ExprKind::ArrayLiteral(elements) => {
                // Check if expecting a tuple type
                if let Some(Type::Tuple(expected_elems)) = expected {
                    // Check that literal has correct number of elements
                    if elements.len() != expected_elems.len() {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("tuple with {} elements", expected_elems.len()),
                                found: format!("{} elements", elements.len()),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::invalid("propagate"));
                    }
                    // Check each element against its expected type
                    let elem_types: Vec<Type> = elements
                        .iter()
                        .zip(expected_elems.iter())
                        .map(|(elem, expected_elem)| {
                            self.check_expr_expecting(elem, Some(expected_elem), interner)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(Type::Tuple(elem_types));
                }

                // Check if expecting an array type
                let elem_expected = match expected {
                    Some(Type::Array(elem)) => Some(elem.as_ref()),
                    _ => None,
                };

                if elements.is_empty() {
                    if let Some(Type::Array(elem)) = expected {
                        return Ok(Type::Array(elem.clone()));
                    }
                    return Ok(Type::Array(Box::new(Type::unknown())));
                }

                // Infer types for all elements, passing expected element type to each
                let elem_types: Vec<Type> = elements
                    .iter()
                    .map(|e| self.check_expr_expecting(e, elem_expected, interner))
                    .collect::<Result<Vec<_>, _>>()?;

                // Check if all elements have compatible types (homogeneous → Array)
                // or different types (heterogeneous → Tuple)
                let first_ty = &elem_types[0];
                let is_homogeneous = elem_types
                    .iter()
                    .skip(1)
                    .all(|ty| self.types_compatible(ty, first_ty, interner));

                if is_homogeneous {
                    Ok(Type::Array(Box::new(first_ty.clone())))
                } else {
                    Ok(Type::Tuple(elem_types))
                }
            }
            ExprKind::Index(_) => {
                // Index expressions just delegate to check_expr
                self.check_expr(expr, interner)
            }
            ExprKind::Lambda(lambda) => {
                // Extract expected function type if available
                // Support both direct function types and functional interfaces
                let expected_fn = expected.and_then(|t| {
                    if let Type::Function(ft) = t {
                        Some(ft.clone())
                    } else if let Type::Interface(iface) = t {
                        // Check if it's a functional interface (single abstract method, no fields)
                        self.get_functional_interface_type_by_name_id(iface.name_id)
                    } else {
                        None
                    }
                });
                Ok(self.analyze_lambda(lambda, expected_fn.as_ref(), interner))
            }
            // All other cases: infer type, then check compatibility
            _ => {
                let inferred = self.check_expr(expr, interner)?;
                if let Some(expected_ty) = expected
                    && !self.types_compatible(&inferred, expected_ty, interner)
                {
                    let expected = self.type_display(expected_ty);
                    let found = self.type_display(&inferred);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found,
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(inferred)
            }
        }
    }
}
