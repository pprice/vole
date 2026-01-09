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
        self.record_expr_type(expr, ty.clone());
        Ok(ty)
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
                            let found = self.type_display(&right_ty);
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "Stringable".to_string(),
                                    found,
                                    span: bin.right.span.into(),
                                },
                                bin.right.span,
                            );
                            Ok(Type::Error)
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
                        let found = self.type_display_pair(&left_ty, &right_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "numeric or string".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
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
                        let found = self.type_display_pair(&left_ty, &right_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "numeric".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
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
                        let found = self.type_display_pair(&left_ty, &right_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "bool".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
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
                        let found = self.type_display_pair(&left_ty, &right_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "integer".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
                    }
                }
            },
            ExprKind::Unary(un) => match un.op {
                UnaryOp::Neg => {
                    // Propagate expected type through negation
                    let operand_ty = self.check_expr_expecting(&un.operand, expected, interner)?;
                    if operand_ty.is_numeric() {
                        Ok(operand_ty)
                    } else {
                        let found = self.type_display(&operand_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "numeric".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
                    }
                }
                UnaryOp::Not => {
                    // Not always expects and returns bool
                    let operand_ty =
                        self.check_expr_expecting(&un.operand, Some(&Type::Bool), interner)?;
                    if operand_ty == Type::Bool {
                        Ok(Type::Bool)
                    } else {
                        let found = self.type_display(&operand_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "bool".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
                    }
                }
                UnaryOp::BitNot => {
                    // Bitwise not: propagate expected type, requires integer
                    let operand_ty = self.check_expr_expecting(&un.operand, expected, interner)?;
                    if operand_ty.is_integer() {
                        Ok(operand_ty)
                    } else {
                        let found = self.type_display(&operand_ty);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "integer".to_string(),
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::Error)
                    }
                }
            },
            ExprKind::Grouping(inner) => self.check_expr_expecting(inner, expected, interner),
            ExprKind::ArrayLiteral(elements) => {
                let elem_expected = match expected {
                    Some(Type::Array(elem)) => Some(elem.as_ref()),
                    _ => None,
                };

                if elements.is_empty() {
                    if let Some(Type::Array(elem)) = expected {
                        return Ok(Type::Array(elem.clone()));
                    }
                    return Ok(Type::Array(Box::new(Type::Unknown)));
                }

                let elem_ty = self.check_expr_expecting(&elements[0], elem_expected, interner)?;

                for elem in elements.iter().skip(1) {
                    self.check_expr_expecting(elem, Some(&elem_ty), interner)?;
                }

                Ok(Type::Array(Box::new(elem_ty)))
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
                        self.get_functional_interface_type(iface.name, interner)
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
