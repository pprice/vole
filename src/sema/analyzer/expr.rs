// src/sema/analyzer/expr.rs

use super::*;

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
                Some(ty) if literal_fits(*value, ty) => Ok(ty.clone()),
                Some(ty) => {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: ty.name().to_string(),
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
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: ty.name().to_string(),
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
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: ty.name().to_string(),
                            found: "f64".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::F64)
                }
                None => Ok(Type::F64),
            },
            ExprKind::Binary(bin) => {
                match bin.op {
                    // Arithmetic ops: propagate expected type to both operands
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // If we have an expected type and both sides match, use it
                            if let Some(exp) = expected
                                && self.types_compatible(&left_ty, exp)
                                && self.types_compatible(&right_ty, exp)
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
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
                                && self.types_compatible(&left_ty, exp)
                                && self.types_compatible(&right_ty, exp)
                            {
                                return Ok(exp.clone());
                            }
                            if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }
            ExprKind::Unary(un) => {
                match un.op {
                    UnaryOp::Neg => {
                        // Propagate expected type through negation
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, expected, interner)?;
                        if operand_ty.is_numeric() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: operand_ty.name().to_string(),
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        // Bitwise not: propagate expected type, requires integer
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, expected, interner)?;
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }
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
                        self.get_functional_interface_type(iface.name)
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
                    && !self.types_compatible(&inferred, expected_ty)
                {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_ty.name().to_string(),
                            found: inferred.name().to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(inferred)
            }
        }
    }

    pub(crate) fn check_expr(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let ty = self.check_expr_inner(expr, interner)?;
        self.record_expr_type(expr, ty.clone());
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
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
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
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => {
                        if operand_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }

            ExprKind::Call(call) => {
                // Handle assert specially
                if self.is_assert_call(&call.callee, interner) {
                    // Assert is an impure builtin - mark side effects if inside lambda
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }

                    if call.args.len() != 1 {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: 1,
                                found: call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::Void);
                    }

                    let arg_ty = self.check_expr(&call.args[0], interner)?;
                    if arg_ty != Type::Bool && arg_ty != Type::Error {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "bool".to_string(),
                                found: arg_ty.name().to_string(),
                                span: call.args[0].span.into(),
                            },
                            call.args[0].span,
                        );
                    }

                    return Ok(Type::Void);
                }

                if let ExprKind::Identifier(sym) = &call.callee.kind {
                    // First check if it's a top-level function
                    if let Some(func_type) = self.functions.get(sym).cloned() {
                        // Calling a user-defined function - conservatively mark side effects
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        self.check_call_args(
                            &call.args,
                            &func_type.params,
                            expr.span,
                            true, // with_inference
                            interner,
                        )?;
                        return Ok(*func_type.return_type);
                    }

                    // Check if it's a variable with a function type
                    if let Some(Type::Function(func_type)) = self.get_variable_type(*sym) {
                        // Calling a function-typed variable - conservatively mark side effects
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        self.check_call_args(
                            &call.args,
                            &func_type.params,
                            expr.span,
                            true, // with_inference
                            interner,
                        )?;
                        return Ok(*func_type.return_type);
                    }

                    // Check if it's a variable with a functional interface type
                    if let Some(Type::Interface(iface)) = self.get_variable_type(*sym)
                        && let Some(func_type) = self.get_functional_interface_type(iface.name)
                    {
                        // Calling a functional interface - treat like a closure call
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        self.check_call_args(
                            &call.args,
                            &func_type.params,
                            expr.span,
                            true, // with_inference
                            interner,
                        )?;
                        return Ok(*func_type.return_type);
                    }

                    // Check if it's a known builtin function
                    let name = interner.resolve(*sym);
                    if name == "println"
                        || name == "print_char"
                        || name == "flush"
                        || name == "print"
                    {
                        // Impure builtins - mark side effects if inside lambda
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Void);
                    }

                    // Check if it's a variable with a non-function type
                    if let Some(var_ty) = self.get_variable_type(*sym) {
                        self.add_error(
                            SemanticError::NotCallable {
                                ty: var_ty.name().to_string(),
                                span: call.callee.span.into(),
                            },
                            call.callee.span,
                        );
                        // Still check args for more errors
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Error);
                    }

                    // Unknown identifier - might be an undefined function
                    // (will be caught by codegen or other checks)
                    for arg in &call.args {
                        self.check_expr(arg, interner)?;
                    }
                    return Ok(Type::Void);
                }

                // Non-identifier callee (e.g., a lambda expression being called directly)
                let callee_ty = self.check_expr(&call.callee, interner)?;
                if let Type::Function(func_type) = callee_ty {
                    // Calling a function-typed expression - conservatively mark side effects
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }
                    self.check_call_args(
                        &call.args,
                        &func_type.params,
                        expr.span,
                        false, // without inference (callee was just an expression)
                        interner,
                    )?;
                    return Ok(*func_type.return_type);
                }

                // Non-callable type
                if callee_ty != Type::Error {
                    self.add_error(
                        SemanticError::NotCallable {
                            ty: callee_ty.name().to_string(),
                            span: call.callee.span.into(),
                        },
                        call.callee.span,
                    );
                }
                Ok(Type::Error)
            }

            ExprKind::Assign(assign) => {
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
                            if !self.types_compatible(&value_ty, &var_ty) {
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
                                if let Some(field_def) = c.fields.iter().find(|f| f.name == *field)
                                {
                                    if !self.types_compatible(&value_ty, &field_def.ty) {
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
                                if !self.types_compatible(&value_ty, &elem_ty) {
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

            ExprKind::CompoundAssign(compound) => {
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
                                if let Some(field_def) = c.fields.iter().find(|f| f.name == *field)
                                {
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

            ExprKind::Grouping(inner) => self.check_expr(inner, interner),

            ExprKind::ArrayLiteral(elements) => {
                if elements.is_empty() {
                    // Empty array needs type annotation or we use Unknown
                    Ok(Type::Array(Box::new(Type::Unknown)))
                } else {
                    // Infer element type from first element
                    let elem_ty = self.check_expr(&elements[0], interner)?;

                    // Check remaining elements match
                    for elem in elements.iter().skip(1) {
                        let ty = self.check_expr(elem, interner)?;
                        if !self.types_compatible(&ty, &elem_ty) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: elem_ty.name().to_string(),
                                    found: ty.name().to_string(),
                                    span: elem.span.into(),
                                },
                                elem.span,
                            );
                        }
                    }

                    Ok(Type::Array(Box::new(elem_ty)))
                }
            }

            ExprKind::Index(idx) => {
                let obj_ty = self.check_expr(&idx.object, interner)?;
                let index_ty = self.check_expr(&idx.index, interner)?;

                // Index must be integer
                if !index_ty.is_integer() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: index_ty.name().to_string(),
                            span: idx.index.span.into(),
                        },
                        idx.index.span,
                    );
                }

                // Object must be array
                match obj_ty {
                    Type::Array(elem_ty) => Ok(*elem_ty),
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "array".to_string(),
                                found: obj_ty.name().to_string(),
                                span: idx.object.span.into(),
                            },
                            idx.object.span,
                        );
                        Ok(Type::Error)
                    }
                }
            }

            ExprKind::Range(range) => {
                let start_ty = self.check_expr(&range.start, interner)?;
                let end_ty = self.check_expr(&range.end, interner)?;

                if !start_ty.is_integer() || !end_ty.is_integer() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: format!("{} and {}", start_ty.name(), end_ty.name()),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(Type::Range)
            }

            ExprKind::Match(match_expr) => {
                // Check scrutinee type
                let scrutinee_type = self.check_expr(&match_expr.scrutinee, interner)?;

                // Get scrutinee symbol if it's an identifier (for type narrowing)
                let scrutinee_sym = if let ExprKind::Identifier(sym) = &match_expr.scrutinee.kind {
                    Some(*sym)
                } else {
                    None
                };

                // Check exhaustiveness - for union types with type patterns, check coverage
                let is_exhaustive = self.check_match_exhaustiveness(
                    &match_expr.arms,
                    &scrutinee_type,
                    match_expr.span,
                );
                if !is_exhaustive {
                    self.add_error(
                        SemanticError::NonExhaustiveMatch {
                            span: match_expr.span.into(),
                        },
                        match_expr.span,
                    );
                }

                // For fallible types, require at least one error arm
                if let Type::Fallible(_) = &scrutinee_type {
                    let has_error_arm = match_expr
                        .arms
                        .iter()
                        .any(|arm| matches!(arm.pattern, Pattern::Error { .. }));
                    if !has_error_arm {
                        self.add_error(
                            SemanticError::MissingErrorArm {
                                span: match_expr.span.into(),
                            },
                            match_expr.span,
                        );
                    }
                }

                // Check each arm, collect result types
                let mut result_type: Option<Type> = None;
                let mut first_arm_span: Option<Span> = None;

                for arm in &match_expr.arms {
                    // Enter new scope for arm (bindings live here)
                    self.scope = Scope::with_parent(std::mem::take(&mut self.scope));

                    // Save current type overrides
                    let saved_overrides = self.type_overrides.clone();

                    // Check pattern and get narrowing info
                    let narrowed_type = self.check_pattern(&arm.pattern, &scrutinee_type, interner);

                    // Apply type narrowing if scrutinee is an identifier and pattern provides narrowing
                    if let (Some(sym), Some(narrow_ty)) = (scrutinee_sym, &narrowed_type) {
                        self.type_overrides.insert(sym, narrow_ty.clone());
                    }

                    // Check guard if present (must be bool)
                    if let Some(guard) = &arm.guard {
                        let guard_type = self.check_expr(guard, interner)?;
                        if guard_type != Type::Bool && !guard_type.is_numeric() {
                            self.add_error(
                                SemanticError::MatchGuardNotBool {
                                    found: guard_type.name().to_string(),
                                    span: guard.span.into(),
                                },
                                guard.span,
                            );
                        }
                    }

                    // Check body expression
                    let body_type = self.check_expr(&arm.body, interner)?;

                    // Restore type overrides
                    self.type_overrides = saved_overrides;

                    // Unify with previous arms
                    match &result_type {
                        None => {
                            result_type = Some(body_type);
                            first_arm_span = Some(arm.span);
                        }
                        Some(expected) if *expected != body_type => {
                            self.add_error(
                                SemanticError::MatchArmTypeMismatch {
                                    expected: expected.name().to_string(),
                                    found: body_type.name().to_string(),
                                    first_arm: first_arm_span.unwrap().into(),
                                    span: arm.body.span.into(),
                                },
                                arm.body.span,
                            );
                        }
                        _ => {}
                    }

                    // Exit arm scope
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }

                Ok(result_type.unwrap_or(Type::Void))
            }

            ExprKind::Nil => Ok(Type::Nil),

            ExprKind::NullCoalesce(nc) => {
                let value_type = self.check_expr(&nc.value, interner)?;

                // Value must be an optional (union containing Nil)
                if !value_type.is_optional() {
                    self.add_error(
                        SemanticError::NullCoalesceNotOptional {
                            found: format!("{}", value_type),
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
                let tested_type = self.resolve_type(&is_expr.type_expr);

                // Warn/error if tested type is not a variant of value's union
                if let Type::Union(variants) = &value_type
                    && !variants.contains(&tested_type)
                {
                    self.add_error(
                        SemanticError::IsNotVariant {
                            tested: format!("{}", tested_type),
                            union_type: format!("{}", value_type),
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
                // Look up the type (class or record)
                let (type_name, fields, is_class) =
                    if let Some(class_type) = self.classes.get(&struct_lit.name).cloned() {
                        (
                            interner.resolve(struct_lit.name).to_string(),
                            class_type.fields,
                            true,
                        )
                    } else if let Some(record_type) = self.records.get(&struct_lit.name).cloned() {
                        (
                            interner.resolve(struct_lit.name).to_string(),
                            record_type.fields,
                            false,
                        )
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(struct_lit.name).to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::Error);
                    };

                // Check that all required fields are present
                let provided_fields: HashSet<Symbol> =
                    struct_lit.fields.iter().map(|f| f.name).collect();

                for field in &fields {
                    if !provided_fields.contains(&field.name) {
                        self.add_error(
                            SemanticError::MissingField {
                                ty: type_name.clone(),
                                field: interner.resolve(field.name).to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                }

                // Check each provided field
                for field_init in &struct_lit.fields {
                    if let Some(expected_field) = fields.iter().find(|f| f.name == field_init.name)
                    {
                        // check_expr_expecting will report errors if types don't match
                        self.check_expr_expecting(
                            &field_init.value,
                            Some(&expected_field.ty),
                            interner,
                        )?;
                    } else {
                        self.add_error(
                            SemanticError::UnknownField {
                                ty: type_name.clone(),
                                field: interner.resolve(field_init.name).to_string(),
                                span: field_init.span.into(),
                            },
                            field_init.span,
                        );
                        // Still check the value for more errors
                        self.check_expr(&field_init.value, interner)?;
                    }
                }

                // Return the appropriate type
                if is_class {
                    Ok(Type::Class(
                        self.classes.get(&struct_lit.name).unwrap().clone(),
                    ))
                } else {
                    Ok(Type::Record(
                        self.records.get(&struct_lit.name).unwrap().clone(),
                    ))
                }
            }

            ExprKind::FieldAccess(field_access) => {
                let object_type = self.check_expr(&field_access.object, interner)?;

                // Handle module field access
                if let Type::Module(ref module_type) = object_type {
                    let field_name = interner.resolve(field_access.field);
                    if let Some(export_type) = module_type.exports.get(field_name) {
                        return Ok(export_type.clone());
                    } else {
                        self.add_error(
                            SemanticError::ModuleNoExport {
                                module: module_type.path.clone(),
                                name: field_name.to_string(),
                                span: field_access.field_span.into(),
                            },
                            field_access.field_span,
                        );
                        return Ok(Type::Error);
                    }
                }

                // Get fields from object type
                let (type_name, fields) = match &object_type {
                    Type::Class(class_type) => (
                        interner.resolve(class_type.name).to_string(),
                        &class_type.fields,
                    ),
                    Type::Record(record_type) => (
                        interner.resolve(record_type.name).to_string(),
                        &record_type.fields,
                    ),
                    Type::Error => return Ok(Type::Error),
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "class or record".to_string(),
                                found: object_type.name().to_string(),
                                span: field_access.object.span.into(),
                            },
                            field_access.object.span,
                        );
                        return Ok(Type::Error);
                    }
                };

                // Find the field
                if let Some(field) = fields.iter().find(|f| f.name == field_access.field) {
                    Ok(field.ty.clone())
                } else {
                    self.add_error(
                        SemanticError::UnknownField {
                            ty: type_name,
                            field: interner.resolve(field_access.field).to_string(),
                            span: field_access.field_span.into(),
                        },
                        field_access.field_span,
                    );
                    Ok(Type::Error)
                }
            }

            ExprKind::MethodCall(method_call) => {
                let object_type = self.check_expr(&method_call.object, interner)?;
                let method_name = interner.resolve(method_call.method);

                // Handle built-in methods for primitive types
                if let Some(return_type) = self.check_builtin_method(
                    &object_type,
                    method_name,
                    &method_call.args,
                    interner,
                ) {
                    // Record the resolution for codegen
                    let resolved = ResolvedMethod::Implemented {
                        trait_name: None,
                        func_type: FunctionType {
                            params: vec![],
                            return_type: Box::new(return_type.clone()),
                            is_closure: false,
                        },
                        is_builtin: true,
                        external_info: None,
                    };
                    self.method_resolutions.insert(expr.id, resolved);
                    return Ok(return_type);
                }

                // Handle Type::Error early
                if matches!(object_type, Type::Error) {
                    return Ok(Type::Error);
                }

                // Handle module method calls (e.g., math.sqrt(16.0))
                if let Type::Module(ref module_type) = object_type {
                    let method_name_str = interner.resolve(method_call.method);

                    // Look up the method in module exports
                    if let Some(export_type) = module_type.exports.get(method_name_str) {
                        if let Type::Function(func_type) = export_type {
                            // Check argument count
                            if method_call.args.len() != func_type.params.len() {
                                self.add_error(
                                    SemanticError::WrongArgumentCount {
                                        expected: func_type.params.len(),
                                        found: method_call.args.len(),
                                        span: expr.span.into(),
                                    },
                                    expr.span,
                                );
                            }

                            // Check argument types
                            for (arg, param_ty) in
                                method_call.args.iter().zip(func_type.params.iter())
                            {
                                let arg_ty =
                                    self.check_expr_expecting(arg, Some(param_ty), interner)?;
                                if !self.types_compatible(&arg_ty, param_ty) {
                                    self.add_error(
                                        SemanticError::TypeMismatch {
                                            expected: format!("{}", param_ty),
                                            found: format!("{}", arg_ty),
                                            span: arg.span.into(),
                                        },
                                        arg.span,
                                    );
                                }
                            }

                            // Record resolution for codegen
                            let external_info = ExternalMethodInfo {
                                module_path: module_type.path.clone(),
                                native_name: method_name_str.to_string(),
                            };

                            self.method_resolutions.insert(
                                expr.id,
                                ResolvedMethod::Implemented {
                                    trait_name: None,
                                    func_type: func_type.clone(),
                                    is_builtin: false,
                                    external_info: Some(external_info),
                                },
                            );

                            return Ok(*func_type.return_type.clone());
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "function".to_string(),
                                    found: export_type.name().to_string(),
                                    span: method_call.method_span.into(),
                                },
                                method_call.method_span,
                            );
                            return Ok(Type::Error);
                        }
                    } else {
                        self.add_error(
                            SemanticError::ModuleNoExport {
                                module: module_type.path.clone(),
                                name: method_name_str.to_string(),
                                span: method_call.method_span.into(),
                            },
                            method_call.method_span,
                        );
                        return Ok(Type::Error);
                    }
                }

                // Get a descriptive type name for error messages
                let type_name = if let Some(type_id) = TypeId::from_type(&object_type) {
                    type_id.type_name(interner)
                } else {
                    object_type.name().to_string()
                };

                // First, check implement registry for ANY type (primitives, arrays, classes, records)
                // This allows implement blocks to work for all types
                if let Some(type_id) = TypeId::from_type(&object_type)
                    && let Some(impl_) = self
                        .implement_registry
                        .get_method(&type_id, method_call.method)
                {
                    let func_type = impl_.func_type.clone();

                    // Record resolution
                    self.method_resolutions.insert(
                        expr.id,
                        ResolvedMethod::Implemented {
                            trait_name: impl_.trait_name,
                            func_type: func_type.clone(),
                            is_builtin: impl_.is_builtin,
                            external_info: impl_.external_info.clone(),
                        },
                    );

                    // Mark side effects if inside lambda
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }

                    // Check argument count
                    if method_call.args.len() != func_type.params.len() {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: func_type.params.len(),
                                found: method_call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }

                    // Check argument types
                    for (arg, param_ty) in method_call.args.iter().zip(func_type.params.iter()) {
                        let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                        if !self.types_compatible(&arg_ty, param_ty) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: param_ty.name().to_string(),
                                    found: arg_ty.name().to_string(),
                                    span: arg.span.into(),
                                },
                                arg.span,
                            );
                        }
                    }

                    return Ok(*func_type.return_type);
                }

                // Check if object is a functional interface and method matches its single method
                if let Type::Interface(iface) = &object_type {
                    // Check if interface is functional and method matches its abstract method
                    if let Some(iface_def) = self.interface_registry.get(iface.name) {
                        // For functional interfaces, check if the method matches
                        if let Some(method_def) = self.interface_registry.is_functional(iface.name)
                            && method_def.name == method_call.method
                        {
                            let func_type = FunctionType {
                                params: method_def.params.clone(),
                                return_type: Box::new(method_def.return_type.clone()),
                                is_closure: true,
                            };

                            // Mark side effects if inside lambda
                            if self.in_lambda() {
                                self.mark_lambda_has_side_effects();
                            }

                            // Check argument count
                            if method_call.args.len() != func_type.params.len() {
                                self.add_error(
                                    SemanticError::WrongArgumentCount {
                                        expected: func_type.params.len(),
                                        found: method_call.args.len(),
                                        span: expr.span.into(),
                                    },
                                    expr.span,
                                );
                            }

                            // Check argument types
                            for (arg, param_ty) in
                                method_call.args.iter().zip(func_type.params.iter())
                            {
                                let arg_ty =
                                    self.check_expr_expecting(arg, Some(param_ty), interner)?;
                                if !self.types_compatible(&arg_ty, param_ty) {
                                    self.add_error(
                                        SemanticError::TypeMismatch {
                                            expected: param_ty.name().to_string(),
                                            found: arg_ty.name().to_string(),
                                            span: arg.span.into(),
                                        },
                                        arg.span,
                                    );
                                }
                            }

                            // Record resolution for functional interface method
                            self.method_resolutions.insert(
                                expr.id,
                                ResolvedMethod::FunctionalInterface {
                                    func_type: func_type.clone(),
                                },
                            );

                            return Ok(*func_type.return_type);
                        }

                        // For non-functional interfaces, check if method is defined
                        for method_def in &iface_def.methods {
                            if method_def.name == method_call.method {
                                // TODO: Support method calls on non-functional interfaces
                                // For now, we just allow the call
                                let func_type = FunctionType {
                                    params: method_def.params.clone(),
                                    return_type: Box::new(method_def.return_type.clone()),
                                    is_closure: false,
                                };
                                return Ok(*func_type.return_type);
                            }
                        }
                    }
                }

                // Next, check direct methods for class/record types
                let type_sym = match &object_type {
                    Type::Class(class_type) => Some(class_type.name),
                    Type::Record(record_type) => Some(record_type.name),
                    _ => None,
                };

                if let Some(type_sym) = type_sym {
                    let method_key = (type_sym, method_call.method);
                    if let Some(method_type) = self.methods.get(&method_key).cloned() {
                        // Mark side effects if inside lambda
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }

                        // Check argument count
                        if method_call.args.len() != method_type.params.len() {
                            self.add_error(
                                SemanticError::WrongArgumentCount {
                                    expected: method_type.params.len(),
                                    found: method_call.args.len(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                        }

                        // Check argument types
                        for (arg, param_ty) in
                            method_call.args.iter().zip(method_type.params.iter())
                        {
                            let arg_ty =
                                self.check_expr_expecting(arg, Some(param_ty), interner)?;
                            if !self.types_compatible(&arg_ty, param_ty) {
                                self.add_error(
                                    SemanticError::TypeMismatch {
                                        expected: param_ty.name().to_string(),
                                        found: arg_ty.name().to_string(),
                                        span: arg.span.into(),
                                    },
                                    arg.span,
                                );
                            }
                        }

                        // Record resolution for direct method
                        self.method_resolutions.insert(
                            expr.id,
                            ResolvedMethod::Direct {
                                func_type: method_type.clone(),
                            },
                        );

                        return Ok(*method_type.return_type);
                    }

                    // Check for default method from implemented interfaces
                    if let Some(interfaces) = self.type_implements.get(&type_sym).cloned() {
                        for interface_name in &interfaces {
                            if let Some(interface_def) =
                                self.interface_registry.get(*interface_name)
                            {
                                // Look for a default method with matching name
                                for method_def in &interface_def.methods {
                                    if method_def.name == method_call.method
                                        && method_def.has_default
                                    {
                                        let func_type = FunctionType {
                                            params: method_def.params.clone(),
                                            return_type: Box::new(method_def.return_type.clone()),
                                            is_closure: false,
                                        };

                                        // Mark side effects if inside lambda
                                        if self.in_lambda() {
                                            self.mark_lambda_has_side_effects();
                                        }

                                        // Check argument count
                                        if method_call.args.len() != func_type.params.len() {
                                            self.add_error(
                                                SemanticError::WrongArgumentCount {
                                                    expected: func_type.params.len(),
                                                    found: method_call.args.len(),
                                                    span: expr.span.into(),
                                                },
                                                expr.span,
                                            );
                                        }

                                        // Check argument types
                                        for (arg, param_ty) in
                                            method_call.args.iter().zip(func_type.params.iter())
                                        {
                                            let arg_ty = self.check_expr_expecting(
                                                arg,
                                                Some(param_ty),
                                                interner,
                                            )?;
                                            if !self.types_compatible(&arg_ty, param_ty) {
                                                self.add_error(
                                                    SemanticError::TypeMismatch {
                                                        expected: param_ty.name().to_string(),
                                                        found: arg_ty.name().to_string(),
                                                        span: arg.span.into(),
                                                    },
                                                    arg.span,
                                                );
                                            }
                                        }

                                        // Record resolution for default method
                                        self.method_resolutions.insert(
                                            expr.id,
                                            ResolvedMethod::DefaultMethod {
                                                interface_name: *interface_name,
                                                type_name: type_sym,
                                                method_name: method_call.method,
                                                func_type: func_type.clone(),
                                            },
                                        );

                                        return Ok(*func_type.return_type);
                                    }
                                }
                            }
                        }
                    }
                }

                // No method found - report error
                self.add_error(
                    SemanticError::UnknownMethod {
                        ty: type_name,
                        method: interner.resolve(method_call.method).to_string(),
                        span: method_call.method_span.into(),
                    },
                    method_call.method_span,
                );
                // Still check args for more errors
                for arg in &method_call.args {
                    self.check_expr(arg, interner)?;
                }
                Ok(Type::Error)
            }

            ExprKind::Try(inner) => self.analyze_try(inner, interner),

            ExprKind::Import(path) => self
                .analyze_module(path, expr.span, interner)
                .map_err(|_| self.errors.clone()),
        }
    }
}
