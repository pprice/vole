// src/sema/analyzer/stmt.rs

use super::*;

impl Analyzer {
    pub(crate) fn check_block(
        &mut self,
        block: &Block,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for stmt in &block.stmts {
            self.check_stmt(stmt, interner)?;
        }
        Ok(())
    }

    pub(crate) fn check_stmt(
        &mut self,
        stmt: &Stmt,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        match stmt {
            Stmt::Let(let_stmt) => {
                let declared_type = let_stmt.ty.as_ref().map(|t| self.resolve_type(t));
                let init_type =
                    self.check_expr_expecting(&let_stmt.init, declared_type.as_ref(), interner)?;

                // Check if trying to use void return value
                if init_type == Type::Void {
                    self.add_error(
                        SemanticError::VoidReturnUsed {
                            span: let_stmt.init.span.into(),
                        },
                        let_stmt.init.span,
                    );
                }

                let var_type = declared_type.unwrap_or(init_type);

                // If this is a type alias (RHS is a type expression), store it
                if var_type == Type::Type
                    && let ExprKind::TypeLiteral(type_expr) = &let_stmt.init.kind
                {
                    let aliased_type = self.resolve_type(type_expr);
                    self.type_aliases.insert(let_stmt.name, aliased_type);
                }

                self.scope.define(
                    let_stmt.name,
                    Variable {
                        ty: var_type,
                        mutable: let_stmt.mutable,
                    },
                );

                // Track as a local if inside a lambda
                self.add_lambda_local(let_stmt.name);
            }
            Stmt::Expr(expr_stmt) => {
                self.check_expr(&expr_stmt.expr, interner)?;
            }
            Stmt::While(while_stmt) => {
                let cond_type = self.check_expr(&while_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found: cond_type.name().to_string(),
                            span: while_stmt.condition.span.into(),
                        },
                        while_stmt.condition.span,
                    );
                }

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.check_block(&while_stmt.body, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::If(if_stmt) => {
                let cond_type = self.check_expr(&if_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found: cond_type.name().to_string(),
                            span: if_stmt.condition.span.into(),
                        },
                        if_stmt.condition.span,
                    );
                }

                // Check if condition is `x is T` for flow-sensitive narrowing
                let narrowing_info = if let ExprKind::Is(is_expr) = &if_stmt.condition.kind {
                    if let ExprKind::Identifier(sym) = &is_expr.value.kind {
                        let tested_type = self.resolve_type(&is_expr.type_expr);
                        Some((*sym, tested_type))
                    } else {
                        None
                    }
                } else {
                    None
                };

                // Save current overrides
                let saved_overrides = self.type_overrides.clone();

                // Then branch (with narrowing if applicable)
                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                if let Some((sym, narrowed_type)) = &narrowing_info {
                    self.type_overrides.insert(*sym, narrowed_type.clone());
                }
                self.check_block(&if_stmt.then_branch, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }

                // Restore overrides for else branch (no narrowing there for now)
                self.type_overrides = saved_overrides.clone();

                if let Some(else_branch) = &if_stmt.else_branch {
                    let parent = std::mem::take(&mut self.scope);
                    self.scope = Scope::with_parent(parent);
                    self.check_block(else_branch, interner)?;
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }

                // Restore original overrides after the entire if statement
                self.type_overrides = saved_overrides;
            }
            Stmt::For(for_stmt) => {
                let iterable_ty = self.check_expr(&for_stmt.iterable, interner)?;

                let elem_ty = match iterable_ty {
                    Type::Range => Type::I64,
                    Type::Array(elem) => *elem,
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "iterable (range or array)".to_string(),
                                found: iterable_ty.name().to_string(),
                                span: for_stmt.iterable.span.into(),
                            },
                            for_stmt.iterable.span,
                        );
                        Type::Error
                    }
                };

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.scope.define(
                    for_stmt.var_name,
                    Variable {
                        ty: elem_ty,
                        mutable: false,
                    },
                );

                self.check_block(&for_stmt.body, interner)?;

                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::Break(_) => {
                // Could check we're in a loop, but skipping for Phase 1
            }
            Stmt::Continue(_) => {
                // Could validate we're in a loop, skip for now
            }
            Stmt::Return(ret) => {
                let ret_type = if let Some(value) = &ret.value {
                    self.check_expr(value, interner)?
                } else {
                    Type::Void
                };

                if let Some(expected) = &self.current_function_return {
                    // If expected is fallible, extract success type for comparison
                    // A `return value` statement returns the success type, not the full fallible type
                    let expected_value_type = match expected {
                        Type::Fallible(ft) => (*ft.success_type).clone(),
                        other => other.clone(),
                    };

                    if !self.types_compatible(&ret_type, &expected_value_type) {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: expected_value_type.name().to_string(),
                                found: ret_type.name().to_string(),
                                span: ret.span.into(),
                            },
                            ret.span,
                        );
                    }
                }
            }
            Stmt::Raise(raise_stmt) => {
                self.analyze_raise_stmt(raise_stmt, interner);
            }
        }
        Ok(())
    }

    /// Analyze a raise statement
    fn analyze_raise_stmt(&mut self, stmt: &RaiseStmt, interner: &Interner) -> Type {
        // Check we're in a fallible function
        let Some(error_type) = self.current_function_error_type.clone() else {
            self.add_error(
                SemanticError::RaiseOutsideFallible {
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return Type::Error;
        };

        // Look up the error type
        let Some(error_info) = self.error_types.get(&stmt.error_name).cloned() else {
            self.add_error(
                SemanticError::UndefinedError {
                    name: interner.resolve(stmt.error_name).to_string(),
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return Type::Error;
        };

        // Get the error type name for error messages
        let error_type_name = interner.resolve(error_info.name).to_string();

        // Check for missing fields (fields in error type but not provided in raise)
        let provided_fields: HashSet<Symbol> = stmt.fields.iter().map(|f| f.name).collect();
        for field in &error_info.fields {
            if !provided_fields.contains(&field.name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: error_type_name.clone(),
                        field: interner.resolve(field.name).to_string(),
                        span: stmt.span.into(),
                    },
                    stmt.span,
                );
            }
        }

        // Type check field initializers and check for unknown fields
        for field_init in &stmt.fields {
            let value_type = match self.check_expr(&field_init.value, interner) {
                Ok(ty) => ty,
                Err(_) => Type::Error,
            };
            if let Some(field) = error_info.fields.iter().find(|f| f.name == field_init.name) {
                // Known field - check type compatibility
                if !types_compatible_core(&value_type, &field.ty) {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: format!("{}", field.ty),
                            found: format!("{}", value_type),
                            span: field_init.span.into(),
                        },
                        field_init.span,
                    );
                }
            } else {
                // Unknown field
                self.add_error(
                    SemanticError::UnknownField {
                        ty: error_type_name.clone(),
                        field: interner.resolve(field_init.name).to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
            }
        }

        // Verify that raised error type is compatible with declared error type
        let is_compatible = match &error_type {
            Type::ErrorType(declared_info) => {
                // Single error type - must match exactly
                declared_info.name == stmt.error_name
            }
            Type::Union(variants) => {
                // Union of error types - raised error must be one of the variants
                variants.iter().any(|variant| {
                    matches!(variant, Type::ErrorType(info) if info.name == stmt.error_name)
                })
            }
            _ => false, // Should not happen if we got past the fallible check
        };

        if !is_compatible {
            // Format the declared error type for the error message
            let declared_str = match &error_type {
                Type::ErrorType(info) => interner.resolve(info.name).to_string(),
                Type::Union(variants) => {
                    let names: Vec<_> = variants
                        .iter()
                        .filter_map(|v| match v {
                            Type::ErrorType(info) => Some(interner.resolve(info.name).to_string()),
                            _ => None,
                        })
                        .collect();
                    names.join(" | ")
                }
                _ => "unknown".to_string(),
            };

            self.add_error(
                SemanticError::IncompatibleRaiseError {
                    raised: interner.resolve(stmt.error_name).to_string(),
                    declared: declared_str,
                    span: stmt.span.into(),
                },
                stmt.span,
            );
        }

        Type::Void // raise doesn't produce a value - it transfers control
    }

    /// Analyze a try expression (propagation)
    ///
    /// try unwraps a fallible type:
    /// - On success: returns the success value
    /// - On error: propagates the error to the caller (early return)
    pub(crate) fn analyze_try(
        &mut self,
        inner_expr: &Expr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // Check the inner expression - must be fallible
        let inner_type = self.check_expr(inner_expr, interner)?;

        let (success_type, error_type) = match &inner_type {
            Type::Fallible(ft) => ((*ft.success_type).clone(), (*ft.error_type).clone()),
            _ => {
                self.add_error(
                    SemanticError::TryOnNonFallible {
                        found: format!("{}", inner_type),
                        span: inner_expr.span.into(),
                    },
                    inner_expr.span,
                );
                return Ok(Type::Error);
            }
        };

        // Check that we're in a fallible function context
        let Some(ref current_error) = self.current_function_error_type else {
            self.add_error(
                SemanticError::TryOutsideFallible {
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
            return Ok(success_type);
        };

        // Check that the error type is compatible with the function's error type
        if !self.error_type_compatible(&error_type, current_error) {
            self.add_error(
                SemanticError::IncompatibleTryError {
                    try_error: format!("{}", error_type),
                    func_error: format!("{}", current_error),
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
        }

        // try unwraps - returns the success type
        Ok(success_type)
    }

    /// Check if error type is compatible with function's declared error type
    fn error_type_compatible(&self, error_type: &Type, func_error: &Type) -> bool {
        // Same type
        if error_type == func_error {
            return true;
        }

        // error_type is a member of func_error union
        if let Type::Union(variants) = func_error {
            if variants.contains(error_type) {
                return true;
            }
            // Also check if error_type is a union whose members are all in func_error
            if let Type::Union(error_variants) = error_type {
                return error_variants.iter().all(|ev| variants.contains(ev));
            }
        }

        false
    }
}
