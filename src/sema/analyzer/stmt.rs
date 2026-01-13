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
                match &let_stmt.init {
                    LetInit::Expr(init_expr) => {
                        // Check for ambiguous type alias: let Alias = TypeName
                        // where TypeName is a type but syntax is ambiguous
                        if let ExprKind::Identifier(ident_sym) = &init_expr.kind {
                            let ident_name = interner.resolve(*ident_sym);
                            if self
                                .resolver(interner)
                                .resolve_type(*ident_sym, &self.entity_registry)
                                .is_some()
                            {
                                let let_name = interner.resolve(let_stmt.name);
                                self.add_error(
                                    SemanticError::AmbiguousTypeAlias {
                                        name: let_name.to_string(),
                                        type_name: ident_name.to_string(),
                                        span: init_expr.span.into(),
                                    },
                                    init_expr.span,
                                );
                            }
                        }

                        let declared_type =
                            let_stmt.ty.as_ref().map(|t| self.resolve_type(t, interner));
                        let init_type =
                            self.check_expr_expecting(init_expr, declared_type.as_ref(), interner)?;

                        // Check if trying to use void return value
                        if init_type == Type::Void {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type = declared_type.unwrap_or(init_type);

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type == Type::Type
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type = self.resolve_type(type_expr, interner);
                            self.register_type_alias(let_stmt.name, aliased_type, interner);
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
                    LetInit::TypeAlias(type_expr) => {
                        // Type alias: let Numeric = i32 | i64
                        let aliased_type = self.resolve_type(type_expr, interner);
                        self.register_type_alias(let_stmt.name, aliased_type, interner);
                    }
                }
            }
            Stmt::Expr(expr_stmt) => {
                self.check_expr(&expr_stmt.expr, interner)?;
            }
            Stmt::While(while_stmt) => {
                let cond_type = self.check_expr(&while_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    let found = self.type_display(&cond_type);
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found,
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
                    let found = self.type_display(&cond_type);
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found,
                            span: if_stmt.condition.span.into(),
                        },
                        if_stmt.condition.span,
                    );
                }

                // Check if condition is `x is T` for flow-sensitive narrowing
                let narrowing_info = if let ExprKind::Is(is_expr) = &if_stmt.condition.kind {
                    if let ExprKind::Identifier(sym) = &is_expr.value.kind {
                        let tested_type = self.resolve_type(&is_expr.type_expr, interner);
                        // Get original type of variable for else-branch narrowing
                        let original_type = self.get_variable_type(*sym);
                        Some((*sym, tested_type, original_type))
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
                if let Some((sym, narrowed_type, _)) = &narrowing_info {
                    self.type_overrides.insert(*sym, narrowed_type.clone());
                }
                self.check_block(&if_stmt.then_branch, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }

                // Restore overrides for else branch
                self.type_overrides = saved_overrides.clone();

                if let Some(else_branch) = &if_stmt.else_branch {
                    let parent = std::mem::take(&mut self.scope);
                    self.scope = Scope::with_parent(parent);

                    // Apply else-branch narrowing: if x is T, else branch has x: (original - T)
                    if let Some((sym, tested_type, Some(Type::Union(variants)))) = &narrowing_info {
                        // Remove tested type from union
                        let remaining: Vec<_> = variants
                            .iter()
                            .filter(|v| *v != tested_type)
                            .cloned()
                            .collect();
                        if remaining.len() == 1 {
                            // Single type remaining - narrow to that
                            self.type_overrides.insert(*sym, remaining[0].clone());
                        } else if remaining.len() > 1 {
                            // Multiple types remaining - narrow to smaller union
                            self.type_overrides.insert(*sym, Type::Union(remaining));
                        }
                    }

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

                let elem_ty = match &iterable_ty {
                    Type::Range => Type::I64,
                    Type::Array(elem) => *elem.clone(),
                    // String is iterable - yields string (individual characters)
                    Type::String => Type::String,
                    // Runtime iterators have their element type directly
                    Type::RuntimeIterator(elem) => *elem.clone(),
                    Type::Interface(_) => {
                        if let Some(elem) =
                            self.extract_iterator_element_type(&iterable_ty, interner)
                        {
                            elem
                        } else {
                            self.type_error(
                                "iterable (range, array, string, or Iterator<T>)",
                                &iterable_ty,
                                for_stmt.iterable.span,
                            );
                            Type::invalid("propagate")
                        }
                    }
                    _ => {
                        self.type_error(
                            "iterable (range, array, string, or Iterator<T>)",
                            &iterable_ty,
                            for_stmt.iterable.span,
                        );
                        Type::invalid("propagate")
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
                // Determine expected type for bidirectional type checking
                let expected_value_type = self.current_function_return.as_ref().map(|expected| {
                    // If expected is fallible, extract success type for comparison
                    // A `return value` statement returns the success type, not the full fallible type
                    match expected {
                        Type::Fallible(ft) => (*ft.success_type).clone(),
                        other => other.clone(),
                    }
                });

                let ret_type = if let Some(value) = &ret.value {
                    self.check_expr_expecting(value, expected_value_type.as_ref(), interner)?
                } else {
                    Type::Void
                };

                if let Some(expected) = &expected_value_type
                    && !self.types_compatible(&ret_type, expected, interner)
                {
                    let expected_str = self.type_display(expected);
                    let found = self.type_display(&ret_type);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_str,
                            found,
                            span: ret.span.into(),
                        },
                        ret.span,
                    );
                }
            }
            Stmt::Raise(raise_stmt) => {
                self.analyze_raise_stmt(raise_stmt, interner);
            }
            Stmt::LetTuple(let_tuple) => {
                // Check the initializer
                let init_type = self.check_expr(&let_tuple.init, interner)?;

                // Recursively check the destructuring pattern
                self.check_destructure_pattern(
                    &let_tuple.pattern,
                    &init_type,
                    let_tuple.mutable,
                    let_tuple.init.span,
                    interner,
                );
            }
        }
        Ok(())
    }

    /// Recursively check a destructuring pattern against a type, defining variables as needed
    fn check_destructure_pattern(
        &mut self,
        pattern: &Pattern,
        ty: &Type,
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        match pattern {
            Pattern::Identifier { name, .. } => {
                self.scope.define(
                    *name,
                    Variable {
                        ty: ty.clone(),
                        mutable,
                    },
                );
                self.add_lambda_local(*name);
            }
            Pattern::Wildcard(_) => {
                // Wildcard - nothing to bind
            }
            Pattern::Tuple { elements, span } => match ty {
                Type::Tuple(elem_types) => {
                    if elements.len() != elem_types.len() {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("tuple of {} elements", elem_types.len()),
                                found: format!(
                                    "destructuring pattern with {} elements",
                                    elements.len()
                                ),
                                span: (*span).into(),
                            },
                            *span,
                        );
                    } else {
                        for (elem_pattern, elem_type) in elements.iter().zip(elem_types.iter()) {
                            self.check_destructure_pattern(
                                elem_pattern,
                                elem_type,
                                mutable,
                                init_span,
                                interner,
                            );
                        }
                    }
                }
                Type::FixedArray { element, size } => {
                    if elements.len() != *size {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("array of {} elements", size),
                                found: format!(
                                    "destructuring pattern with {} elements",
                                    elements.len()
                                ),
                                span: (*span).into(),
                            },
                            *span,
                        );
                    } else {
                        for elem_pattern in elements.iter() {
                            self.check_destructure_pattern(
                                elem_pattern,
                                element,
                                mutable,
                                init_span,
                                interner,
                            );
                        }
                    }
                }
                _ => {
                    self.type_error("tuple or fixed array", ty, init_span);
                }
            },
            Pattern::Record { fields, span, .. } => {
                self.check_record_destructuring(ty, fields, mutable, *span, init_span, interner);
            }
            _ => {
                // Other patterns not supported in let destructuring
            }
        }
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
            return Type::invalid("propagate");
        };

        // Look up the error type via resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(stmt.error_name, &self.entity_registry);

        let Some(type_id) = type_id_opt else {
            self.add_error(
                SemanticError::UndefinedError {
                    name: interner.resolve(stmt.error_name).to_string(),
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return Type::invalid("propagate");
        };

        let type_def = self.entity_registry.get_type(type_id);
        let Some(error_info) = type_def.error_info.clone() else {
            // Type exists but is not an error type
            self.add_error(
                SemanticError::UndefinedError {
                    name: interner.resolve(stmt.error_name).to_string(),
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return Type::invalid("propagate");
        };

        // Get the error type name for error messages
        let error_type_name = self
            .name_table
            .last_segment_str(self.entity_registry.name_id(error_info.type_def_id))
            .unwrap_or_else(|| "error".to_string());

        // Check for missing fields (fields in error type but not provided in raise)
        let provided_fields: HashSet<String> = stmt
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();
        for field in &error_info.fields {
            if !provided_fields.contains(&field.name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: error_type_name.clone(),
                        field: field.name.clone(),
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
                Err(_) => Type::invalid("fallback"),
            };
            let field_init_name = interner.resolve(field_init.name);
            if let Some(field) = error_info.fields.iter().find(|f| f.name == field_init_name) {
                // Known field - check type compatibility
                if !types_compatible_core(&value_type, &field.ty) {
                    self.add_type_mismatch(&field.ty, &value_type, field_init.span);
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
        let stmt_error_name = interner.resolve(stmt.error_name);
        let is_compatible = match &error_type {
            Type::ErrorType(declared_info) => {
                // Single error type - must match exactly
                let name = self
                    .name_table
                    .last_segment_str(self.entity_registry.name_id(declared_info.type_def_id));
                name.as_deref() == Some(stmt_error_name)
            }
            Type::Union(variants) => {
                // Union of error types - raised error must be one of the variants
                variants.iter().any(|variant| {
                    if let Type::ErrorType(info) = variant {
                        let name = self
                            .name_table
                            .last_segment_str(self.entity_registry.name_id(info.type_def_id));
                        name.as_deref() == Some(stmt_error_name)
                    } else {
                        false
                    }
                })
            }
            _ => false, // Should not happen if we got past the fallible check
        };

        if !is_compatible {
            let declared_str = self.type_display(&error_type);
            let raised_str = self.type_display(&Type::ErrorType(error_info));

            self.add_error(
                SemanticError::IncompatibleRaiseError {
                    raised: raised_str,
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
                let found = self.type_display(&inner_type);
                self.add_error(
                    SemanticError::TryOnNonFallible {
                        found,
                        span: inner_expr.span.into(),
                    },
                    inner_expr.span,
                );
                return Ok(Type::invalid("propagate"));
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
        let current_error = current_error.clone();

        // Check that the error type is compatible with the function's error type
        if !self.error_type_compatible(&error_type, &current_error) {
            let try_error = self.type_display(&error_type);
            let func_error = self.type_display(&current_error);
            self.add_error(
                SemanticError::IncompatibleTryError {
                    try_error,
                    func_error,
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

    /// Check record destructuring and bind variables
    fn check_record_destructuring(
        &mut self,
        init_type: &Type,
        fields: &[RecordFieldPattern],
        mutable: bool,
        _pattern_span: Span,
        init_span: Span,
        interner: &Interner,
    ) {
        // Get type_def_id from the type
        let type_def_id = match init_type {
            Type::Record(record_type) => record_type.type_def_id,
            Type::Class(class_type) => class_type.type_def_id,
            _ => {
                self.type_error("record or class", init_type, init_span);
                return;
            }
        };

        // Look up fields from entity_registry - clone to avoid borrow conflicts
        let type_def = self.entity_registry.get_type(type_def_id);
        let generic_info = match &type_def.generic_info {
            Some(gi) => gi.clone(),
            None => {
                self.type_error("record or class with fields", init_type, init_span);
                return;
            }
        };

        // Check each destructured field
        for field_pattern in fields {
            let field_name_str = interner.resolve(field_pattern.field_name);

            // Find the field by name in generic_info
            let found = generic_info
                .field_names
                .iter()
                .enumerate()
                .find(|(_, name_id)| {
                    self.name_table.last_segment_str(**name_id).as_deref() == Some(field_name_str)
                });

            if let Some((slot, _)) = found {
                let field_type = generic_info.field_types[slot].clone();
                // Bind the field to the binding name
                self.scope.define(
                    field_pattern.binding,
                    Variable {
                        ty: field_type,
                        mutable,
                    },
                );
                self.add_lambda_local(field_pattern.binding);
            } else {
                // Get the type name for the error message
                let type_name = self.type_display(init_type);
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name,
                        field: field_name_str.to_string(),
                        span: field_pattern.span.into(),
                    },
                    field_pattern.span,
                );
            }
        }
    }
}
