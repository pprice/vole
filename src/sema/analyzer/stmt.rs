// src/sema/analyzer/stmt.rs

use super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;

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
                        if init_type == LegacyType::Void {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type = declared_type.unwrap_or(init_type);

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type == LegacyType::MetaType
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type = self.resolve_type(type_expr, interner);
                            self.register_type_alias(let_stmt.name, aliased_type, interner);
                        }

                        let var_type_id = self.type_arena.borrow_mut().from_type(&var_type);
                        self.scope.define(
                            let_stmt.name,
                            Variable {
                                ty: var_type_id,
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
                let cond_type_id = self.check_expr_id(&while_stmt.condition, interner)?;
                if !self.is_bool_id(cond_type_id) && !self.is_numeric_id(cond_type_id) {
                    let found = self.type_display_id(cond_type_id);
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
                let cond_type_id = self.check_expr_id(&if_stmt.condition, interner)?;
                if !self.is_bool_id(cond_type_id) && !self.is_numeric_id(cond_type_id) {
                    let found = self.type_display_id(cond_type_id);
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found,
                            span: if_stmt.condition.span.into(),
                        },
                        if_stmt.condition.span,
                    );
                }

                // Check if condition is `x is T` for flow-sensitive narrowing (using TypeId)
                let narrowing_info = if let ExprKind::Is(is_expr) = &if_stmt.condition.kind {
                    if let ExprKind::Identifier(sym) = &is_expr.value.kind {
                        let tested_type_id = self.resolve_type_id(&is_expr.type_expr, interner);
                        // Get original type of variable for else-branch narrowing
                        let original_type_id = self.get_variable_type_id(*sym);
                        Some((*sym, tested_type_id, original_type_id))
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
                if let Some((sym, narrowed_type_id, _)) = &narrowing_info {
                    self.type_overrides.insert(*sym, *narrowed_type_id);
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
                    // Using TypeId - check if original type is a union
                    if let Some((sym, tested_type_id, Some(original_type_id))) = &narrowing_info {
                        let union_variants: Option<Vec<ArenaTypeId>> = {
                            let arena = self.type_arena.borrow();
                            arena.unwrap_union(*original_type_id).map(|v| v.to_vec())
                        };
                        if let Some(variants) = union_variants {
                            // Remove tested type from union
                            let remaining: Vec<_> = variants
                                .iter()
                                .filter(|&&v| v != *tested_type_id)
                                .copied()
                                .collect();
                            if remaining.len() == 1 {
                                // Single type remaining - narrow to that
                                self.type_overrides.insert(*sym, remaining[0]);
                            } else if remaining.len() > 1 {
                                // Multiple types remaining - narrow to smaller union
                                let narrow_id = self.type_arena.borrow_mut().union(remaining);
                                self.type_overrides.insert(*sym, narrow_id);
                            }
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
                let iterable_ty_id = self.check_expr_id(&for_stmt.iterable, interner)?;

                // Determine element type based on iterable type using TypeId
                let elem_ty_id = if self.is_range_id(iterable_ty_id) {
                    self.ty_i64_id()
                } else if let Some(elem_id) = self.unwrap_array_id(iterable_ty_id) {
                    elem_id
                } else if self.is_string_id(iterable_ty_id) {
                    // String is iterable - yields string (individual characters)
                    self.ty_string_id()
                } else if let Some(elem_id) = self.unwrap_runtime_iterator_id(iterable_ty_id) {
                    // Runtime iterators have their element type directly
                    elem_id
                } else {
                    // Check for interface implementing Iterator (uses TypeId directly)
                    if let Some(elem_id) = self.extract_iterator_element_type_id(iterable_ty_id) {
                        elem_id
                    } else {
                        self.type_error_id(
                            "iterable (range, array, string, or Iterator<T>)",
                            iterable_ty_id,
                            for_stmt.iterable.span,
                        );
                        self.ty_invalid_id()
                    }
                };

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.scope.define(
                    for_stmt.var_name,
                    Variable {
                        ty: elem_ty_id,
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
                // Determine expected type for bidirectional type checking (TypeId-based)
                let expected_value_type_id = self.current_function_return.map(|expected| {
                    // If expected is fallible, extract success type for comparison
                    // A `return value` statement returns the success type, not the full fallible type
                    if let Some((success, _error)) =
                        self.type_arena.borrow().unwrap_fallible(expected)
                    {
                        success
                    } else {
                        expected
                    }
                });

                let ret_type_id = if let Some(value) = &ret.value {
                    self.check_expr_expecting_id(value, expected_value_type_id, interner)?
                } else {
                    self.ty_void_id()
                };

                if let Some(expected_id) = expected_value_type_id
                    && !self.types_compatible_id(ret_type_id, expected_id, interner)
                {
                    let expected_str = self.type_display_id(expected_id);
                    let found = self.type_display_id(ret_type_id);
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
                let init_type_id = self.check_expr(&let_tuple.init, interner)?;

                // Recursively check the destructuring pattern using TypeId
                self.check_destructure_pattern_id(
                    &let_tuple.pattern,
                    init_type_id,
                    let_tuple.mutable,
                    let_tuple.init.span,
                    interner,
                );
            }
        }
        Ok(())
    }

    /// Recursively check a destructuring pattern against a type using TypeId (avoids LegacyType)
    fn check_destructure_pattern_id(
        &mut self,
        pattern: &Pattern,
        ty_id: ArenaTypeId,
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        match pattern {
            Pattern::Identifier { name, .. } => {
                self.scope.define(*name, Variable { ty: ty_id, mutable });
                self.add_lambda_local(*name);
            }
            Pattern::Wildcard(_) => {
                // Wildcard - nothing to bind
            }
            Pattern::Tuple { elements, span } => {
                // Check for tuple or fixed array using arena (extract info first to avoid borrow conflicts)
                enum TupleOrArray {
                    Tuple(crate::sema::type_arena::TypeIdVec),
                    FixedArray(ArenaTypeId, usize),
                    Neither,
                }
                let type_info = {
                    let arena = self.type_arena.borrow();
                    if let Some(elem_ids) = arena.unwrap_tuple(ty_id) {
                        TupleOrArray::Tuple(elem_ids.clone())
                    } else if let Some((elem_id, size)) = arena.unwrap_fixed_array(ty_id) {
                        TupleOrArray::FixedArray(elem_id, size)
                    } else {
                        TupleOrArray::Neither
                    }
                };

                match type_info {
                    TupleOrArray::Tuple(elem_type_ids) => {
                        if elements.len() != elem_type_ids.len() {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: format!("tuple of {} elements", elem_type_ids.len()),
                                    found: format!(
                                        "destructuring pattern with {} elements",
                                        elements.len()
                                    ),
                                    span: (*span).into(),
                                },
                                *span,
                            );
                        } else {
                            for (elem_pattern, &elem_type_id) in
                                elements.iter().zip(elem_type_ids.iter())
                            {
                                self.check_destructure_pattern_id(
                                    elem_pattern,
                                    elem_type_id,
                                    mutable,
                                    init_span,
                                    interner,
                                );
                            }
                        }
                    }
                    TupleOrArray::FixedArray(elem_id, size) => {
                        if elements.len() != size {
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
                                self.check_destructure_pattern_id(
                                    elem_pattern,
                                    elem_id,
                                    mutable,
                                    init_span,
                                    interner,
                                );
                            }
                        }
                    }
                    TupleOrArray::Neither => {
                        self.type_error_id("tuple or fixed array", ty_id, init_span);
                    }
                }
            }
            Pattern::Record { fields, span, .. } => {
                self.check_record_destructuring_id(
                    ty_id, fields, mutable, *span, init_span, interner,
                );
            }
            _ => {
                // Other patterns not supported in let destructuring
            }
        }
    }

    /// Analyze a raise statement
    fn analyze_raise_stmt(&mut self, stmt: &RaiseStmt, interner: &Interner) -> ArenaTypeId {
        // Check we're in a fallible function
        let Some(error_type) = self.current_function_error_type else {
            self.add_error(
                SemanticError::RaiseOutsideFallible {
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return self.ty_invalid_id();
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
            return self.ty_invalid_id();
        };

        let type_def = self.entity_registry.get_type(type_id);
        if type_def.error_info.is_none() {
            // Type exists but is not an error type
            self.add_error(
                SemanticError::UndefinedError {
                    name: interner.resolve(stmt.error_name).to_string(),
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return self.ty_invalid_id();
        }

        // Get the error type name for error messages
        let error_type_name = self
            .name_table
            .last_segment_str(self.entity_registry.name_id(type_id))
            .unwrap_or_else(|| "error".to_string());

        // Build field info from EntityRegistry using TypeId (avoids LegacyType)
        let error_fields: Vec<(String, ArenaTypeId)> = self
            .entity_registry
            .fields_on_type(type_id)
            .filter_map(|field_id| {
                let field = self.entity_registry.get_field(field_id);
                let name = self.name_table.last_segment_str(field.name_id)?;
                Some((name, field.ty))
            })
            .collect();

        // Check for missing fields (fields in error type but not provided in raise)
        let provided_fields: HashSet<String> = stmt
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();
        for (field_name, _) in &error_fields {
            if !provided_fields.contains(field_name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: error_type_name.clone(),
                        field: field_name.clone(),
                        span: stmt.span.into(),
                    },
                    stmt.span,
                );
            }
        }

        // Type check field initializers and check for unknown fields
        for field_init in &stmt.fields {
            let value_type_id = match self.check_expr(&field_init.value, interner) {
                Ok(ty_id) => ty_id,
                Err(_) => ArenaTypeId::INVALID,
            };
            let field_init_name = interner.resolve(field_init.name);
            if let Some((_, field_ty_id)) = error_fields
                .iter()
                .find(|(name, _)| name == field_init_name)
            {
                // Known field - check type compatibility using TypeId
                if !self.types_compatible_id(value_type_id, *field_ty_id, interner) {
                    self.add_type_mismatch_id(*field_ty_id, value_type_id, field_init.span);
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
        // Use arena queries to avoid LegacyType conversion
        let stmt_error_name = interner.resolve(stmt.error_name);
        let is_compatible = {
            let arena = self.type_arena.borrow();
            if let Some(declared_type_def_id) = arena.unwrap_error(error_type) {
                // Single error type - must match exactly
                let name = self
                    .name_table
                    .last_segment_str(self.entity_registry.name_id(declared_type_def_id));
                name.as_deref() == Some(stmt_error_name)
            } else if let Some(variants) = arena.unwrap_union(error_type) {
                // Union of error types - raised error must be one of the variants
                variants.iter().any(|&variant_id| {
                    if let Some(variant_type_def_id) = arena.unwrap_error(variant_id) {
                        let name = self
                            .name_table
                            .last_segment_str(self.entity_registry.name_id(variant_type_def_id));
                        name.as_deref() == Some(stmt_error_name)
                    } else {
                        false
                    }
                })
            } else {
                false // Should not happen if we got past the fallible check
            }
        };

        if !is_compatible {
            // Extract types before calling type_display_id to avoid borrow conflict
            let raised_type_id = self.type_arena.borrow_mut().error_type(type_id);
            let declared_str = self.type_display_id(error_type);
            let raised_str = self.type_display_id(raised_type_id);

            self.add_error(
                SemanticError::IncompatibleRaiseError {
                    raised: raised_str,
                    declared: declared_str,
                    span: stmt.span.into(),
                },
                stmt.span,
            );
        }

        self.ty_void_id() // raise doesn't produce a value - it transfers control
    }

    /// Analyze a try expression (propagation)
    ///
    /// try unwraps a fallible type:
    /// - On success: returns the success value
    /// - On error: propagates the error to the caller (early return)
    pub(crate) fn analyze_try(
        &mut self,
        inner_expr: &Expr,
        _interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check the inner expression - must be fallible
        let inner_type_id = self.check_expr(inner_expr, _interner)?;

        // Use arena.unwrap_fallible to check if fallible (avoids LegacyType)
        let fallible_info = self.type_arena.borrow().unwrap_fallible(inner_type_id);
        let Some((success_type_id, error_type_id)) = fallible_info else {
            let found = self.type_display_id(inner_type_id);
            self.add_error(
                SemanticError::TryOnNonFallible {
                    found,
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
            return Ok(ArenaTypeId::INVALID);
        };

        // Check that we're in a fallible function context
        let Some(current_error_id) = self.current_function_error_type else {
            self.add_error(
                SemanticError::TryOutsideFallible {
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
            return Ok(success_type_id);
        };

        // Check that the error type is compatible with the function's error type (TypeId version)
        if !self.error_type_compatible_id(error_type_id, current_error_id) {
            let try_error = self.type_display_id(error_type_id);
            let func_error = self.type_display_id(current_error_id);
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
        Ok(success_type_id)
    }

    /// Check if error type is compatible with function's declared error type (TypeId version)
    fn error_type_compatible_id(
        &self,
        error_type_id: ArenaTypeId,
        func_error_id: ArenaTypeId,
    ) -> bool {
        // Same type (O(1) via TypeId equality)
        if error_type_id == func_error_id {
            return true;
        }

        // Check if func_error is a union and error_type is a member
        let arena = self.type_arena.borrow();
        if let Some(func_variants) = arena.unwrap_union(func_error_id) {
            if func_variants.contains(&error_type_id) {
                return true;
            }
            // Also check if error_type is a union whose members are all in func_error
            if let Some(error_variants) = arena.unwrap_union(error_type_id) {
                return error_variants.iter().all(|ev| func_variants.contains(ev));
            }
        }

        false
    }

    /// Check record destructuring and bind variables (TypeId version)
    fn check_record_destructuring_id(
        &mut self,
        ty_id: ArenaTypeId,
        fields: &[RecordFieldPattern],
        mutable: bool,
        _pattern_span: Span,
        init_span: Span,
        interner: &Interner,
    ) {
        // Get type_def_id from the type using arena
        let type_def_id = {
            let arena = self.type_arena.borrow();
            if let Some((type_def_id, _)) = arena.unwrap_record(ty_id) {
                Some(type_def_id)
            } else if let Some((type_def_id, _)) = arena.unwrap_class(ty_id) {
                Some(type_def_id)
            } else {
                None
            }
        };

        let Some(type_def_id) = type_def_id else {
            self.type_error_id("record or class", ty_id, init_span);
            return;
        };

        // Look up fields from entity_registry - clone to avoid borrow conflicts
        let type_def = self.entity_registry.get_type(type_def_id);
        let generic_info = match &type_def.generic_info {
            Some(gi) => gi.clone(),
            None => {
                self.type_error_id("record or class with fields", ty_id, init_span);
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
                let field_type_id = generic_info.field_types[slot];
                // Bind the field to the binding name
                self.scope.define(
                    field_pattern.binding,
                    Variable {
                        ty: field_type_id,
                        mutable,
                    },
                );
                self.add_lambda_local(field_pattern.binding);
            } else {
                // Get the type name for the error message
                let type_name = self.type_display_id(ty_id);
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
