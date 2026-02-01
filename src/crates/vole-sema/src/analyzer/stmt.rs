// src/sema/analyzer/stmt.rs

use super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::PatternKind;

impl Analyzer {
    /// Checks whether all control flow paths through a block definitely return.
    ///
    /// A block definitely returns if any of its statements definitely returns
    /// (e.g. a return/raise statement, or a branching construct where all branches return).
    fn block_definitely_returns(block: &Block) -> bool {
        block.stmts.iter().any(Self::stmt_definitely_returns)
    }

    /// Checks whether a statement definitely returns on all control flow paths.
    fn stmt_definitely_returns(stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Return(_) => true,
            Stmt::Raise(_) => true,
            Stmt::If(if_stmt) => {
                // Both branches must exist and both must definitely return
                if let Some(else_branch) = &if_stmt.else_branch {
                    Self::block_definitely_returns(&if_stmt.then_branch)
                        && Self::block_definitely_returns(else_branch)
                } else {
                    false
                }
            }
            Stmt::Expr(expr_stmt) => Self::expr_definitely_returns(&expr_stmt.expr),
            // While/For loops may never execute their body
            _ => false,
        }
    }

    /// Checks whether an expression definitely returns on all control flow paths.
    ///
    /// This is used for expression-statements that contain control flow like
    /// match/when with return statements in all arms, or unreachable.
    fn expr_definitely_returns(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Unreachable => true,
            ExprKind::Block(block_expr) => Self::block_expr_definitely_returns(block_expr),
            ExprKind::Match(match_expr) => {
                // All arms must definitely return, and there must be at least one arm
                !match_expr.arms.is_empty()
                    && match_expr
                        .arms
                        .iter()
                        .all(|arm| Self::expr_definitely_returns(&arm.body))
            }
            ExprKind::When(when_expr) => {
                // All arms must definitely return, must have a wildcard (else) arm,
                // and there must be at least one arm
                let has_wildcard = when_expr.arms.iter().any(|arm| arm.condition.is_none());
                has_wildcard
                    && !when_expr.arms.is_empty()
                    && when_expr
                        .arms
                        .iter()
                        .all(|arm| Self::expr_definitely_returns(&arm.body))
            }
            ExprKind::If(if_expr) => {
                // Both branches must exist and both must definitely return
                if let Some(else_branch) = &if_expr.else_branch {
                    Self::expr_definitely_returns(&if_expr.then_branch)
                        && Self::expr_definitely_returns(else_branch)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Checks whether a block expression definitely returns on all control flow paths.
    fn block_expr_definitely_returns(block: &BlockExpr) -> bool {
        block.stmts.iter().any(Self::stmt_definitely_returns)
    }

    /// Check if an expression kind is a literal that can benefit from bidirectional type inference.
    /// This includes int literals and float literals - types that can be inferred from context.
    fn is_inferable_literal(kind: &ExprKind) -> bool {
        matches!(
            kind,
            ExprKind::IntLiteral(_, None)   // Int without suffix
                | ExprKind::FloatLiteral(_, None) // Float without suffix
        )
    }

    pub(crate) fn check_block(
        &mut self,
        block: &Block,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        let mut info = ReturnInfo::default();
        for stmt in &block.stmts {
            let stmt_info = self.check_stmt(stmt, interner)?;
            info.return_types.extend(stmt_info.return_types);
            if stmt_info.definitely_returns {
                info.definitely_returns = true;
                // Future: could warn about unreachable code after this
            }
        }
        Ok(info)
    }

    pub(crate) fn check_stmt(
        &mut self,
        stmt: &Stmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        match stmt {
            Stmt::Let(let_stmt) => {
                match &let_stmt.init {
                    LetInit::Expr(init_expr) => {
                        // Check for ambiguous type alias: let Alias = TypeName
                        // where TypeName is a type but syntax is ambiguous.
                        // Sentinel types are excluded because bare-name construction is valid.
                        if let ExprKind::Identifier(ident_sym) = &init_expr.kind {
                            let ident_name = interner.resolve(*ident_sym);
                            // Well-known sentinel values (nil, Done) are valid bare-name
                            // constructions and should not trigger the ambiguity warning.
                            if !matches!(ident_name, "nil" | "Done") {
                                let resolved = self
                                    .resolver(interner)
                                    .resolve_type(*ident_sym, &self.entity_registry());
                                if let Some(type_def_id) = resolved {
                                    let kind = self.entity_registry().type_kind(type_def_id);
                                    if !kind.is_sentinel() {
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
                            }
                        }

                        let declared_type_id = let_stmt
                            .ty
                            .as_ref()
                            .map(|t| self.resolve_type_id(t, interner));

                        // Check that never is not used in variable declarations
                        if let Some(decl_type_id) = declared_type_id {
                            self.check_never_not_allowed(decl_type_id, let_stmt.span);
                        }
                        if let Some(ty) = &let_stmt.ty {
                            self.check_union_simplification(ty, let_stmt.span);
                            self.check_combination_not_allowed(ty, let_stmt.span);
                        }

                        // Store declared type for codegen (keyed by init expression id)
                        if let Some(decl_type_id) = declared_type_id {
                            self.declared_var_types.insert(init_expr.id, decl_type_id);
                        }

                        // For recursive lambdas: if lambda has fully explicit types,
                        // pre-register the variable so it's in scope during body analysis.
                        // This enables recursive self-reference by making the binding
                        // visible before the lambda body is analyzed.
                        let preregistered = if let ExprKind::Lambda(lambda) = &init_expr.kind {
                            if let Some(fn_type_id) = self.lambda_explicit_type_id(lambda, interner)
                            {
                                self.scope.define(
                                    let_stmt.name,
                                    Variable {
                                        ty: fn_type_id,
                                        mutable: let_stmt.mutable,
                                    },
                                );
                                true
                            } else {
                                false
                            }
                        } else {
                            false
                        };

                        let init_type_id =
                            self.check_expr_expecting_id(init_expr, declared_type_id, interner)?;

                        // Check if trying to use void return value
                        if init_type_id == ArenaTypeId::VOID {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type_id = declared_type_id.unwrap_or(init_type_id);

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type_id == ArenaTypeId::METATYPE
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type_id = self.resolve_type_id(type_expr, interner);
                            self.register_type_alias_id(
                                let_stmt.name,
                                aliased_type_id,
                                interner,
                                let_stmt.span,
                            );
                        }

                        // Only define if not already pre-registered for recursion
                        if !preregistered {
                            self.scope.define(
                                let_stmt.name,
                                Variable {
                                    ty: var_type_id,
                                    mutable: let_stmt.mutable,
                                },
                            );
                        }
                        // Track as a local if inside a lambda (even if preregistered)
                        // This is needed so nested functions aren't incorrectly marked as captures
                        self.add_lambda_local(let_stmt.name);

                        // Track lambda variables for default parameter support
                        if let ExprKind::Lambda(lambda) = &init_expr.kind {
                            let required_params = Self::lambda_required_params(lambda);
                            self.lambda_variables
                                .insert(let_stmt.name, (init_expr.id, required_params));
                        }
                    }
                    LetInit::TypeAlias(type_expr) => {
                        // Type alias: let Numeric = i32 | i64
                        let aliased_type_id = self.resolve_type_id(type_expr, interner);
                        // Check for struct types in union variants
                        self.check_struct_in_union(aliased_type_id, let_stmt.span);
                        self.register_type_alias_id(
                            let_stmt.name,
                            aliased_type_id,
                            interner,
                            let_stmt.span,
                        );
                    }
                }
            }
            Stmt::Expr(expr_stmt) => {
                // Check if the expression definitely returns before type-checking
                // (structural analysis on the AST, independent of types)
                let definitely_returns = Self::expr_definitely_returns(&expr_stmt.expr);

                let expr_type_id = self.check_expr(&expr_stmt.expr, interner)?;

                // Check for unused expression result
                // Don't warn if:
                // 1. The expression is void (nothing to discard)
                // 2. The expression is an assignment (regular or discard - assignments are
                //    inherently used for their side effect)
                // 3. The expression is a compound assignment (+=, -=, etc.)
                // 4. The type is invalid (already has errors)
                let is_assignment = matches!(
                    &expr_stmt.expr.kind,
                    ExprKind::Assign(_) | ExprKind::CompoundAssign(_)
                );
                if !is_assignment
                    && expr_type_id != ArenaTypeId::VOID
                    && !expr_type_id.is_invalid()
                    && !expr_type_id.is_never()
                {
                    let ty = self.type_display_id(expr_type_id);
                    self.add_warning(
                        SemanticWarning::UnusedExpressionResult {
                            ty,
                            span: expr_stmt.expr.span.into(),
                        },
                        expr_stmt.expr.span,
                    );
                }

                if definitely_returns {
                    return Ok(ReturnInfo {
                        definitely_returns: true,
                        return_types: vec![],
                    });
                }
            }
            Stmt::While(while_stmt) => {
                let cond_type_id = self.check_expr(&while_stmt.condition, interner)?;
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
                // While loop body may never execute, so we collect return_types
                // but don't propagate definitely_returns
                let body_info = self.check_block(&while_stmt.body, interner)?;
                let _ = body_info; // Return info from loops handled in v-2602
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::If(if_stmt) => {
                let cond_type_id = self.check_expr(&if_stmt.condition, interner)?;
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

                // Check if condition is `x is T` for flow-sensitive narrowing
                let narrowing_info = self.extract_is_narrowing_info(&if_stmt.condition, interner);

                // Save current overrides
                let saved_overrides = self.type_overrides.clone();

                // Then branch (with narrowing if applicable)
                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                if let Some((sym, narrowed_type_id, _)) = &narrowing_info {
                    self.type_overrides.insert(*sym, *narrowed_type_id);
                }
                let then_info = self.check_block(&if_stmt.then_branch, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }

                // Restore overrides for else branch
                self.type_overrides = saved_overrides.clone();

                // Check else branch if present
                let (else_info, has_else) = if let Some(else_branch) = &if_stmt.else_branch {
                    let parent = std::mem::take(&mut self.scope);
                    self.scope = Scope::with_parent(parent);

                    // Apply else-branch narrowing: if x is T, else branch has x: (original - T)
                    if let Some((sym, tested_type_id, Some(original_type_id))) = &narrowing_info
                        && let Some(else_narrowed) =
                            self.compute_else_narrowed_type(*tested_type_id, *original_type_id)
                    {
                        self.type_overrides.insert(*sym, else_narrowed);
                    }

                    let info = self.check_block(else_branch, interner)?;
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                    (info, true)
                } else {
                    // No else branch means the if might not execute, so definitely_returns is false
                    (ReturnInfo::default(), false)
                };

                // Restore original overrides after the entire if statement
                self.type_overrides = saved_overrides;

                // Aggregate return info from both branches:
                // - definitely_returns only if BOTH branches return AND there is an else branch
                // - collect return_types from both branches
                let mut return_types = then_info.return_types;
                return_types.extend(else_info.return_types);

                return Ok(ReturnInfo {
                    definitely_returns: has_else
                        && then_info.definitely_returns
                        && else_info.definitely_returns,
                    return_types,
                });
            }
            Stmt::For(for_stmt) => {
                let iterable_ty_id = self.check_expr(&for_stmt.iterable, interner)?;

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

                // For loop body may never execute, so we collect return_types
                // but don't propagate definitely_returns
                let body_info = self.check_block(&for_stmt.body, interner)?;
                let _ = body_info; // Return info from loops handled in v-2602

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
                // Determine expected type for type checking (TypeId-based)
                // Only use expected type if we're NOT in inference mode (current_function_return is set)
                let expected_value_type_id = self.current_function_return.map(|expected| {
                    // If expected is fallible, extract success type for comparison
                    // A `return value` statement returns the success type, not the full fallible type
                    if let Some((success, _error)) = self.type_arena().unwrap_fallible(expected) {
                        success
                    } else {
                        expected
                    }
                });

                // Get the span of the return value expression (or the return keyword for bare returns)
                let ret_value_span = ret.value.as_ref().map(|v| v.span).unwrap_or(ret.span);

                // Type check the return expression.
                // For numeric/float literals, use bidirectional inference to infer type from return type.
                // For other expressions, check normally and report E2096 for mismatches.
                let ret_type_id = if let Some(value) = &ret.value {
                    if Self::is_inferable_literal(&value.kind) {
                        // Use bidirectional inference for literals (e.g., return 0.0 in f32 func)
                        self.check_expr_expecting_id(value, expected_value_type_id, interner)?
                    } else {
                        // For non-literals, check without expected type to avoid double errors
                        self.check_expr(value, interner)?
                    }
                } else {
                    self.ty_void_id()
                };

                // In inference mode (current_function_return is None), we collect all return types
                // via ReturnInfo and compute the union at the end.
                // When NOT in inference mode, check that return type matches expected.
                if let Some(expected_id) = expected_value_type_id
                    && !self.types_compatible_id(ret_type_id, expected_id, interner)
                {
                    let expected_str = self.type_display_id(expected_id);
                    let found = self.type_display_id(ret_type_id);
                    self.add_error(
                        SemanticError::ReturnTypeMismatch {
                            expected: expected_str,
                            found,
                            span: ret_value_span.into(),
                        },
                        ret_value_span,
                    );
                }

                return Ok(ReturnInfo {
                    definitely_returns: true,
                    return_types: vec![(ret_type_id, ret_value_span)],
                });
            }
            Stmt::Raise(raise_stmt) => {
                self.analyze_raise_stmt(raise_stmt, interner);

                return Ok(ReturnInfo {
                    definitely_returns: true,
                    return_types: vec![],
                });
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
        Ok(ReturnInfo::default())
    }

    /// Recursively check a destructuring pattern against a type.
    pub(super) fn check_destructure_pattern_id(
        &mut self,
        pattern: &Pattern,
        ty_id: ArenaTypeId,
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        match &pattern.kind {
            PatternKind::Identifier { name } => {
                self.scope.define(*name, Variable { ty: ty_id, mutable });
                self.add_lambda_local(*name);
            }
            PatternKind::Wildcard => {
                // Wildcard - nothing to bind
            }
            PatternKind::Tuple { elements } => {
                let span = pattern.span;
                // Check for tuple or fixed array using arena (extract info first to avoid borrow conflicts)
                enum TupleOrArray {
                    Tuple(crate::type_arena::TypeIdVec),
                    FixedArray(ArenaTypeId, usize),
                    Neither,
                }
                let type_info = {
                    let arena = self.type_arena();
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
                                    span: span.into(),
                                },
                                span,
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
                                    span: span.into(),
                                },
                                span,
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
            PatternKind::Record { fields, .. } => {
                let span = pattern.span;
                self.check_record_destructuring_id(
                    ty_id, fields, mutable, span, init_span, interner,
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
            .resolve_type(stmt.error_name, &self.entity_registry());

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

        let has_error_info = self
            .entity_registry()
            .get_type(type_id)
            .error_info
            .is_some();
        if !has_error_info {
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
        let error_type_name = {
            let name_id = self.entity_registry().name_id(type_id);
            self.name_table()
                .last_segment_str(name_id)
                .unwrap_or_else(|| "error".to_string())
        };

        // Collect field IDs first to avoid borrow conflicts in the loop
        let field_ids = self.entity_registry().type_fields(type_id);
        let error_fields: Vec<(String, ArenaTypeId)> = field_ids
            .into_iter()
            .filter_map(|field_id| {
                let (name_id, ty) = self.entity_registry().field_name_and_type(field_id);
                let name = self.name_table().last_segment_str(name_id)?;
                Some((name, ty))
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
        let stmt_error_name = interner.resolve(stmt.error_name);
        let is_compatible = {
            let arena = self.type_arena();
            if let Some(declared_type_def_id) = arena.unwrap_error(error_type) {
                // Single error type - must match exactly
                let name = self
                    .name_table()
                    .last_segment_str(self.entity_registry().name_id(declared_type_def_id));
                name.as_deref() == Some(stmt_error_name)
            } else if let Some(variants) = arena.unwrap_union(error_type) {
                // Union of error types - raised error must be one of the variants
                variants.iter().any(|&variant_id| {
                    if let Some(variant_type_def_id) = arena.unwrap_error(variant_id) {
                        let name = self
                            .name_table()
                            .last_segment_str(self.entity_registry().name_id(variant_type_def_id));
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
            let raised_type_id = self.type_arena_mut().error_type(type_id);
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

        let fallible_info = self.type_arena().unwrap_fallible(inner_type_id);
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
        let arena = self.type_arena();
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

    /// Check destructuring and bind variables (TypeId version)
    fn check_record_destructuring_id(
        &mut self,
        ty_id: ArenaTypeId,
        fields: &[RecordFieldPattern],
        mutable: bool,
        _pattern_span: Span,
        init_span: Span,
        interner: &Interner,
    ) {
        // First check if this is a module type - if so, use module destructuring
        // Clone to avoid borrow conflicts with the mutable method call
        let module_info = self.type_arena().unwrap_module(ty_id).cloned();
        if let Some(module_info) = module_info {
            self.check_module_destructuring(&module_info, fields, mutable, init_span, interner);
            return;
        }

        // Get type_def_id from the type using arena (class only)
        let type_def_id = {
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            arena.unwrap_nominal(ty_id).and_then(|(id, _, kind)| {
                matches!(kind, NominalKind::Class | NominalKind::Struct).then_some(id)
            })
        };

        let Some(type_def_id) = type_def_id else {
            self.type_error_id("class, struct, or module", ty_id, init_span);
            return;
        };

        // Look up fields from entity_registry - clone to avoid borrow conflicts
        let generic_info_opt = self.entity_registry().type_generic_info(type_def_id);
        let Some(generic_info) = generic_info_opt else {
            self.type_error_id("class or struct with fields", ty_id, init_span);
            return;
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
                    self.name_table().last_segment_str(**name_id).as_deref() == Some(field_name_str)
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

    /// Check module destructuring and bind variables.
    /// Handles `let { A, B as C } = import "..."`.
    fn check_module_destructuring(
        &mut self,
        module_info: &crate::type_arena::InternedModule,
        fields: &[RecordFieldPattern],
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        // Get the module path for error messages
        let module_path = self
            .name_table()
            .module_path(module_info.module_id)
            .to_string();

        // Check each destructured field against module exports
        for field_pattern in fields {
            let export_name_str = interner.resolve(field_pattern.field_name);

            // Find the export by name in module_info.exports
            let found = module_info.exports.iter().find(|(name_id, _)| {
                self.name_table().last_segment_str(*name_id).as_deref() == Some(export_name_str)
            });

            if let Some((export_name_id, export_type_id)) = found {
                // Check if this is a generic function that needs special registration
                // Look up the function in the source module's EntityRegistry
                let source_func_id = self.entity_registry().function_by_name(*export_name_id);
                let generic_func_data = source_func_id.and_then(|func_id| {
                    let registry = self.entity_registry();
                    let func_def = registry.get_function(func_id);
                    func_def.generic_info.clone().map(|gi| {
                        (
                            gi,
                            func_def.signature.clone(),
                            func_def.required_params,
                            func_def.param_defaults.clone(),
                        )
                    })
                });
                if let Some((generic_info, signature, required_params, param_defaults)) =
                    generic_func_data
                {
                    // This is a generic function - register it in the current module
                    // under the binding name so call analysis can find it
                    let binding_name_id = self.name_table_mut().intern(
                        self.current_module,
                        &[field_pattern.binding],
                        interner,
                    );

                    // Register a copy of the function in the current module's namespace
                    let new_func_id = self.entity_registry_mut().register_function_full(
                        binding_name_id,
                        *export_name_id, // Keep original name for codegen lookup
                        self.current_module,
                        signature,
                        required_params,
                        param_defaults,
                    );
                    self.entity_registry_mut()
                        .set_function_generic_info(new_func_id, generic_info);
                }

                // Check if the export type is a class or interface type
                // If so, register a type alias so it's usable as a type name
                self.maybe_register_type_binding(field_pattern.binding, *export_type_id, interner);

                // Bind the export to the binding name
                self.scope.define(
                    field_pattern.binding,
                    Variable {
                        ty: *export_type_id,
                        mutable,
                    },
                );
                self.add_lambda_local(field_pattern.binding);
            } else {
                // Export not found
                self.add_error(
                    SemanticError::ModuleNoExport {
                        module: module_path.clone(),
                        name: export_name_str.to_string(),
                        span: field_pattern.span.into(),
                    },
                    field_pattern.span,
                );
            }
        }

        // Emit a warning if mutable is used with module destructuring
        if mutable {
            self.add_warning(
                SemanticWarning::MutableModuleBinding {
                    span: init_span.into(),
                },
                init_span,
            );
        }
    }

    /// Check if a type is a class or interface type and if so,
    /// register a type alias so it's usable as a type name in the current module.
    ///
    /// This enables patterns like:
    /// ```vole
    /// let { Duration } = import "std:time"
    /// let d = Duration { nanos: 1000 }  // Works as type name
    /// func foo(d: Duration) -> Duration { d }  // Works in type annotations
    /// ```
    fn maybe_register_type_binding(
        &mut self,
        binding_name: Symbol,
        type_id: ArenaTypeId,
        interner: &Interner,
    ) {
        use crate::entity_defs::TypeDefKind;

        // Check if the type is a class or interface
        let type_def_id = {
            let arena = self.type_arena();
            arena
                .unwrap_nominal(type_id)
                .map(|(def_id, _, _kind)| def_id)
        };

        let Some(original_type_def_id) = type_def_id else {
            return; // Not a class/interface type, nothing to register
        };

        // Don't create type aliases for generic types - they need proper handling
        // Generic types like Iterator<T> or MapLike<K, V> can't be aliased simply
        // because the alias wouldn't carry the type parameters
        let is_generic = !self
            .entity_registry()
            .get_type(original_type_def_id)
            .type_params
            .is_empty();
        if is_generic {
            return; // Skip generic types
        }

        // Create a type alias in the current module pointing to the original type
        // First, intern the binding name in the current module's namespace
        let binding_name_id =
            self.name_table_mut()
                .intern(self.current_module, &[binding_name], interner);

        // Check if a type with this name already exists in the current module
        if self
            .entity_registry()
            .type_by_name(binding_name_id)
            .is_some()
        {
            // Type already exists (possibly from a previous import or local definition)
            // Don't create a duplicate
            return;
        }

        // Register a new type alias that points to the original type
        let alias_type_def_id = self.entity_registry_mut().register_type(
            binding_name_id,
            TypeDefKind::Alias,
            self.current_module,
        );

        // Set the aliased type to the original class/interface type
        self.entity_registry_mut()
            .set_aliased_type(alias_type_def_id, type_id);
    }
}
