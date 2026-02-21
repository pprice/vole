// src/sema/analyzer/stmt/mod.rs
//
// Statement checking: main router (check_stmt), block checking,
// and control flow analysis helpers.

mod destructuring;
mod error_handling;

use super::*;
use crate::type_arena::TypeId as ArenaTypeId;

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
            // These statements don't guarantee a return from the function
            Stmt::Let(_)
            | Stmt::LetTuple(_)
            | Stmt::While(_)
            | Stmt::For(_)
            | Stmt::Break(_)
            | Stmt::Continue(_) => false,
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
            Stmt::Let(let_stmt) => self.check_let_stmt(let_stmt, interner),
            Stmt::Expr(expr_stmt) => self.check_expr_stmt(expr_stmt, interner),
            Stmt::While(while_stmt) => self.check_while_stmt(while_stmt, interner),
            Stmt::If(if_stmt) => self.check_if_stmt(if_stmt, interner),
            Stmt::For(for_stmt) => self.check_for_stmt(for_stmt, interner),
            Stmt::Break(_) => {
                // Could check we're in a loop, but skipping for Phase 1
                Ok(ReturnInfo::default())
            }
            Stmt::Continue(_) => {
                // Could validate we're in a loop, skip for now
                Ok(ReturnInfo::default())
            }
            Stmt::Return(ret) => self.check_return_stmt(ret, interner),
            Stmt::Raise(raise_stmt) => {
                self.analyze_raise_stmt(raise_stmt, interner);
                Ok(ReturnInfo {
                    definitely_returns: true,
                    return_types: vec![],
                })
            }
            Stmt::LetTuple(let_tuple) => self.check_let_tuple_stmt(let_tuple, interner),
        }
    }

    /// Check a let statement with expression or type alias initializer.
    fn check_let_stmt(
        &mut self,
        let_stmt: &LetStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        match &let_stmt.init {
            LetInit::Expr(init_expr) => {
                self.check_let_expr_init(let_stmt, init_expr, interner)?;
            }
            LetInit::TypeAlias(type_expr) => {
                // Type alias: let Numeric = i32 | i64
                let aliased_type_id = self.resolve_type_id(type_expr, interner);
                self.register_type_alias_id(
                    let_stmt.name,
                    aliased_type_id,
                    interner,
                    let_stmt.span,
                );
            }
        }
        Ok(ReturnInfo::default())
    }

    /// Check a let statement with an expression initializer.
    fn check_let_expr_init(
        &mut self,
        let_stmt: &LetStmt,
        init_expr: &Expr,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Check for ambiguous type alias: let Alias = TypeName
        self.check_ambiguous_type_alias(let_stmt, init_expr, interner);

        // Validate type annotation first to emit errors for unknown types
        if let Some(ty) = &let_stmt.ty {
            self.validate_type_annotation(ty, let_stmt.span, interner, None);
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
            self.results
                .declared_var_types
                .insert(init_expr.id, decl_type_id);
        }

        // For recursive lambdas: if lambda has fully explicit types,
        // pre-register the variable so it's in scope during body analysis.
        let preregistered = self.try_preregister_recursive_lambda(let_stmt, init_expr, interner);

        let init_type_id = self.check_expr_expecting_id(init_expr, declared_type_id, interner)?;

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
            self.register_type_alias_id(let_stmt.name, aliased_type_id, interner, let_stmt.span);
        }

        // Only define if not already pre-registered for recursion
        if !preregistered {
            self.env.scope.define(
                let_stmt.name,
                Variable {
                    ty: var_type_id,
                    mutable: let_stmt.mutable,
                    declaration_span: let_stmt.span,
                },
            );
        }
        // Track as a local if inside a lambda (even if preregistered)
        // This is needed so nested functions aren't incorrectly marked as captures
        self.add_lambda_local(let_stmt.name);

        // Track lambda variables for default parameter support
        if let ExprKind::Lambda(lambda) = &init_expr.kind {
            let required_params = Self::lambda_required_params(lambda);
            let param_names: Vec<String> = lambda
                .params
                .iter()
                .map(|p| interner.resolve(p.name).to_string())
                .collect();
            self.lambda
                .variables
                .insert(let_stmt.name, (init_expr.id, required_params, param_names));
        } else {
            // Remove stale entry if this variable shadows a lambda
            // from a different scope (e.g. same-named local in another function)
            self.lambda.variables.remove(&let_stmt.name);
        }

        Ok(())
    }

    /// Check for ambiguous type alias: let Alias = TypeName
    /// where TypeName is a type but syntax is ambiguous.
    /// Sentinel types are excluded because bare-name construction is valid.
    fn check_ambiguous_type_alias(
        &mut self,
        let_stmt: &LetStmt,
        init_expr: &Expr,
        interner: &Interner,
    ) {
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
    }

    /// For recursive lambdas: if lambda has fully explicit types,
    /// pre-register the variable so it's in scope during body analysis.
    /// Returns true if the variable was pre-registered.
    fn try_preregister_recursive_lambda(
        &mut self,
        let_stmt: &LetStmt,
        init_expr: &Expr,
        interner: &Interner,
    ) -> bool {
        if let ExprKind::Lambda(lambda) = &init_expr.kind
            && let Some(fn_type_id) = self.lambda_explicit_type_id(lambda, interner)
        {
            self.env.scope.define(
                let_stmt.name,
                Variable {
                    ty: fn_type_id,
                    mutable: let_stmt.mutable,
                    declaration_span: let_stmt.span,
                },
            );
            return true;
        }
        false
    }

    /// Check an expression statement.
    fn check_expr_stmt(
        &mut self,
        expr_stmt: &ExprStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
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

        Ok(ReturnInfo::default())
    }

    /// Check a while loop statement.
    fn check_while_stmt(
        &mut self,
        while_stmt: &WhileStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        let cond_type_id = self.check_expr(&while_stmt.condition, interner)?;
        if !self.is_bool_compatible_id(cond_type_id) {
            let found = self.type_display_id(cond_type_id);
            self.add_error(
                SemanticError::ConditionNotBool {
                    found,
                    span: while_stmt.condition.span.into(),
                },
                while_stmt.condition.span,
            );
        }

        self.push_scope();
        // While loop body may never execute, so we collect return_types
        // but don't propagate definitely_returns
        let body_info = self.check_block(&while_stmt.body, interner)?;
        let _ = body_info; // Return info from loops handled in v-2602
        self.pop_scope();

        Ok(ReturnInfo::default())
    }

    /// Check an if statement with optional else branch.
    fn check_if_stmt(
        &mut self,
        if_stmt: &IfStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        let cond_type_id = self.check_expr(&if_stmt.condition, interner)?;
        if !self.is_bool_compatible_id(cond_type_id) {
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
        let saved_overrides = self.env.type_overrides.clone();

        // Then branch (with narrowing if applicable)
        self.push_scope();
        if let Some((sym, narrowed_type_id, _)) = &narrowing_info {
            self.env.type_overrides.insert(*sym, *narrowed_type_id);
        }
        let then_info = self.check_block(&if_stmt.then_branch, interner)?;
        self.pop_scope();

        // Restore overrides for else branch
        self.env.type_overrides = saved_overrides.clone();

        // Check else branch if present
        let (else_info, has_else) = if let Some(else_branch) = &if_stmt.else_branch {
            let parent = std::mem::take(&mut self.env.scope);
            self.env.scope = Scope::with_parent(parent);

            // Apply else-branch narrowing: if x is T, else branch has x: (original - T)
            if let Some((sym, tested_type_id, Some(original_type_id))) = &narrowing_info
                && let Some(else_narrowed) =
                    self.compute_else_narrowed_type(*tested_type_id, *original_type_id)
            {
                self.env.type_overrides.insert(*sym, else_narrowed);
            }

            let info = self.check_block(else_branch, interner)?;
            if let Some(parent) = std::mem::take(&mut self.env.scope).into_parent() {
                self.env.scope = parent;
            }
            (info, true)
        } else {
            // No else branch means the if might not execute, so definitely_returns is false
            (ReturnInfo::default(), false)
        };

        // Restore original overrides after the entire if statement
        self.env.type_overrides = saved_overrides;

        // Aggregate return info from both branches:
        // - definitely_returns only if BOTH branches return AND there is an else branch
        // - collect return_types from both branches
        let mut return_types = then_info.return_types;
        return_types.extend(else_info.return_types);

        Ok(ReturnInfo {
            definitely_returns: has_else
                && then_info.definitely_returns
                && else_info.definitely_returns,
            return_types,
        })
    }

    /// Check a for loop statement.
    fn check_for_stmt(
        &mut self,
        for_stmt: &ForStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
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
            } else if let Some(elem_id) = self.extract_iterable_element_type_id(iterable_ty_id) {
                // Type implements Iterable<T> — for-in will call .iter() at codegen.
                // Pre-create RuntimeIterator<T> so codegen can look it up.
                self.type_arena_mut().runtime_iterator(elem_id);
                elem_id
            } else {
                self.type_error_id(
                    "iterable (range, array, string, Iterator<T>, or Iterable<T>)",
                    iterable_ty_id,
                    for_stmt.iterable.span,
                );
                self.ty_invalid_id()
            }
        };

        self.push_scope();
        self.env.scope.define(
            for_stmt.var_name,
            Variable {
                ty: elem_ty_id,
                mutable: false,
                declaration_span: for_stmt.span,
            },
        );
        self.add_lambda_local(for_stmt.var_name);

        // For loop body may never execute, so we collect return_types
        // but don't propagate definitely_returns
        let body_info = self.check_block(&for_stmt.body, interner)?;
        let _ = body_info; // Return info from loops handled in v-2602

        self.pop_scope();

        Ok(ReturnInfo::default())
    }

    /// Check a return statement.
    fn check_return_stmt(
        &mut self,
        ret: &ReturnStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        // Determine expected type for type checking (TypeId-based)
        // Only use expected type if we're NOT in inference mode (current_function_return is set)
        let expected_value_type_id = self.env.current_function_return.map(|expected| {
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

        Ok(ReturnInfo {
            definitely_returns: true,
            return_types: vec![(ret_type_id, ret_value_span)],
        })
    }

    /// Check a let-tuple destructuring statement.
    fn check_let_tuple_stmt(
        &mut self,
        let_tuple: &LetTupleStmt,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
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

        Ok(ReturnInfo::default())
    }
}
