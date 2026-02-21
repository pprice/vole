use super::super::*;
use crate::expression_data::ItLambdaInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::ast::{CallArg, FuncBody, LambdaExpr, LambdaParam, StringPart};

/// Context for resolving named call arguments.
///
/// When all args are positional, pass `None` for `param_names` to skip named-arg
/// processing. When Some, the validator checks ordering, unknown names, duplicates,
/// and missing required args, and stores a `resolved_call_args` mapping for codegen.
pub(crate) struct NamedArgContext<'a> {
    /// Parameter names in declaration order (excluding `self`).
    pub param_names: &'a [String],
    /// Whether this function is an external (FFI) function.
    /// Named arguments are rejected for external functions.
    pub is_external: bool,
    /// The NodeId of the call expression. Used to key `resolved_call_args`.
    pub call_node_id: NodeId,
}

impl Analyzer {
    /// Check call arguments against expected parameter types.
    ///
    /// Uses check_expr_expecting_id for inference (integer literals, union coercion).
    pub(crate) fn check_call_args_id(
        &mut self,
        args: &[CallArg],
        param_type_ids: &[ArenaTypeId],
        return_type_id: ArenaTypeId,
        call_span: Span,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check with all params required (no defaults)
        self.check_call_args_with_defaults_id(
            args,
            param_type_ids,
            param_type_ids.len(), // required_params = total params (no defaults)
            return_type_id,
            call_span,
            None,
            interner,
        )
    }

    /// Check call arguments with named arg support.
    ///
    /// Like `check_call_args_with_defaults_id`, but also validates and resolves
    /// named arguments, storing the resolved mapping for codegen.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_call_args_named_id(
        &mut self,
        args: &[CallArg],
        param_type_ids: &[ArenaTypeId],
        required_params: usize,
        return_type_id: ArenaTypeId,
        call_span: Span,
        named_ctx: NamedArgContext<'_>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        self.check_call_args_with_defaults_id(
            args,
            param_type_ids,
            required_params,
            return_type_id,
            call_span,
            Some(named_ctx),
            interner,
        )
    }

    /// Check call arguments against expected parameter types, allowing omission of defaulted params.
    ///
    /// `required_params` is the number of parameters that must be provided (no defaults).
    /// Parameters from `required_params` up to `param_type_ids.len()` have default values.
    ///
    /// When `named_ctx` is Some, validates and resolves named arguments and stores the
    /// resolved arg-index mapping in `self.results.node_map (resolved_call_args)` for codegen.
    ///
    /// Uses check_expr_expecting_id for inference (integer literals, union coercion).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_call_args_with_defaults_id(
        &mut self,
        args: &[CallArg],
        param_type_ids: &[ArenaTypeId],
        required_params: usize,
        return_type_id: ArenaTypeId,
        call_span: Span,
        named_ctx: Option<NamedArgContext<'_>>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let total_params = param_type_ids.len();
        let has_named = args.iter().any(|a| matches!(a, CallArg::Named { .. }));

        // Fast path: all positional, no named arg context needed
        if !has_named {
            // Check argument count: must be at least required_params and at most total_params
            if args.len() < required_params || args.len() > total_params {
                self.add_wrong_arg_count_range(
                    required_params,
                    total_params,
                    args.len(),
                    call_span,
                );
            }

            // Check each provided argument against its expected parameter type.
            for (arg, &param_ty_id) in args.iter().zip(param_type_ids.iter()) {
                let expr = arg.expr();
                // Try implicit `it` lambda synthesis before normal type checking
                if let Some(arg_ty_id) = self.try_check_as_it_lambda(expr, param_ty_id, interner) {
                    // Record the synthesized type for the expression node
                    self.record_expr_type_id(expr, arg_ty_id);
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                    }
                } else {
                    let arg_ty_id =
                        self.check_expr_expecting_id(expr, Some(param_ty_id), interner)?;
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                    }
                }
            }

            return Ok(return_type_id);
        }

        // Named args are present. Validate and resolve.
        if let Some(ctx) = named_ctx {
            self.check_call_args_with_named(
                args,
                param_type_ids,
                required_params,
                return_type_id,
                call_span,
                ctx,
                interner,
            )
        } else {
            // No context provided (e.g., lambda call, functional interface).
            // Fall back to positional treatment but still type-check.
            if args.len() < required_params || args.len() > total_params {
                self.add_wrong_arg_count_range(
                    required_params,
                    total_params,
                    args.len(),
                    call_span,
                );
            }
            for (arg, &param_ty_id) in args.iter().zip(param_type_ids.iter()) {
                let expr = arg.expr();
                // Try implicit `it` lambda synthesis before normal type checking
                if let Some(arg_ty_id) = self.try_check_as_it_lambda(expr, param_ty_id, interner) {
                    self.record_expr_type_id(expr, arg_ty_id);
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                    }
                } else {
                    let arg_ty_id =
                        self.check_expr_expecting_id(expr, Some(param_ty_id), interner)?;
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                    }
                }
            }
            Ok(return_type_id)
        }
    }

    /// Core named-argument validation and resolution.
    ///
    /// Validates:
    /// 1. Named args not allowed on external (FFI) functions (E2113)
    /// 2. All positional args must precede all named args (E2114)
    /// 3. Named arg name must match a known parameter (E2115)
    /// 4. No slot may be filled both positionally and by name (E2116)
    /// 5. All required params must be filled (E2117)
    ///
    /// After validation, produces a `Vec<Option<usize>>` of length `total_params` where
    /// entry `i` = `Some(j)` means `call.args[j]` fills slot `i`, and `None` means
    /// the slot uses its default value.  The mapping is stored in
    /// `self.results.node_map (resolved_call_args)` for codegen to use when emitting the call.
    #[allow(clippy::too_many_arguments)]
    fn check_call_args_with_named(
        &mut self,
        args: &[CallArg],
        param_type_ids: &[ArenaTypeId],
        required_params: usize,
        return_type_id: ArenaTypeId,
        call_span: Span,
        ctx: NamedArgContext<'_>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let total_params = param_type_ids.len();
        let NamedArgContext {
            param_names,
            is_external,
            call_node_id,
        } = ctx;

        // Rule 1: Named args not allowed for external functions.
        if is_external
            && let Some(named_arg) = args.iter().find(|a| matches!(a, CallArg::Named { .. }))
        {
            let span = match named_arg {
                CallArg::Named { span, .. } => *span,
                _ => call_span,
            };
            self.add_error(
                SemanticError::ExternalFunctionNamedArg { span: span.into() },
                span,
            );
            // Still type-check positionally to avoid cascading errors.
            for (arg, &param_ty_id) in args.iter().zip(param_type_ids.iter()) {
                let expr = arg.expr();
                let _ = self.check_expr_expecting_id(expr, Some(param_ty_id), interner);
            }
            return Ok(return_type_id);
        }

        // Rule 2: All positional args must precede named args.
        // Find first named arg index.
        let first_named_idx = args
            .iter()
            .position(|a| matches!(a, CallArg::Named { .. }))
            .unwrap_or(args.len());
        let first_named_span = match &args[first_named_idx] {
            CallArg::Named { span, .. } => *span,
            _ => call_span,
        };
        // Check if any positional arg comes after the first named arg.
        for (_i, arg) in args.iter().enumerate().skip(first_named_idx + 1) {
            if let CallArg::Positional(expr) = arg {
                self.add_error(
                    SemanticError::PositionalArgAfterNamed {
                        span: expr.span.into(),
                        named_span: first_named_span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Number of positional args (everything before the first named arg).
        let positional_count = first_named_idx;

        // Too many positional args (excess positional before named).
        if positional_count > total_params {
            self.add_wrong_arg_count_range(required_params, total_params, args.len(), call_span);
            // Still type-check what we can.
            for (arg, &param_ty_id) in args.iter().zip(param_type_ids.iter()) {
                let expr = arg.expr();
                let _ = self.check_expr_expecting_id(expr, Some(param_ty_id), interner);
            }
            return Ok(return_type_id);
        }

        // Build the resolved mapping: slot -> Option<call_args_index>
        // None means: use the default value for that slot.
        let mut mapping: Vec<Option<usize>> = vec![None; total_params];

        // Fill positional slots.
        for (i, slot) in mapping.iter_mut().enumerate().take(positional_count) {
            *slot = Some(i);
        }

        // Track which slots are already filled (positionally) to detect duplicates.
        let mut slot_filled = vec![false; total_params];
        for filled in slot_filled.iter_mut().take(positional_count) {
            *filled = true;
        }

        // Rule 3 & 4: Resolve named args to slots.
        let mut had_validation_error = false;
        for (call_arg_idx, arg) in args.iter().enumerate().skip(first_named_idx) {
            let (name_sym, arg_span) = match arg {
                CallArg::Named { name, span, .. } => (*name, *span),
                CallArg::Positional(_) => continue, // Already reported positional-after-named above
            };
            let name_str = interner.resolve(name_sym);

            // Find the slot index for this name.
            let slot = param_names.iter().position(|n| n == name_str);
            let Some(slot) = slot else {
                // Rule 3: Unknown parameter name.
                self.add_error(
                    SemanticError::UnknownParamName {
                        name: name_str.to_string(),
                        span: arg_span.into(),
                    },
                    arg_span,
                );
                had_validation_error = true;
                continue;
            };

            // Rule 4: Slot already filled positionally.
            if slot_filled[slot] {
                let param_name = param_names[slot].clone();
                self.add_error(
                    SemanticError::DuplicateArg {
                        name: param_name,
                        span: arg_span.into(),
                    },
                    arg_span,
                );
                had_validation_error = true;
                continue;
            }

            mapping[slot] = Some(call_arg_idx);
            slot_filled[slot] = true;
        }

        // Rule 5: Check all required params are filled.
        for slot in 0..required_params {
            if !slot_filled[slot] {
                let param_name = if slot < param_names.len() {
                    param_names[slot].clone()
                } else {
                    format!("param_{slot}")
                };
                self.add_error(
                    SemanticError::MissingRequiredArg {
                        name: param_name,
                        span: call_span.into(),
                    },
                    call_span,
                );
                had_validation_error = true;
            }
        }

        // Check for too many args total (positional + named > total_params).
        // Only named args that resolved successfully count toward this.
        let named_filled = slot_filled[positional_count..]
            .iter()
            .filter(|&&f| f)
            .count();
        if positional_count + named_filled > total_params {
            self.add_wrong_arg_count_range(
                required_params,
                total_params,
                positional_count + named_filled,
                call_span,
            );
            had_validation_error = true;
        }

        // Type-check each argument in its resolved slot order.
        // Even if there were validation errors, type-check what we can to surface more issues.
        for (slot, &opt_call_idx) in mapping.iter().enumerate() {
            let Some(call_arg_idx) = opt_call_idx else {
                continue; // Default-filled slot — no type checking needed here
            };
            let arg = &args[call_arg_idx];
            let expr = arg.expr();
            if slot < param_type_ids.len() {
                let param_ty_id = param_type_ids[slot];
                // Try implicit `it` lambda synthesis before normal type checking
                if let Some(arg_ty_id) = self.try_check_as_it_lambda(expr, param_ty_id, interner) {
                    self.record_expr_type_id(expr, arg_ty_id);
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                    }
                } else {
                    match self.check_expr_expecting_id(expr, Some(param_ty_id), interner) {
                        Ok(arg_ty_id) => {
                            if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                                self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                            }
                        }
                        Err(errs) => {
                            for e in errs {
                                self.diagnostics.errors.push(e);
                            }
                        }
                    }
                }
            }
        }

        // Store the resolved mapping for codegen only if named args were actually used
        // and there were no fundamental validation errors that would corrupt the mapping.
        if !had_validation_error {
            // Only store if the mapping differs from purely positional order
            // (i.e., if any named arg was used or if arg order differs from slot order).
            let is_pure_positional = mapping
                .iter()
                .enumerate()
                .take(args.len())
                .all(|(i, opt)| *opt == Some(i))
                && mapping[args.len()..].iter().all(|opt| opt.is_none());

            if !is_pure_positional {
                self.results
                    .node_map
                    .set_resolved_call_args(call_node_id, mapping);
            }
        }

        Ok(return_type_id)
    }

    /// Check whether `expr` should be treated as an implicit `it => expr` lambda.
    ///
    /// Returns `Some(type_id)` when synthesis was performed (either successfully or
    /// with an error), `None` when normal type checking should proceed.
    ///
    /// Synthesis is triggered when:
    /// - `expected` is a single-parameter function type `(T) -> U`
    /// - `expr` is not already a lambda expression
    /// - `expr` contains `it` as an identifier
    /// - `it` is NOT currently bound in scope (would be a free reference)
    pub(crate) fn try_check_as_it_lambda(
        &mut self,
        expr: &Expr,
        expected: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        // Must not already be a lambda
        if matches!(expr.kind, ExprKind::Lambda(_)) {
            return None;
        }

        // Must have `it` in the interner (only present if user actually wrote "it")
        let it_sym = interner.lookup("it")?;

        // Check if expression contains `it` as a free identifier
        if !expr_contains_it(expr, it_sym) {
            return None;
        }

        // Expected type must be a function type with exactly 1 parameter
        let (param_types, ret_type) = {
            let arena = self.type_arena();
            let info = arena.unwrap_function(expected)?;
            if info.0.len() != 1 {
                return None;
            }
            (info.0.to_vec(), info.1)
        };

        // If `it` is already in scope as a variable, don't synthesize
        // (it's being used as a regular variable, not as the implicit param)
        if self.get_variable_type_id(it_sym).is_some() {
            return None;
        }

        // Nesting check: if already inside an implicit `it`-lambda, emit E2118
        if self.lambda.it_lambda_depth > 0 {
            self.add_error(
                SemanticError::ItInNestedLambda {
                    span: expr.span.into(),
                },
                expr.span,
            );
            return Some(ArenaTypeId::INVALID);
        }

        // Build expected function type for analyze_lambda
        let expected_fn = FunctionType::from_ids(&param_types, ret_type, false);

        // When the expected return type is void, wrap the expression in a block body
        // so the expression result is discarded (expression body always returns a value).
        let body = if ret_type.is_void() {
            FuncBody::Block(Block {
                stmts: vec![Stmt::Expr(ExprStmt {
                    expr: expr.clone(),
                    span: expr.span,
                })],
                span: expr.span,
            })
        } else {
            FuncBody::Expr(Box::new(expr.clone()))
        };

        // Synthesize: build a LambdaExpr with `it` as the single param
        let synthetic_lambda = LambdaExpr {
            type_params: vec![],
            params: vec![LambdaParam {
                name: it_sym,
                ty: None, // Type will be inferred from expected_fn
                default_value: None,
                span: expr.span,
            }],
            return_type: None,
            body,
            span: expr.span,
        };

        // Increment depth, analyze, decrement
        self.lambda.it_lambda_depth += 1;
        let lambda_ty =
            self.analyze_lambda(&synthetic_lambda, expr.id, Some(&expected_fn), interner);
        self.lambda.it_lambda_depth -= 1;

        // Store compact info so codegen can reconstruct the lambda
        self.results.node_map.set_it_lambda_info(
            expr.id,
            ItLambdaInfo {
                param_type: param_types[0],
                return_type: ret_type,
                body_node: expr.id,
            },
        );

        Some(lambda_ty)
    }
}

/// Walk an expression tree and return true if it contains `it_sym` as an Identifier.
/// This is a recursive check that covers all sub-expressions.
fn expr_contains_it(expr: &Expr, it_sym: Symbol) -> bool {
    match &expr.kind {
        ExprKind::Identifier(sym) => *sym == it_sym,
        ExprKind::Binary(bin) => {
            expr_contains_it(&bin.left, it_sym) || expr_contains_it(&bin.right, it_sym)
        }
        ExprKind::Unary(un) => expr_contains_it(&un.operand, it_sym),
        ExprKind::Call(call) => {
            expr_contains_it(&call.callee, it_sym)
                || call
                    .args
                    .iter()
                    .any(|a: &CallArg| expr_contains_it(a.expr(), it_sym))
        }
        ExprKind::Grouping(inner) => expr_contains_it(inner, it_sym),
        ExprKind::Index(idx) => {
            expr_contains_it(&idx.object, it_sym) || expr_contains_it(&idx.index, it_sym)
        }
        ExprKind::ArrayLiteral(elems) => elems.iter().any(|e| expr_contains_it(e, it_sym)),
        ExprKind::NullCoalesce(nc) => {
            expr_contains_it(&nc.value, it_sym) || expr_contains_it(&nc.default, it_sym)
        }
        ExprKind::Is(is_expr) => expr_contains_it(&is_expr.value, it_sym),
        ExprKind::StructLiteral(sl) => sl.fields.iter().any(|f| expr_contains_it(&f.value, it_sym)),
        ExprKind::InterpolatedString(parts) => parts.iter().any(|p| {
            if let StringPart::Expr(e) = p {
                expr_contains_it(e, it_sym)
            } else {
                false
            }
        }),
        // Method calls: check the object and all args
        ExprKind::MethodCall(mc) => {
            expr_contains_it(&mc.object, it_sym)
                || mc
                    .args
                    .iter()
                    .any(|a: &CallArg| expr_contains_it(a.expr(), it_sym))
        }
        // Field access: check the object
        ExprKind::FieldAccess(fa) => expr_contains_it(&fa.object, it_sym),
        ExprKind::OptionalChain(oc) => expr_contains_it(&oc.object, it_sym),
        ExprKind::OptionalMethodCall(omc) => {
            expr_contains_it(&omc.object, it_sym)
                || omc
                    .args
                    .iter()
                    .any(|a: &CallArg| expr_contains_it(a.expr(), it_sym))
        }
        ExprKind::Range(r) => {
            expr_contains_it(&r.start, it_sym) || expr_contains_it(&r.end, it_sym)
        }
        ExprKind::Try(inner) => expr_contains_it(inner, it_sym),
        ExprKind::Assign(assign) => expr_contains_it(&assign.value, it_sym),
        ExprKind::CompoundAssign(ca) => expr_contains_it(&ca.value, it_sym),
        // Lambda bodies are nested lambdas — don't descend into them for synthesis detection
        ExprKind::Lambda(_) => false,
        // Literals, TypeLiteral, Import, Unreachable, Yield, Block, If, When, Match
        // — skip for now; `it` in complex nested structures is less common
        _ => false,
    }
}
