use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::ast::CallArg;

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
    /// resolved arg-index mapping in `self.results.resolved_call_args` for codegen.
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
                let arg_ty_id = self.check_expr_expecting_id(expr, Some(param_ty_id), interner)?;
                if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
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
                let arg_ty_id = self.check_expr_expecting_id(expr, Some(param_ty_id), interner)?;
                if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
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
    /// `self.results.resolved_call_args` for codegen to use when emitting the call.
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
                    .resolved_call_args
                    .insert(call_node_id, mapping);
            }
        }

        Ok(return_type_id)
    }
}
