use super::super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::LegacyType;

impl Analyzer {
    /// Check call arguments against expected parameter types (TypeId version).
    ///
    /// This version takes TypeIds directly and avoids LegacyType conversion.
    /// Uses check_expr_expecting_id for inference (integer literals, union coercion).
    pub(crate) fn check_call_args_id(
        &mut self,
        args: &[Expr],
        param_type_ids: &[ArenaTypeId],
        return_type_id: ArenaTypeId,
        call_span: Span,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check argument count
        if args.len() != param_type_ids.len() {
            self.add_wrong_arg_count(param_type_ids.len(), args.len(), call_span);
        }

        // Check each argument against its expected parameter type
        for (arg, &param_ty_id) in args.iter().zip(param_type_ids.iter()) {
            // Use check_expr_expecting_id to enable integer literal inference
            // and union type coercion (e.g., passing i32 literal to union param)
            let arg_ty_id = self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?;
            if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
            }
        }

        Ok(return_type_id)
    }

    /// Check call arguments against expected parameter types.
    ///
    /// This helper unifies the argument checking logic used for:
    /// - Named function calls
    /// - Function-typed variable calls
    /// - Expression calls (e.g., immediately invoked lambdas)
    ///
    /// If `with_inference` is true, uses `check_expr_expecting` for argument type checking,
    /// enabling integer literal inference and lambda parameter inference. Otherwise uses
    /// plain `check_expr` (for cases where type inference context isn't available).
    pub(crate) fn check_call_args(
        &mut self,
        args: &[Expr],
        param_types: &[LegacyType],
        call_span: Span,
        with_inference: bool,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Check argument count
        if args.len() != param_types.len() {
            self.add_wrong_arg_count(param_types.len(), args.len(), call_span);
        }

        // Check each argument against its expected parameter type
        for (arg, param_ty) in args.iter().zip(param_types.iter()) {
            // Convert param type to TypeId once
            let param_ty_id = self.type_to_id(param_ty);

            // Get argument type as TypeId
            let arg_ty_id = if with_inference {
                // For lambda arguments, pass expected function type for inference
                if let ExprKind::Lambda(lambda) = &arg.kind {
                    let expected_fn = if let LegacyType::Function(ft) = param_ty {
                        Some(ft)
                    } else {
                        None
                    };
                    self.analyze_lambda(lambda, expected_fn, interner)
                } else {
                    // Use TypeId-based expecting to avoid unnecessary conversions
                    self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?
                }
            } else {
                // No inference needed - just check and keep TypeId directly
                self.check_expr(arg, interner)?
            };

            // Check compatibility using TypeId
            if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
            }
        }

        Ok(())
    }
}
