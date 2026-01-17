use super::super::*;
use crate::sema::types::LegacyType;

impl Analyzer {
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
            let arg_ty = if with_inference {
                // For lambda arguments, pass expected function type for inference
                if let ExprKind::Lambda(lambda) = &arg.kind {
                    let expected_fn = if let LegacyType::Function(ft) = param_ty {
                        Some(ft)
                    } else {
                        None
                    };
                    self.analyze_lambda(lambda, expected_fn, interner)
                } else {
                    // Pass expected type to allow integer literal inference
                    self.check_expr_expecting(arg, Some(param_ty), interner)?
                }
            } else {
                self.check_expr(arg, interner)?
            };

            // Convert to TypeId for compatibility check (Phase 2 migration)
            let arg_ty_id = self.type_to_id(&arg_ty);
            let param_ty_id = self.type_to_id(param_ty);
            if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
            }
        }

        Ok(())
    }
}
