use super::super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::LegacyType;

impl Analyzer {
    /// Check call arguments against expected parameter types (TypeId version).
    ///
    /// This version takes TypeIds directly and avoids LegacyType conversion.
    /// Use this for simple call checking without type inference.
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
            let arg_ty_id = self.check_expr(arg, interner)?;
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
            // Get argument type as TypeId, avoiding LegacyType round-trip where possible
            let arg_ty_id = if with_inference {
                // For lambda arguments, pass expected function type for inference
                if let ExprKind::Lambda(lambda) = &arg.kind {
                    let expected_fn = if let LegacyType::Function(ft) = param_ty {
                        Some(ft)
                    } else {
                        None
                    };
                    let arg_ty = self.analyze_lambda(lambda, expected_fn, interner);
                    self.type_to_id(&arg_ty)
                } else {
                    // Pass expected type to allow integer literal inference
                    let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                    self.type_to_id(&arg_ty)
                }
            } else {
                // No inference needed - just check and keep TypeId directly
                self.check_expr(arg, interner)?
            };

            // Check compatibility using TypeId
            let param_ty_id = self.type_to_id(param_ty);
            if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
            }
        }

        Ok(())
    }
}
