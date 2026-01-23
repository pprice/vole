use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check call arguments against expected parameter types.
    ///
    /// Uses check_expr_expecting_id for inference (integer literals, union coercion).
    pub(crate) fn check_call_args_id(
        &mut self,
        args: &[Expr],
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
            interner,
        )
    }

    /// Check call arguments against expected parameter types, allowing omission of defaulted params.
    ///
    /// `required_params` is the number of parameters that must be provided (no defaults).
    /// Parameters from `required_params` up to `param_type_ids.len()` have default values.
    ///
    /// Uses check_expr_expecting_id for inference (integer literals, union coercion).
    pub(crate) fn check_call_args_with_defaults_id(
        &mut self,
        args: &[Expr],
        param_type_ids: &[ArenaTypeId],
        required_params: usize,
        return_type_id: ArenaTypeId,
        call_span: Span,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let total_params = param_type_ids.len();

        // Check argument count: must be at least required_params and at most total_params
        if args.len() < required_params || args.len() > total_params {
            self.add_wrong_arg_count_range(required_params, total_params, args.len(), call_span);
        }

        // Check each provided argument against its expected parameter type
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
}
