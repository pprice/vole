use super::super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;

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
}
