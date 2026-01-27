use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check identifier expression.
    /// Resolves variables, functions, and handles captures in lambdas.
    pub(super) fn check_identifier_expr(
        &mut self,
        expr: &Expr,
        sym: Symbol,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check for 'self' usage in static method
        let name_str = interner.resolve(sym);
        if name_str == "self"
            && let Some(ref method_name) = self.current_static_method
        {
            self.add_error(
                SemanticError::SelfInStaticMethod {
                    method: method_name.clone(),
                    span: expr.span.into(),
                },
                expr.span,
            );
            return Ok(ArenaTypeId::INVALID);
        }

        // Use get_variable_type to respect flow-sensitive narrowing
        if let Some(ty_id) = self.get_variable_type_id(sym) {
            // Check if this is a capture (inside lambda, not a local)
            if self.in_lambda() && !self.is_lambda_local(sym) {
                // Look up variable info to get mutability
                if let Some(var) = self.scope.get(sym) {
                    self.record_capture(sym, var.mutable);
                }
            }
            Ok(ty_id)
        } else if let Some(func_type) = self.get_function_type(sym, interner) {
            // Identifier refers to a function - treat it as a function value
            // When a named function is used as a value, it becomes a closure type
            // (is_closure: true) because codegen wraps it in a closure struct.
            // This allows codegen to use the type directly without creating it.
            let params_id = &func_type.params_id;
            let return_id = func_type.return_type_id;
            Ok(self.type_arena_mut().function(
                params_id.clone(),
                return_id,
                true, // Always closure when used as a value
            ))
        } else {
            let name = interner.resolve(sym);
            self.add_error(
                SemanticError::UndefinedVariable {
                    name: name.to_string(),
                    span: expr.span.into(),
                },
                expr.span,
            );
            Ok(ArenaTypeId::INVALID)
        }
    }
}
