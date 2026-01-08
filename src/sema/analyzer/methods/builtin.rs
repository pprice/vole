use super::super::*;

impl Analyzer {
    /// Check if a method call is a built-in method on a primitive type
    /// Returns Some(function_type) if handled, None if not a built-in
    pub(crate) fn check_builtin_method(
        &mut self,
        object_type: &Type,
        method_name: &str,
        args: &[Expr],
        interner: &Interner,
    ) -> Option<FunctionType> {
        let method_type = |params: Vec<Type>, return_type: Type| FunctionType {
            params,
            return_type: Box::new(return_type),
            is_closure: false,
        };

        match (object_type, method_name) {
            // Array.length() -> i64
            (Type::Array(_), "length") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(method_type(vec![], Type::I64))
            }
            // Array.iter() -> Iterator<T>
            (Type::Array(elem_ty), "iter") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                let iter_type =
                    self.interface_type("Iterator", vec![*elem_ty.clone()], interner)?;
                Some(method_type(vec![], iter_type))
            }
            // String.length() -> i64
            (Type::String, "length") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(method_type(vec![], Type::I64))
            }
            _ => None,
        }
    }
}
