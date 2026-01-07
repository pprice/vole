use super::super::*;

impl Analyzer {
    pub(super) fn check_call_expr(
        &mut self,
        expr: &Expr,
        call: &CallExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // Handle assert specially
        if self.is_assert_call(&call.callee, interner) {
            // Assert is an impure builtin - mark side effects if inside lambda
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }

            if call.args.len() != 1 {
                self.add_error(
                    SemanticError::WrongArgumentCount {
                        expected: 1,
                        found: call.args.len(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
                return Ok(Type::Void);
            }

            let arg_ty = self.check_expr(&call.args[0], interner)?;
            if arg_ty != Type::Bool && arg_ty != Type::Error {
                let found = self.type_display(&arg_ty, interner);
                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "bool".to_string(),
                        found,
                        span: call.args[0].span.into(),
                    },
                    call.args[0].span,
                );
            }

            return Ok(Type::Void);
        }

        if let ExprKind::Identifier(sym) = &call.callee.kind {
            // First check if it's a top-level function
            if let Some(func_type) = self.functions.get(sym).cloned() {
                // Calling a user-defined function - conservatively mark side effects
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                self.check_call_args(
                    &call.args,
                    &func_type.params,
                    expr.span,
                    true, // with_inference
                    interner,
                )?;
                return Ok(*func_type.return_type);
            }

            // Check if it's a generic function
            if let Some(generic_def) = self.generic_functions.get(sym).cloned() {
                // Calling a generic function - infer type params and monomorphize
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }

                // First, type-check the arguments to get their types
                let arg_types: Vec<Type> = call
                    .args
                    .iter()
                    .map(|arg| self.check_expr(arg, interner))
                    .collect::<Result<Vec<_>, _>>()?;

                // Infer type parameters from argument types
                let inferred = self.infer_type_params(
                    &generic_def.type_params,
                    &generic_def.param_types,
                    &arg_types,
                );

                // Create the concrete function type by substituting
                let concrete_params: Vec<Type> = generic_def
                    .param_types
                    .iter()
                    .map(|t| substitute_type(t, &inferred))
                    .collect();
                let concrete_return = substitute_type(&generic_def.return_type, &inferred);

                // Check arg count
                if call.args.len() != concrete_params.len() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: concrete_params.len(),
                            found: call.args.len(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(Type::Error);
                }

                // Type check arguments against concrete params
                for (i, (arg, expected)) in call.args.iter().zip(concrete_params.iter()).enumerate()
                {
                    let arg_ty = &arg_types[i];
                    if !types_compatible_core(arg_ty, expected) {
                        let expected = self.type_display(expected, interner);
                        let found = self.type_display(arg_ty, interner);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected,
                                found,
                                span: arg.span.into(),
                            },
                            arg.span,
                        );
                    }
                }

                // Get or create monomorphized instance
                let type_args: Vec<Type> = generic_def
                    .type_params
                    .iter()
                    .filter_map(|tp| inferred.get(&tp.name).cloned())
                    .collect();
                let type_keys = type_args.iter().map(|ty| self.type_key_for(ty)).collect();
                let name_id = self
                    .name_table
                    .intern(self.name_table.main_module(), &[*sym]);
                let key = MonomorphKey::new(name_id, type_keys);

                if !self.monomorph_cache.contains(&key) {
                    let id = self.monomorph_cache.next_unique_id();
                    let module_id = self.name_table.module_of(name_id);
                    let base_sym = self.name_table.last_symbol(name_id).unwrap_or(*sym);
                    let mangled = format!("{}__mono_{}", interner.resolve(base_sym), id);
                    let mangled_name = self.name_table.intern_raw(module_id, &[mangled.as_str()]);
                    self.monomorph_cache.insert(
                        key.clone(),
                        MonomorphInstance {
                            original_name: name_id,
                            mangled_name,
                            instance_id: id,
                            func_type: FunctionType {
                                params: concrete_params,
                                return_type: Box::new(concrete_return.clone()),
                                is_closure: false,
                            },
                            substitutions: inferred,
                        },
                    );
                }

                // Record the call -> monomorph key mapping for codegen
                self.generic_calls.insert(expr.id, key);

                return Ok(concrete_return);
            }

            // Check if it's a variable with a function type
            if let Some(Type::Function(func_type)) = self.get_variable_type(*sym) {
                // Calling a function-typed variable - conservatively mark side effects
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                self.check_call_args(
                    &call.args,
                    &func_type.params,
                    expr.span,
                    true, // with_inference
                    interner,
                )?;
                return Ok(*func_type.return_type);
            }

            // Check if it's a variable with a functional interface type
            if let Some(Type::Interface(iface)) = self.get_variable_type(*sym)
                && let Some(func_type) = self.get_functional_interface_type(iface.name, interner)
            {
                // Calling a functional interface - treat like a closure call
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                self.check_call_args(
                    &call.args,
                    &func_type.params,
                    expr.span,
                    true, // with_inference
                    interner,
                )?;
                return Ok(*func_type.return_type);
            }

            // Check if it's a known builtin function
            let name = interner.resolve(*sym);
            if name == "println" || name == "print_char" || name == "flush" || name == "print" {
                // Impure builtins - mark side effects if inside lambda
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                for arg in &call.args {
                    self.check_expr(arg, interner)?;
                }
                return Ok(Type::Void);
            }

            // Check if it's a variable with a non-function type
            if let Some(var_ty) = self.get_variable_type(*sym) {
                let ty = self.type_display(&var_ty, interner);
                self.add_error(
                    SemanticError::NotCallable {
                        ty,
                        span: call.callee.span.into(),
                    },
                    call.callee.span,
                );
                // Still check args for more errors
                for arg in &call.args {
                    self.check_expr(arg, interner)?;
                }
                return Ok(Type::Error);
            }

            // Unknown identifier - might be an undefined function
            // (will be caught by codegen or other checks)
            for arg in &call.args {
                self.check_expr(arg, interner)?;
            }
            return Ok(Type::Void);
        }

        // Non-identifier callee (e.g., a lambda expression being called directly)
        let callee_ty = self.check_expr(&call.callee, interner)?;
        if let Type::Function(func_type) = callee_ty {
            // Calling a function-typed expression - conservatively mark side effects
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }
            self.check_call_args(
                &call.args,
                &func_type.params,
                expr.span,
                false, // without inference (callee was just an expression)
                interner,
            )?;
            return Ok(*func_type.return_type);
        }

        // Non-callable type
        if callee_ty != Type::Error {
            let ty = self.type_display(&callee_ty, interner);
            self.add_error(
                SemanticError::NotCallable {
                    ty,
                    span: call.callee.span.into(),
                },
                call.callee.span,
            );
        }
        Ok(Type::Error)
    }
}
