// src/sema/analyzer/functions/mod.rs
//! Function and method checking: context management, body analysis, monomorphization.

mod monomorphization;

use super::*;

/// Saved state when entering a function/method check context.
/// Used by enter_function_context/exit_function_context for uniform save/restore.
pub(super) struct FunctionCheckContext {
    return_type: Option<ArenaTypeId>,
    error_type: Option<ArenaTypeId>,
    generator_element_type: Option<ArenaTypeId>,
    static_method: Option<String>,
    /// How many scopes were on the stack when we entered this context
    type_param_stack_depth: usize,
}

impl Analyzer {
    /// Enter a function/method check context, saving current state.
    /// Automatically sets return/error/generator types from return_type_id.
    /// For static methods, caller should set static_method and push type params after calling.
    pub(super) fn enter_function_context(
        &mut self,
        return_type_id: ArenaTypeId,
    ) -> FunctionCheckContext {
        let saved = FunctionCheckContext {
            return_type: self.env.current_function_return.take(),
            error_type: self.env.current_function_error_type.take(),
            generator_element_type: self.env.current_generator_element_type.take(),
            static_method: self.env.current_static_method.take(),
            type_param_stack_depth: self.env.type_param_stack.depth(),
        };

        self.env.current_function_return = Some(return_type_id);

        // Set error type context if this is a fallible function
        let error_type = self
            .type_arena()
            .unwrap_fallible(return_type_id)
            .map(|(_, e)| e);
        if let Some(error) = error_type {
            self.env.current_function_error_type = Some(error);
        }

        // Set generator context if return type is Iterator<T>
        if let Some(element_type_id) = self.extract_iterator_element_type_id(return_type_id) {
            self.env.current_generator_element_type = Some(element_type_id);
            // Pre-create RuntimeIterator(T) so codegen can look it up when
            // compiling generator functions (coroutine-backed iterators).
            self.type_arena_mut().runtime_iterator(element_type_id);
        }

        saved
    }

    /// Enter a function context for return type inference (no known return type).
    /// The first return statement will set current_function_return; subsequent returns check against it.
    pub(super) fn enter_function_context_inferring(&mut self) -> FunctionCheckContext {
        // current_function_return stays None to signal inference mode
        FunctionCheckContext {
            return_type: self.env.current_function_return.take(),
            error_type: self.env.current_function_error_type.take(),
            generator_element_type: self.env.current_generator_element_type.take(),
            static_method: self.env.current_static_method.take(),
            type_param_stack_depth: self.env.type_param_stack.depth(),
        }
    }

    /// Exit function/method check context, restoring saved state.
    pub(super) fn exit_function_context(&mut self, saved: FunctionCheckContext) {
        self.env.current_function_return = saved.return_type;
        self.env.current_function_error_type = saved.error_type;
        self.env.current_generator_element_type = saved.generator_element_type;
        self.env.current_static_method = saved.static_method;
        // Pop any scopes that were pushed during this context
        while self.env.type_param_stack.depth() > saved.type_param_stack_depth {
            self.env.type_param_stack.pop();
        }
    }

    /// Create a new scope and define function/method/lambda parameters in it.
    pub(super) fn enter_param_scope(&mut self, params: &[Param], type_ids: &[ArenaTypeId]) {
        self.push_scope();
        for (param, &ty_id) in params.iter().zip(type_ids.iter()) {
            self.env.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                    declaration_span: param.span,
                },
            );
        }
    }

    /// Infer the return type from collected return_types in ReturnInfo.
    ///
    /// This enables multi-branch return type inference:
    /// - If no return types collected, returns void
    /// - If one return type, returns that type
    /// - If multiple different return types, creates a union type
    ///
    /// Example: `func foo(x: bool) { if x { return 1 } else { return "hi" } }`
    /// will infer return type `i64 | string`.
    pub(super) fn infer_return_type_from_info(&mut self, info: &ReturnInfo) -> ArenaTypeId {
        if info.return_types.is_empty() {
            ArenaTypeId::VOID
        } else if info.return_types.len() == 1 {
            info.return_types[0].0
        } else {
            // Extract just the types for union creation
            let types: Vec<ArenaTypeId> = info.return_types.iter().map(|(ty, _)| *ty).collect();
            // Create union of all return types (the union method handles deduplication)
            self.type_arena_mut().union(types)
        }
    }

    pub(super) fn check_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Skip generic functions - they will be type-checked when monomorphized
        // This includes both explicitly generic functions (with type params in the AST)
        // and implicitly generified functions (with structural type parameters)
        // TODO: In M4+, we could type-check with abstract type params
        if !func.type_params.is_empty() {
            return Ok(());
        }

        // Also skip implicitly generified functions (structural types in parameters)
        // These have generic_info but no AST-level type_params
        let name_id =
            self.name_table_mut()
                .intern(self.module.current_module, &[func.name], interner);
        let has_generic_info = self
            .entity_registry()
            .function_by_name(name_id)
            .map(|func_id| {
                self.entity_registry()
                    .get_function(func_id)
                    .generic_info
                    .is_some()
            })
            .unwrap_or(false);
        if has_generic_info {
            return Ok(());
        }

        let func_type = self
            .symbols
            .functions
            .get(&func.name)
            .cloned()
            .expect("function registered in signature collection pass");

        // Determine if we need to infer the return type
        let needs_inference = func.return_type.is_none();

        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(func_type.return_type_id)
        };

        // Create new scope with parameters
        self.enter_param_scope(&func.params, &func_type.params_id);

        // Type-check parameter default expressions
        self.check_param_defaults(&func.params, &func_type.params_id, interner)?;

        // Check body
        let body_info = self.check_func_body(&func.body, interner)?;

        // If we were inferring the return type, update the function signature
        if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            let inferred_return_type = self.infer_return_type_from_info(&body_info);

            // Update the function signature with the inferred return type
            if let Some(existing) = self.symbols.functions.get_mut(&func.name) {
                existing.return_type_id = inferred_return_type;
            }

            // Also update in entity_registry
            // Get func_id first, then drop borrow before mutating
            let name_id =
                self.name_table_mut()
                    .intern(self.module.current_module, &[func.name], interner);
            let func_id = self.entity_registry().function_by_name(name_id);
            if let Some(func_id) = func_id {
                self.entity_registry_mut()
                    .update_function_return_type(func_id, inferred_return_type);
            }
        } else {
            // Check for missing return statement when return type is explicit and non-void.
            // Generator functions (those with current_generator_element_type set) don't need
            // explicit return statements -- they produce values via yield and implicitly
            // return Done when the body completes.
            let is_void = func_type.return_type_id.is_void();
            let is_generator = self.env.current_generator_element_type.is_some();
            if !is_void && !is_generator && !body_info.definitely_returns {
                let func_name = interner.resolve(func.name).to_string();
                let expected = self.type_display_id(func_type.return_type_id);
                let hint = self.compute_missing_return_hint(
                    &func.body,
                    func_type.return_type_id,
                    interner,
                );
                self.add_error(
                    SemanticError::MissingReturn {
                        name: func_name,
                        expected,
                        hint,
                        span: func.span.into(),
                    },
                    func.span,
                );
            }
        }

        // Restore scope
        self.pop_scope();
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    pub(super) fn check_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Look up method type via Resolver
        let type_def_id = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry())
            .expect("type should be registered in EntityRegistry");
        let lookup = self
            .lookup_method(type_def_id, method.name, interner)
            .expect("method should be registered in EntityRegistry");

        // Get signature components from arena
        // If the signature is invalid (e.g., due to an unknown type in the method signature),
        // skip checking this method - the type error will be reported from declarations
        let (params_id, return_type_id) = {
            let arena = self.type_arena();
            match arena.unwrap_function(lookup.signature_id) {
                Some((params, ret, _)) => (params.clone(), ret),
                None => return Ok(()), // Invalid signature - skip body checking
            }
        };

        // Determine if we need to infer the return type
        let needs_inference = method.return_type.is_none();

        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(return_type_id)
        };

        // Create scope with 'self' and parameters
        self.push_scope();

        // Add 'self' to scope
        // Note: "self" should already be interned by the parser when it parses method bodies
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        // Build self type directly as TypeId.
        // For generic types, include type parameter TypeIds as type args so that
        // method calls on `self` (e.g. self.getItem()) properly record class method
        // monomorphizations with the type parameters.
        let kind = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).kind
        };
        let type_args = {
            let generic_info = {
                let registry = self.entity_registry();
                registry.get_generic_info(type_def_id).cloned()
            };
            if let Some(gi) = generic_info {
                let mut args = crate::type_arena::TypeIdVec::new();
                for tp in &gi.type_params {
                    let tp_type_id = self.type_arena_mut().type_param(tp.name_id);
                    args.push(tp_type_id);
                }
                args
            } else {
                crate::type_arena::TypeIdVec::new()
            }
        };
        let self_type_id = match kind {
            TypeDefKind::Class => self.type_arena_mut().class(type_def_id, type_args),
            TypeDefKind::Struct | TypeDefKind::Sentinel => {
                self.type_arena_mut().struct_type(type_def_id, type_args)
            }
            TypeDefKind::Interface
            | TypeDefKind::ErrorType
            | TypeDefKind::Primitive
            | TypeDefKind::Alias => self.type_arena().invalid(),
        };
        self.env.scope.define(
            self_sym,
            Variable {
                ty: self_type_id,
                mutable: false,
                declaration_span: method.span, // 'self' is implicitly declared by the method
            },
        );

        // Add parameters (filter out explicit `self` — it was already added above)
        let non_self_params: Vec<_> = method
            .params
            .iter()
            .filter(|p| interner.resolve(p.name) != "self")
            .collect();
        for (param, &ty_id) in non_self_params.iter().zip(params_id.iter()) {
            self.env.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                    declaration_span: param.span,
                },
            );
        }

        // Type-check parameter default expressions
        self.check_param_defaults(
            &non_self_params.into_iter().cloned().collect::<Vec<_>>(),
            &params_id,
            interner,
        )?;

        // Check body
        let body_info = self.check_func_body(&method.body, interner)?;

        // If we were inferring the return type, update the method signature
        if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            let inferred_return_type = self.infer_return_type_from_info(&body_info);

            // Update the method's return type in EntityRegistry
            {
                let mut entities = self.entity_registry_mut();
                let mut types = self.type_arena_mut();
                entities.update_method_return_type(
                    lookup.method_id,
                    inferred_return_type,
                    &mut types,
                );
            }
        } else {
            // Check for missing return statement when return type is explicit and non-void
            let is_void = return_type_id.is_void();
            if !is_void && !body_info.definitely_returns {
                let method_name = interner.resolve(method.name).to_string();
                let expected = self.type_display_id(return_type_id);
                let hint = self.compute_missing_return_hint(&method.body, return_type_id, interner);
                self.add_error(
                    SemanticError::MissingReturn {
                        name: method_name,
                        expected,
                        hint,
                        span: method.span.into(),
                    },
                    method.span,
                );
            }
        }

        // Restore scope
        self.pop_scope();
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Check a function body - either a block or a single expression
    pub(super) fn check_func_body(
        &mut self,
        body: &FuncBody,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        match body {
            FuncBody::Block(block) => self.check_block(block, interner),
            FuncBody::Expr(expr) => {
                // Expression body is implicitly a return
                let expr_type = self.check_expr(expr, interner)?;

                // Handle return type inference or checking
                if let Some(expected_return) = self.env.current_function_return {
                    // Explicit return type - check for match
                    if !self.types_compatible_id(expr_type, expected_return, interner) {
                        let expected_str = self.type_display_id(expected_return);
                        let found = self.type_display_id(expr_type);
                        self.add_error(
                            SemanticError::ReturnTypeMismatch {
                                expected: expected_str,
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                } else {
                    // Inference mode - set the return type
                    self.env.current_function_return = Some(expr_type);
                }
                // Expression body definitely returns with the expression type
                Ok(ReturnInfo {
                    definitely_returns: true,
                    return_types: vec![(expr_type, expr.span)],
                })
            }
        }
    }

    /// Compute the hint for a MissingReturn error.
    /// If the last statement in the block is an expression whose type matches the expected return type,
    /// suggest adding `return` before it. Otherwise, provide a generic hint.
    pub(super) fn compute_missing_return_hint(
        &mut self,
        body: &FuncBody,
        expected_return_type: ArenaTypeId,
        interner: &Interner,
    ) -> String {
        if let FuncBody::Block(block) = body
            && let Some(Stmt::Expr(expr_stmt)) = block.stmts.last()
        {
            // Check if we have a recorded type for this expression
            if let Some(&expr_type) = self.results.expr_types.get(&expr_stmt.expr.id) {
                // Check if it matches the expected return type
                if self.types_compatible_id(expr_type, expected_return_type, interner) {
                    return "did you mean to add `return` before the last expression?".to_string();
                }
            }
        }
        // Default hint
        "add a return statement, or change return type to void".to_string()
    }

    /// Check a static method body (no `self` access allowed)
    pub(super) fn check_static_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Resolve type name and delegate to check_static_method_with_type_def
        let type_def_id = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry())
            .expect("type should be registered in EntityRegistry");
        self.check_static_method_with_type_def(method, type_def_id, interner)
    }

    /// Check a static method body with the type already resolved to a TypeDefId.
    /// This is used for primitive types where we can't resolve via Symbol.
    pub(super) fn check_static_method_with_type_def(
        &mut self,
        method: &InterfaceMethod,
        type_def_id: TypeDefId,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Only check methods with bodies
        let Some(ref body) = method.body else {
            return Ok(());
        };

        let method_name_id = self.method_name_id(method.name, interner);
        let method_id = self
            .entity_registry_mut()
            .find_static_method_on_type(type_def_id, method_name_id)
            .expect("static method should be registered in EntityRegistry");
        let (method_type_params, signature_id) = {
            let registry = self.entity_registry();
            let method_def = registry.get_method(method_id);
            (
                method_def.method_type_params.clone(),
                method_def.signature_id,
            )
        };

        // Get signature components from arena
        let (params_id, return_type_id) = {
            let arena = self.type_arena();
            // If signature is invalid (unknown type), skip checking - error already reported
            let Some((params, ret, _)) = arena.unwrap_function(signature_id) else {
                return Ok(());
            };
            (params.clone(), ret)
        };

        // Determine if we need to infer the return type
        let needs_inference = method.return_type.is_none();
        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(return_type_id)
        };

        // Mark that we're in a static method (for self-usage detection)
        self.env.current_static_method = Some(interner.resolve(method.name).to_string());

        // Push method-level type params onto the stack (merged with any class type params)
        let has_method_type_params = !method_type_params.is_empty();
        if has_method_type_params {
            self.env.type_param_stack.push_merged(method_type_params);
        }

        // Create scope WITHOUT 'self', define parameters
        self.enter_param_scope(&method.params, &params_id);

        // Check body
        let body_info = self.check_func_body(body, interner)?;

        // If we were inferring the return type, update the method signature
        if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            let inferred_return_type = self.infer_return_type_from_info(&body_info);

            // Update the method signature with the inferred return type
            {
                let mut entities = self.entity_registry_mut();
                let mut types = self.type_arena_mut();
                entities.update_method_return_type(method_id, inferred_return_type, &mut types);
            }
        }

        // Restore scope and context
        self.pop_scope();
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Check an implement block method body.
    /// This is called for instance methods defined in implement blocks.
    /// The method signature should already be registered in the implement registry.
    pub(super) fn check_implement_method(
        &mut self,
        method: &FuncDecl,
        target_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        use crate::implement_registry::ImplTypeId;

        // Get the impl_type_id for looking up method signature
        let impl_type_id = {
            let arena = self.type_arena();
            ImplTypeId::from_type_id(target_type_id, &arena, &self.entity_registry())
        };
        let Some(impl_type_id) = impl_type_id else {
            return Ok(()); // Can't check if we can't identify the type
        };

        // Get method signature from implement registry
        let method_name_id = self.method_name_id(method.name, interner);
        let (params_id, return_type_id) = {
            let registry = self.implement_registry();
            let method_impl = registry.get_method(&impl_type_id, method_name_id);
            let Some(method_impl) = method_impl else {
                return Ok(()); // Method not found in registry, skip
            };
            (
                method_impl.func_type.params_id.clone(),
                method_impl.func_type.return_type_id,
            )
        };

        // Determine if we need to infer the return type
        let needs_inference = method.return_type.is_none();

        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(return_type_id)
        };

        // Create scope with 'self' and parameters
        self.push_scope();

        // Add 'self' to scope
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        self.env.scope.define(
            self_sym,
            Variable {
                ty: target_type_id,
                mutable: false,
                declaration_span: method.span,
            },
        );

        // Add parameters (filter out explicit `self` — it was already added above)
        let non_self_params: Vec<_> = method
            .params
            .iter()
            .filter(|p| interner.resolve(p.name) != "self")
            .collect();
        for (param, &ty_id) in non_self_params.iter().zip(params_id.iter()) {
            self.env.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                    declaration_span: param.span,
                },
            );
        }

        // Type-check parameter default expressions
        self.check_param_defaults(
            &non_self_params.into_iter().cloned().collect::<Vec<_>>(),
            &params_id,
            interner,
        )?;

        // Check body
        let _body_info = self.check_func_body(&method.body, interner)?;

        // Note: We don't update inferred return types for implement block methods
        // since they're stored in the implement registry, not entity registry.
        // This could be enhanced later if needed.

        // Restore scope and context
        self.pop_scope();
        self.exit_function_context(saved_ctx);

        Ok(())
    }
}
