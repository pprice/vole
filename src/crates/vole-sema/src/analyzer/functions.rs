// src/sema/analyzer/functions.rs
//! Function and method checking: context management, body analysis, monomorphization.

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
            return_type: self.current_function_return.take(),
            error_type: self.current_function_error_type.take(),
            generator_element_type: self.current_generator_element_type.take(),
            static_method: self.current_static_method.take(),
            type_param_stack_depth: self.type_param_stack.depth(),
        };

        self.current_function_return = Some(return_type_id);

        // Set error type context if this is a fallible function
        let error_type = self
            .type_arena()
            .unwrap_fallible(return_type_id)
            .map(|(_, e)| e);
        if let Some(error) = error_type {
            self.current_function_error_type = Some(error);
        }

        // Set generator context if return type is Iterator<T>
        if let Some(element_type_id) = self.extract_iterator_element_type_id(return_type_id) {
            self.current_generator_element_type = Some(element_type_id);
        }

        saved
    }

    /// Enter a function context for return type inference (no known return type).
    /// The first return statement will set current_function_return; subsequent returns check against it.
    pub(super) fn enter_function_context_inferring(&mut self) -> FunctionCheckContext {
        // current_function_return stays None to signal inference mode
        FunctionCheckContext {
            return_type: self.current_function_return.take(),
            error_type: self.current_function_error_type.take(),
            generator_element_type: self.current_generator_element_type.take(),
            static_method: self.current_static_method.take(),
            type_param_stack_depth: self.type_param_stack.depth(),
        }
    }

    /// Exit function/method check context, restoring saved state.
    pub(super) fn exit_function_context(&mut self, saved: FunctionCheckContext) {
        self.current_function_return = saved.return_type;
        self.current_function_error_type = saved.error_type;
        self.current_generator_element_type = saved.generator_element_type;
        self.current_static_method = saved.static_method;
        // Pop any scopes that were pushed during this context
        while self.type_param_stack.depth() > saved.type_param_stack_depth {
            self.type_param_stack.pop();
        }
    }

    /// Create a new scope and define function/method/lambda parameters in it.
    pub(super) fn enter_param_scope(&mut self, params: &[Param], type_ids: &[ArenaTypeId]) {
        let parent = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent);
        for (param, &ty_id) in params.iter().zip(type_ids.iter()) {
            self.scope.define(
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
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);
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
            if let Some(existing) = self.functions.get_mut(&func.name) {
                existing.return_type_id = inferred_return_type;
            }

            // Also update in entity_registry
            // Get func_id first, then drop borrow before mutating
            let name_id = self
                .name_table_mut()
                .intern(self.current_module, &[func.name], interner);
            let func_id = self.entity_registry().function_by_name(name_id);
            if let Some(func_id) = func_id {
                self.entity_registry_mut()
                    .update_function_return_type(func_id, inferred_return_type);
            }
        } else {
            // Check for missing return statement when return type is explicit and non-void
            let is_void = func_type.return_type_id.is_void();
            if !is_void && !body_info.definitely_returns {
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
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Analyze a generic function body with type substitutions applied.
    /// This discovers nested generic function calls and creates their MonomorphInstances.
    fn analyze_monomorph_body(
        &mut self,
        func: &FuncDecl,
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
        interner: &Interner,
    ) {
        // Get the generic function info to resolve parameter and return types
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);
        let generic_info = {
            let registry = self.entity_registry();
            registry
                .function_by_name(name_id)
                .and_then(|fid| registry.get_function(fid).generic_info.clone())
        };

        let Some(generic_info) = generic_info else {
            return;
        };

        // Compute concrete parameter and return types
        let (concrete_param_ids, concrete_return_id) = {
            let mut arena = self.type_arena_mut();
            let param_ids: Vec<_> = generic_info
                .param_types
                .iter()
                .map(|&t| arena.substitute(t, substitutions))
                .collect();
            let return_id = arena.substitute(generic_info.return_type, substitutions);
            (param_ids, return_id)
        };

        // Set up function context with the concrete return type
        let saved_ctx = self.enter_function_context(concrete_return_id);

        // Create new scope with parameters (using concrete types)
        self.enter_param_scope(&func.params, &concrete_param_ids);

        // Set up type parameter scope with the substitutions
        // This maps type param names to their concrete types
        let mut type_param_scope = TypeParamScope::new();
        for tp in &generic_info.type_params {
            // Create TypeParamInfo with the substituted type
            type_param_scope.add(tp.clone());
        }
        self.type_param_stack.push_scope(type_param_scope);

        // Store substitutions for use during type resolution
        // We need to make type param lookups return the substituted concrete types
        // This is handled via type_arena.substitute during check_call_expr

        // Check the function body - this will discover nested generic calls
        // and create MonomorphInstances for them
        let _ = self.check_func_body(&func.body, interner);

        // Pop type parameter scope
        self.type_param_stack.pop();

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);
    }

    /// Analyze all monomorphized function bodies to discover nested generic calls.
    /// Iterates until no new MonomorphInstances are created (fixpoint).
    pub(super) fn analyze_monomorph_bodies(&mut self, program: &Program, interner: &Interner) {
        // Build map of generic function names to their ASTs
        // Include both explicit generics (type_params in AST) and implicit generics
        // (structural type params that create generic_info in entity registry)
        let generic_func_asts: FxHashMap<NameId, &FuncDecl> = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Function(func) = decl {
                    let name_id =
                        self.name_table_mut()
                            .intern(self.current_module, &[func.name], interner);

                    // Check for explicit type params OR implicit generic_info
                    let has_explicit_type_params = !func.type_params.is_empty();
                    let has_implicit_generic_info = self
                        .entity_registry()
                        .function_by_name(name_id)
                        .map(|func_id| {
                            self.entity_registry()
                                .get_function(func_id)
                                .generic_info
                                .is_some()
                        })
                        .unwrap_or(false);

                    if has_explicit_type_params || has_implicit_generic_info {
                        return Some((name_id, func));
                    }
                }
                None
            })
            .collect();

        // Track which instances we've already analyzed
        let mut analyzed_keys: HashSet<MonomorphKey> = HashSet::new();

        // Iterate until fixpoint
        loop {
            // Collect current instances that haven't been analyzed yet
            let instances: Vec<_> = self
                .entity_registry()
                .monomorph_cache
                .collect_instances()
                .into_iter()
                .filter(|inst| {
                    let key = MonomorphKey::new(
                        inst.original_name,
                        inst.substitutions.values().copied().collect(),
                    );
                    !analyzed_keys.contains(&key)
                })
                .collect();

            if instances.is_empty() {
                break;
            }

            for instance in instances {
                // Mark as analyzed
                let key = MonomorphKey::new(
                    instance.original_name,
                    instance.substitutions.values().copied().collect(),
                );
                analyzed_keys.insert(key);

                // Find the function AST
                if let Some(func) = generic_func_asts.get(&instance.original_name) {
                    // Analyze the body with substitutions
                    self.analyze_monomorph_body(func, &instance.substitutions, interner);
                }
            }
        }
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
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

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
        self.scope.define(
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
            self.scope.define(
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
                let mut db = self.ctx.db.borrow_mut();
                let CompilationDb {
                    ref mut entities,
                    ref mut types,
                    ..
                } = *db;
                Rc::make_mut(entities).update_method_return_type(
                    lookup.method_id,
                    inferred_return_type,
                    Rc::make_mut(types),
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
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
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
                if let Some(expected_return) = self.current_function_return {
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
                    self.current_function_return = Some(expr_type);
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
            if let Some(&expr_type) = self.expr_types.get(&expr_stmt.expr.id) {
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
        self.current_static_method = Some(interner.resolve(method.name).to_string());

        // Push method-level type params onto the stack (merged with any class type params)
        let has_method_type_params = !method_type_params.is_empty();
        if has_method_type_params {
            self.type_param_stack.push_merged(method_type_params);
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
            // Destructure db to get both entities and types to avoid RefCell conflict
            {
                let mut db = self.ctx.db.borrow_mut();
                let CompilationDb {
                    ref mut entities,
                    ref mut types,
                    ..
                } = *db;
                Rc::make_mut(entities).update_method_return_type(
                    method_id,
                    inferred_return_type,
                    Rc::make_mut(types),
                );
            }
        }

        // Restore scope and context
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
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
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add 'self' to scope
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        self.scope.define(
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
            self.scope.define(
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
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Propagate concrete type substitutions to class method monomorphs created
    /// from self-method calls inside generic class methods.
    ///
    /// When sema analyzes method bodies, `self` has abstract type params (e.g., `Box<T>`).
    /// A call like `self.inner()` records a monomorph with identity substitutions
    /// `{T: TypeParam(T)}`. When a concrete monomorph exists for `outer()` with `{T: i64}`,
    /// this pass creates a matching concrete monomorph for `inner()` with `{T: i64}`.
    ///
    /// Iterates to fixpoint to handle transitive chains: a() -> self.b() -> self.c().
    pub(super) fn propagate_class_method_monomorphs(&mut self) {
        loop {
            let new_instances = self.derive_concrete_class_method_monomorphs();
            if new_instances.is_empty() {
                break;
            }

            for (key, instance) in new_instances {
                self.entity_registry_mut()
                    .class_method_monomorph_cache
                    .insert(key, instance);
            }
        }
    }

    /// Propagate concrete substitutions to static method monomorphs created
    /// from static calls inside generic class static methods.
    ///
    /// Example: `Map.new<K, V>()` calls `Map.with_capacity<K, V>(8)` and records
    /// an identity monomorph for `with_capacity`. When a concrete caller exists
    /// (e.g., `Map.new<i64, string>`), derive `Map.with_capacity<i64, string>`.
    pub(super) fn propagate_static_method_monomorphs(&mut self) {
        loop {
            let new_instances = self.derive_concrete_static_method_monomorphs();
            if new_instances.is_empty() {
                break;
            }

            for (key, instance) in new_instances {
                self.entity_registry_mut()
                    .static_method_monomorph_cache
                    .insert(key, instance);
            }
        }
    }

    /// Single iteration: derive concrete static monomorphs from identity-substituted ones.
    fn derive_concrete_static_method_monomorphs(
        &mut self,
    ) -> Vec<(
        StaticMethodMonomorphKey,
        crate::generic::StaticMethodMonomorphInstance,
    )> {
        let all_instances: Vec<crate::generic::StaticMethodMonomorphInstance> = self
            .entity_registry()
            .static_method_monomorph_cache
            .collect_instances();

        let mut concrete_subs_by_class: FxHashMap<NameId, Vec<FxHashMap<NameId, ArenaTypeId>>> =
            FxHashMap::default();
        let mut identity_instances: Vec<&crate::generic::StaticMethodMonomorphInstance> =
            Vec::new();

        {
            let arena = self.type_arena();
            for inst in &all_instances {
                let has_type_param_value = inst
                    .substitutions
                    .values()
                    .any(|&v| arena.unwrap_type_param(v).is_some());
                if has_type_param_value {
                    identity_instances.push(inst);
                } else if !inst.substitutions.is_empty() {
                    concrete_subs_by_class
                        .entry(inst.class_name)
                        .or_default()
                        .push(inst.substitutions.clone());
                }
            }
        }

        for subs_list in concrete_subs_by_class.values_mut() {
            subs_list.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
            subs_list.dedup();
        }

        let mut new_instances = Vec::new();

        for identity_inst in &identity_instances {
            let Some(concrete_subs_list) = concrete_subs_by_class.get(&identity_inst.class_name)
            else {
                continue;
            };

            for concrete_subs in concrete_subs_list {
                let composed_subs =
                    self.compose_substitutions(&identity_inst.substitutions, concrete_subs);

                let Some(key) = self.build_static_method_monomorph_key(
                    identity_inst.class_name,
                    identity_inst.method_name,
                    &composed_subs,
                ) else {
                    continue;
                };

                if self
                    .entity_registry()
                    .static_method_monomorph_cache
                    .contains(&key)
                {
                    continue;
                }

                if new_instances
                    .iter()
                    .any(|(existing_key, _)| *existing_key == key)
                {
                    continue;
                }

                let Some(instance) =
                    self.create_derived_static_method_monomorph(identity_inst, &composed_subs)
                else {
                    continue;
                };

                tracing::debug!(
                    class = ?identity_inst.class_name,
                    method = ?identity_inst.method_name,
                    subs = ?composed_subs,
                    "propagated concrete static method monomorph"
                );

                new_instances.push((key, instance));
            }
        }

        new_instances
    }

    /// Single iteration: derive concrete monomorphs from identity-substituted ones.
    ///
    /// Returns a list of (key, instance) pairs to insert into the cache.
    fn derive_concrete_class_method_monomorphs(
        &mut self,
    ) -> Vec<(
        ClassMethodMonomorphKey,
        crate::generic::ClassMethodMonomorphInstance,
    )> {
        let all_instances: Vec<crate::generic::ClassMethodMonomorphInstance> = self
            .entity_registry()
            .class_method_monomorph_cache
            .collect_instances();

        // Partition into concrete and identity substitutions.
        let mut concrete_subs_by_class: FxHashMap<NameId, Vec<FxHashMap<NameId, ArenaTypeId>>> =
            FxHashMap::default();
        let mut identity_instances: Vec<&crate::generic::ClassMethodMonomorphInstance> = Vec::new();

        {
            let arena = self.type_arena();
            for inst in &all_instances {
                let has_type_param_value = inst
                    .substitutions
                    .values()
                    .any(|&v| arena.unwrap_type_param(v).is_some());
                if has_type_param_value {
                    identity_instances.push(inst);
                } else if !inst.substitutions.is_empty() {
                    concrete_subs_by_class
                        .entry(inst.class_name)
                        .or_default()
                        .push(inst.substitutions.clone());
                }
            }
        }

        for subs_list in concrete_subs_by_class.values_mut() {
            subs_list.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
            subs_list.dedup();
        }

        let mut new_instances = Vec::new();

        for identity_inst in &identity_instances {
            let Some(concrete_subs_list) = concrete_subs_by_class.get(&identity_inst.class_name)
            else {
                continue;
            };

            for concrete_subs in concrete_subs_list {
                let composed_subs =
                    self.compose_substitutions(&identity_inst.substitutions, concrete_subs);

                let Some(key) = self.build_class_method_monomorph_key(
                    identity_inst.class_name,
                    identity_inst.method_name,
                    &composed_subs,
                ) else {
                    continue;
                };

                if self
                    .entity_registry()
                    .class_method_monomorph_cache
                    .contains(&key)
                {
                    continue;
                }

                if new_instances
                    .iter()
                    .any(|(existing_key, _)| *existing_key == key)
                {
                    continue;
                }

                let type_keys = key.type_keys.clone();
                let Some(instance) = self.create_derived_class_method_monomorph(
                    identity_inst,
                    &composed_subs,
                    &type_keys,
                ) else {
                    continue;
                };

                tracing::debug!(
                    class = ?identity_inst.class_name,
                    method = ?identity_inst.method_name,
                    subs = ?composed_subs,
                    "propagated concrete class method monomorph"
                );

                new_instances.push((key, instance));
            }
        }

        new_instances
    }

    /// Compose two substitution maps: apply `concrete` to the values of `identity`.
    ///
    /// Example:
    /// identity = {T: TypeParam(T)}, concrete = {T: i64} => {T: i64}
    fn compose_substitutions(
        &self,
        identity: &FxHashMap<NameId, ArenaTypeId>,
        concrete: &FxHashMap<NameId, ArenaTypeId>,
    ) -> FxHashMap<NameId, ArenaTypeId> {
        let arena = self.type_arena();
        let mut composed = FxHashMap::default();

        for (&name_id, &type_id) in identity {
            if let Some(param_name_id) = arena.unwrap_type_param(type_id)
                && let Some(&concrete_type_id) = concrete.get(&param_name_id)
            {
                composed.insert(name_id, concrete_type_id);
                continue;
            }
            composed.insert(name_id, type_id);
        }

        composed
    }

    /// Build a class-method monomorph key using the class's declared type param order.
    fn build_class_method_monomorph_key(
        &self,
        class_name: NameId,
        method_name: NameId,
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Option<ClassMethodMonomorphKey> {
        let registry = self.entity_registry();
        let type_def_id = registry.type_by_name(class_name)?;
        let generic_info = registry.type_generic_info(type_def_id)?;
        let type_keys: Vec<ArenaTypeId> = generic_info
            .type_params
            .iter()
            .filter_map(|tp| substitutions.get(&tp.name_id).copied())
            .collect();
        Some(ClassMethodMonomorphKey::new(
            class_name,
            method_name,
            type_keys,
        ))
    }

    /// Build a static-method monomorph key using class and method type param order.
    fn build_static_method_monomorph_key(
        &self,
        class_name: NameId,
        method_name: NameId,
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Option<StaticMethodMonomorphKey> {
        let registry = self.entity_registry();
        let type_def_id = registry.type_by_name(class_name)?;
        let class_type_keys: Vec<ArenaTypeId> = registry
            .type_generic_info(type_def_id)
            .map(|generic_info| {
                generic_info
                    .type_params
                    .iter()
                    .filter_map(|tp| substitutions.get(&tp.name_id).copied())
                    .collect()
            })
            .unwrap_or_default();

        let method_id = registry.find_static_method_on_type(type_def_id, method_name)?;
        let method = registry.get_method(method_id);
        let method_type_keys: Vec<ArenaTypeId> = method
            .method_type_params
            .iter()
            .filter_map(|tp| substitutions.get(&tp.name_id).copied())
            .collect();

        Some(StaticMethodMonomorphKey::new(
            class_name,
            method_name,
            class_type_keys,
            method_type_keys,
        ))
    }

    /// Create a derived concrete class-method monomorph instance.
    fn create_derived_class_method_monomorph(
        &mut self,
        identity_inst: &crate::generic::ClassMethodMonomorphInstance,
        concrete_subs: &FxHashMap<NameId, ArenaTypeId>,
        type_keys: &[ArenaTypeId],
    ) -> Option<crate::generic::ClassMethodMonomorphInstance> {
        let type_def_id = self
            .entity_registry()
            .type_by_name(identity_inst.class_name)?;
        let method_id = self
            .entity_registry()
            .find_method_on_type(type_def_id, identity_inst.method_name)?;
        let signature_id = self.entity_registry().method_signature(method_id);

        let (params, ret, is_closure) = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena.unwrap_function(signature_id)?;
            (params.to_vec(), ret, is_closure)
        };

        let (subst_params, subst_ret) = {
            let mut arena = self.type_arena_mut();
            let subst_params = params
                .iter()
                .map(|&param_type_id| arena.substitute(param_type_id, concrete_subs))
                .collect::<Vec<_>>();
            let subst_ret = arena.substitute(ret, concrete_subs);
            (subst_params, subst_ret)
        };
        let func_type = FunctionType::from_ids(&subst_params, subst_ret, is_closure);

        // Eagerly substitute field types so codegen can do immutable lookup_substitute.
        let generic_info = { self.entity_registry().type_generic_info(type_def_id) };
        if let Some(generic_info) = generic_info {
            let field_types = generic_info.field_types;
            let mut arena = self.type_arena_mut();
            for field_type_id in field_types {
                arena.substitute(field_type_id, concrete_subs);
            }
        }

        let kind = { self.entity_registry().get_type(type_def_id).kind };
        let type_args: crate::type_arena::TypeIdVec = type_keys.iter().copied().collect();
        let self_type = match kind {
            TypeDefKind::Class => self.type_arena_mut().class(type_def_id, type_args),
            TypeDefKind::Struct | TypeDefKind::Sentinel => {
                self.type_arena_mut().struct_type(type_def_id, type_args)
            }
            TypeDefKind::Interface
            | TypeDefKind::ErrorType
            | TypeDefKind::Primitive
            | TypeDefKind::Alias => return None,
        };

        let instance_id = self
            .entity_registry_mut()
            .class_method_monomorph_cache
            .next_unique_id();
        let class_name_str = self
            .name_table()
            .last_segment_str(identity_inst.class_name)
            .unwrap_or_else(|| "class".to_string());
        let method_name_str = self
            .name_table()
            .last_segment_str(identity_inst.method_name)
            .unwrap_or_else(|| "method".to_string());
        let mangled_name_str = format!(
            "{}__method_{}__mono_{}",
            class_name_str, method_name_str, instance_id
        );
        let mangled_name = self
            .name_table_mut()
            .intern_raw(self.current_module, &[&mangled_name_str]);

        Some(crate::generic::ClassMethodMonomorphInstance {
            class_name: identity_inst.class_name,
            method_name: identity_inst.method_name,
            mangled_name,
            instance_id,
            func_type,
            substitutions: concrete_subs.clone(),
            external_info: identity_inst.external_info,
            self_type,
        })
    }

    /// Create a derived concrete static-method monomorph instance.
    fn create_derived_static_method_monomorph(
        &mut self,
        identity_inst: &crate::generic::StaticMethodMonomorphInstance,
        concrete_subs: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Option<crate::generic::StaticMethodMonomorphInstance> {
        let type_def_id = self
            .entity_registry()
            .type_by_name(identity_inst.class_name)?;
        let method_id = self
            .entity_registry()
            .find_static_method_on_type(type_def_id, identity_inst.method_name)?;
        let signature_id = self.entity_registry().method_signature(method_id);

        let (params, ret, is_closure) = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena.unwrap_function(signature_id)?;
            (params.to_vec(), ret, is_closure)
        };

        let (subst_params, subst_ret) = {
            let mut arena = self.type_arena_mut();
            let subst_params = params
                .iter()
                .map(|&param_type_id| arena.substitute(param_type_id, concrete_subs))
                .collect::<Vec<_>>();
            let subst_ret = arena.substitute(ret, concrete_subs);
            (subst_params, subst_ret)
        };
        let func_type = FunctionType::from_ids(&subst_params, subst_ret, is_closure);

        // Eagerly substitute field types so codegen can do immutable lookup_substitute.
        let generic_info = { self.entity_registry().type_generic_info(type_def_id) };
        if let Some(generic_info) = generic_info {
            let field_types = generic_info.field_types;
            let mut arena = self.type_arena_mut();
            for field_type_id in field_types {
                arena.substitute(field_type_id, concrete_subs);
            }
        }

        let instance_id = self
            .entity_registry_mut()
            .static_method_monomorph_cache
            .next_unique_id();
        let class_name_str = self
            .name_table()
            .last_segment_str(identity_inst.class_name)
            .unwrap_or_else(|| "class".to_string());
        let method_name_str = self
            .name_table()
            .last_segment_str(identity_inst.method_name)
            .unwrap_or_else(|| "method".to_string());
        let mangled_name_str = format!(
            "{}__static_{}__mono_{}",
            class_name_str, method_name_str, instance_id
        );
        let mangled_name = self
            .name_table_mut()
            .intern_raw(self.current_module, &[&mangled_name_str]);

        Some(crate::generic::StaticMethodMonomorphInstance {
            class_name: identity_inst.class_name,
            method_name: identity_inst.method_name,
            mangled_name,
            instance_id,
            func_type,
            substitutions: concrete_subs.clone(),
        })
    }
}
