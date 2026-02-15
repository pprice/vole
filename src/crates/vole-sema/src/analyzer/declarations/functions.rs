//! Declaration signature collection — function signature collection.

use super::*;

impl Analyzer {
    /// Check if a TypeExpr resolves to a structural type, with type params in scope.
    /// This is needed when the structural type may reference explicit type parameters
    /// (e.g., `{ name: T }` where T is a type param).
    pub(super) fn extract_structural_from_type_expr_with_scope(
        &self,
        ty: &TypeExpr,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) -> Option<InternedStructural> {
        match &ty.kind {
            TypeExprKind::Structural {
                fields: _,
                methods: _,
            } => {
                // Direct structural type - resolve it to an InternedStructural
                let module_id = self.current_module;
                let mut ctx = if let Some(scope) = type_param_scope {
                    TypeResolutionContext::with_type_params(
                        &self.ctx.db,
                        interner,
                        module_id,
                        scope,
                    )
                } else {
                    TypeResolutionContext::new(&self.ctx.db, interner, module_id)
                };
                let type_id = resolve_type_to_id(ty, &mut ctx);
                self.type_arena().unwrap_structural(type_id).cloned()
            }
            TypeExprKind::Named(sym) => {
                // Check if this named type is a type alias that resolves to a structural type
                let _name_str = interner.resolve(*sym);
                if let Some(type_def_id) = self
                    .resolver(interner)
                    .resolve_type(*sym, &self.entity_registry())
                {
                    let kind = self.entity_registry().type_kind(type_def_id);
                    let aliased_type = self.entity_registry().type_aliased(type_def_id);
                    if kind == TypeDefKind::Alias
                        && let Some(aliased_type_id) = aliased_type
                    {
                        return self
                            .type_arena()
                            .unwrap_structural(aliased_type_id)
                            .cloned();
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Collect structural types from function parameters for implicit generification.
    /// Returns a list of (param_index, structural_type) pairs for parameters that need
    /// synthetic type params.
    pub(super) fn collect_structural_params(
        &self,
        func: &FuncDecl,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) -> Vec<(usize, InternedStructural)> {
        let mut result = Vec::new();
        for (i, param) in func.params.iter().enumerate() {
            if let Some(structural) = self.extract_structural_from_type_expr_with_scope(
                &param.ty,
                interner,
                type_param_scope,
            ) {
                let func_name = interner.resolve(func.name);
                tracing::debug!(
                    ?func_name,
                    param_idx = i,
                    ?structural,
                    "implicit generification: found structural type param"
                );
                result.push((i, structural));
            }
        }
        result
    }

    /// Build synthetic type parameters for structural constraints and add them to the scope.
    /// Returns a map from param_index -> synthetic type param name_id.
    pub(super) fn build_synthetic_type_params(
        &mut self,
        structural_params: Vec<(usize, InternedStructural)>,
        type_param_scope: &mut TypeParamScope,
    ) -> FxHashMap<usize, NameId> {
        let builtin_mod = self.name_table_mut().builtin_module();
        let mut synthetic_param_map: FxHashMap<usize, NameId> = FxHashMap::default();

        for (i, (param_idx, structural)) in structural_params.into_iter().enumerate() {
            // Generate synthetic type param name like __T0, __T1, etc.
            let synthetic_name = format!("__T{}", i);
            let synthetic_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[&synthetic_name]);

            // Create a synthetic Symbol for the type param
            // Use a high value that won't collide with user symbols.
            // This is safe because synthetic type params are never looked up by Symbol,
            // only by name_id during monomorphization/codegen.
            let synthetic_symbol = Symbol::synthetic(i as u32);

            tracing::debug!(
                ?synthetic_name,
                ?synthetic_name_id,
                ?param_idx,
                "created synthetic type param for structural constraint"
            );

            type_param_scope.add(TypeParamInfo {
                name: synthetic_symbol,
                name_id: synthetic_name_id,
                constraint: Some(TypeConstraint::Structural(structural)),
                type_param_id: None,
                variance: TypeParamVariance::default(),
            });
            synthetic_param_map.insert(param_idx, synthetic_name_id);
        }

        synthetic_param_map
    }

    /// Resolve and validate parameter types for a non-generic function.
    /// Returns the resolved TypeIds for each parameter.
    pub(super) fn resolve_non_generic_params(
        &mut self,
        params: &[Param],
        interner: &Interner,
    ) -> Vec<ArenaTypeId> {
        params
            .iter()
            .map(|p| {
                // Validate type annotation first to emit errors for unknown types
                self.validate_type_annotation(&p.ty, p.span, interner, None);
                let type_id = self.resolve_type_id(&p.ty, interner);
                self.check_type_annotation_constraints(type_id, &p.ty, p.span);
                type_id
            })
            .collect()
    }

    /// Resolve and validate the return type for a non-generic function.
    pub(super) fn resolve_non_generic_return(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> ArenaTypeId {
        // Validate return type annotation first to emit errors for unknown types
        if let Some(rt) = &func.return_type {
            self.validate_type_annotation(rt, func.span, interner, None);
        }
        let return_type_id = func
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_id(t, interner))
            .unwrap_or_else(|| self.type_arena().void());
        if let Some(rt) = &func.return_type {
            self.check_union_simplification(rt, func.span);
            self.check_combination_not_allowed(rt, func.span);
        }
        return_type_id
    }

    /// Resolve parameter and return types for a generic function with type params in scope.
    /// Synthetic type params are substituted for their corresponding structural types.
    pub(super) fn resolve_generic_signature(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
        type_param_scope: &TypeParamScope,
        synthetic_param_map: &FxHashMap<usize, NameId>,
    ) -> (Vec<ArenaTypeId>, ArenaTypeId) {
        let module_id = self.current_module;
        let mut ctx = TypeResolutionContext::with_type_params(
            &self.ctx.db,
            interner,
            module_id,
            type_param_scope,
        );

        let param_types = func
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                if let Some(&synthetic_name_id) = synthetic_param_map.get(&i) {
                    // Use the synthetic type parameter instead of the structural type
                    ctx.type_arena_mut().type_param(synthetic_name_id)
                } else {
                    resolve_type_to_id(&p.ty, &mut ctx)
                }
            })
            .collect();

        let return_type = func
            .return_type
            .as_ref()
            .map(|t| resolve_type_to_id(t, &mut ctx))
            .unwrap_or_else(|| self.type_arena().void());

        (param_types, return_type)
    }

    /// Validate parameter and return types after resolution (for generic functions).
    pub(super) fn validate_generic_function_types(
        &mut self,
        func: &FuncDecl,
        param_type_ids: &[ArenaTypeId],
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        for (param, &type_id) in func.params.iter().zip(param_type_ids) {
            // Validate type annotation to emit errors for unknown types
            self.validate_type_annotation(&param.ty, param.span, interner, type_param_scope);
            self.check_type_annotation_constraints(type_id, &param.ty, param.span);
        }
        if let Some(rt) = &func.return_type {
            // Validate return type annotation to emit errors for unknown types
            self.validate_type_annotation(rt, func.span, interner, type_param_scope);
            self.check_combination_not_allowed(rt, func.span);
        }
    }

    /// Register a non-generic function (no type parameters).
    pub(super) fn register_non_generic_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
        reg_data: FuncRegistrationData,
    ) {
        let params_id = self.resolve_non_generic_params(&func.params, interner);
        let return_type_id = self.resolve_non_generic_return(func, interner);

        let signature = FunctionType::from_ids(&params_id, return_type_id, false);
        self.functions.insert(func.name, signature.clone());

        // Register in EntityRegistry with default expressions
        self.entity_registry_mut().register_function_full(
            reg_data.name_id,
            reg_data.name_id, // For top-level functions, name_id == full_name_id
            self.current_module,
            signature,
            reg_data.required_params,
            reg_data.param_defaults,
        );
    }

    /// Register a generic function (explicit type parameters or implicit via structural types).
    pub(super) fn register_generic_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
        reg_data: FuncRegistrationData,
        type_param_scope: TypeParamScope,
        synthetic_param_map: FxHashMap<usize, NameId>,
    ) {
        // Resolve param and return types with type params in scope
        let (param_type_ids, return_type_id) =
            self.resolve_generic_signature(func, interner, &type_param_scope, &synthetic_param_map);

        // Validate types after resolution
        self.validate_generic_function_types(
            func,
            &param_type_ids,
            interner,
            Some(&type_param_scope),
        );

        // Create signature and register
        let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);

        let func_id = self.entity_registry_mut().register_function_full(
            reg_data.name_id,
            reg_data.name_id, // For top-level functions, name_id == full_name_id
            self.current_module,
            signature,
            reg_data.required_params,
            reg_data.param_defaults,
        );

        // Set generic info
        let type_params = type_param_scope.into_params();
        self.entity_registry_mut().set_function_generic_info(
            func_id,
            GenericFuncInfo {
                type_params,
                param_types: param_type_ids,
                return_type: return_type_id,
            },
        );
    }

    pub(super) fn collect_function_signature(&mut self, func: &FuncDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);

        // Validate parameter default ordering: non-defaulted params must come before defaulted
        let required_params = self.validate_param_defaults(&func.params, interner);

        // Clone the default expressions for storage
        let param_defaults: Vec<Option<Box<Expr>>> = func
            .params
            .iter()
            .map(|p| p.default_value.clone())
            .collect();

        let reg_data = FuncRegistrationData {
            name_id,
            required_params,
            param_defaults,
        };

        // Build initial type param scope from explicit type params (if any)
        // This is needed so that structural types like { name: T } can resolve T
        let explicit_type_param_scope: Option<TypeParamScope> = if !func.type_params.is_empty() {
            Some(self.build_unconstrained_scope(&func.type_params, interner))
        } else {
            None
        };

        // Collect structural types for implicit generification
        let structural_params =
            self.collect_structural_params(func, interner, explicit_type_param_scope.as_ref());

        let has_explicit_type_params = !func.type_params.is_empty();
        let has_synthetic_type_params = !structural_params.is_empty();

        if !has_explicit_type_params && !has_synthetic_type_params {
            self.register_non_generic_function(func, interner, reg_data);
        } else {
            // Build type param scope with constraints and synthetic params
            let mut type_param_scope =
                self.build_type_params_with_constraints(&func.type_params, interner);
            let synthetic_param_map =
                self.build_synthetic_type_params(structural_params, &mut type_param_scope);

            self.register_generic_function(
                func,
                interner,
                reg_data,
                type_param_scope,
                synthetic_param_map,
            );
        }
    }

    /// Validate parameter default ordering and count required params.
    /// Returns the number of required (non-defaulted) parameters.
    /// Emits errors if non-defaulted params come after defaulted params.
    pub(super) fn validate_param_defaults(
        &mut self,
        params: &[Param],
        interner: &Interner,
    ) -> usize {
        let (required_count, _) = validate_defaults(params, interner, |name, span| {
            self.add_error(
                SemanticError::DefaultParamNotLast {
                    name,
                    span: span.into(),
                },
                span,
            );
        });
        required_count
    }
}
