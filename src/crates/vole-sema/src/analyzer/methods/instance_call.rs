use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;

impl Analyzer {
    /// Process a resolved instance method call: check arguments, record monomorphization,
    /// compute return type, and store resolution.
    ///
    /// This consolidates the post-resolution logic for instance method calls.
    /// Returns the final return type for the expression.
    pub(crate) fn process_resolved_instance_method(
        &mut self,
        expr: &Expr,
        method_call: &MethodCallExpr,
        object_type_id: ArenaTypeId,
        resolved: ResolvedMethod,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let method_name = interner.resolve(method_call.method);

        // Handle builtin method override
        if resolved.is_builtin()
            && let Some(func_type) = self.check_builtin_method_id(
                object_type_id,
                method_name,
                &method_call.args,
                interner,
            )
        {
            let updated = self.apply_builtin_override(resolved, &func_type);
            self.results.method_resolutions.insert(expr.id, updated);
            return Ok(func_type.return_type_id);
        }

        // Reconstruct FunctionType from arena for arg checking and monomorph recording
        let func_type = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena
                .unwrap_function(resolved.func_type_id())
                .expect("resolved method must have function type");
            FunctionType {
                is_closure,
                params_id: params.clone(),
                return_type_id: ret,
            }
        };

        // Mark side effects if inside lambda
        if self.in_lambda() {
            self.mark_lambda_has_side_effects();
        }

        // Check argument count with defaults support
        self.check_method_arg_count(&resolved, &func_type, method_call, expr.span);

        // Check argument types (including map/flat_map transform handling)
        let map_inferred_return_type =
            self.check_instance_method_args(method_call, object_type_id, &func_type, interner)?;

        // Compute final return type (handling map transform override)
        let external_info = resolved.external_info().copied();
        let resolved_return_id = self.compute_resolved_return_type(
            &resolved,
            map_inferred_return_type,
            method_call,
            interner,
        );

        // Store resolution
        self.results.method_resolutions.insert(expr.id, resolved);

        // Record class method monomorphization for generic classes/records
        self.record_class_method_monomorph(
            expr,
            object_type_id,
            method_call.method,
            &func_type,
            external_info,
            interner,
        );

        // Store the substituted return type for codegen
        let final_return_id = self.compute_substituted_return_type(
            expr,
            object_type_id,
            &func_type,
            resolved_return_id,
        );

        Ok(final_return_id)
    }

    /// Apply builtin method override to a resolved method.
    fn apply_builtin_override(
        &mut self,
        resolved: ResolvedMethod,
        func_type: &FunctionType,
    ) -> ResolvedMethod {
        match resolved {
            ResolvedMethod::Implemented {
                type_def_id,
                method_name_id,
                trait_name,
                is_builtin,
                external_info,
                concrete_return_hint,
                ..
            } => {
                let return_type_id = func_type.return_type_id;
                let func_type_id = func_type.intern(&mut self.type_arena_mut());
                ResolvedMethod::Implemented {
                    type_def_id,
                    method_name_id,
                    trait_name,
                    func_type_id,
                    return_type_id,
                    is_builtin,
                    external_info,
                    concrete_return_hint,
                }
            }
            other => other,
        }
    }

    /// Check argument count for a method call, handling default parameters.
    fn check_method_arg_count(
        &mut self,
        resolved: &ResolvedMethod,
        func_type: &FunctionType,
        method_call: &MethodCallExpr,
        call_span: Span,
    ) {
        let required_params = if let Some(method_id) = resolved.method_id() {
            self.entity_registry().get_method(method_id).required_params
        } else {
            func_type.params_id.len()
        };
        let total_params = func_type.params_id.len();
        let provided = method_call.args.len();

        if provided < required_params || provided > total_params {
            if required_params < total_params {
                self.add_wrong_arg_count_range(required_params, total_params, provided, call_span);
            } else {
                self.add_wrong_arg_count(total_params, provided, call_span);
            }
        }
    }

    /// Check argument types for an instance method call.
    /// Handles the special case of type-transforming iterator methods (map, flat_map).
    /// Returns the inferred map return type if applicable.
    fn check_instance_method_args(
        &mut self,
        method_call: &MethodCallExpr,
        object_type_id: ArenaTypeId,
        func_type: &FunctionType,
        interner: &Interner,
    ) -> Result<Option<ArenaTypeId>, Vec<TypeError>> {
        let is_map_transform =
            self.is_map_transform(method_call, object_type_id, func_type, interner);
        let mut map_inferred_return_type: Option<ArenaTypeId> = None;

        for (arg, &param_ty_id) in method_call.args.iter().zip(func_type.params_id.iter()) {
            let expr = arg.expr();
            if is_map_transform {
                let inferred = self.check_map_transform_arg(expr, param_ty_id, interner)?;
                if let Some(ret_ty) = inferred {
                    map_inferred_return_type = Some(ret_ty);
                }
            } else {
                let arg_ty_id = self.check_expr_expecting_id(expr, Some(param_ty_id), interner)?;
                if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, arg_ty_id, expr.span);
                }
            }
        }

        Ok(map_inferred_return_type)
    }

    /// Check if this method call is a type-transforming iterator method (map, flat_map).
    fn is_map_transform(
        &self,
        method_call: &MethodCallExpr,
        object_type_id: ArenaTypeId,
        func_type: &FunctionType,
        interner: &Interner,
    ) -> bool {
        let method_name_str = interner.resolve(method_call.method);
        let is_transform_method = method_name_str == "map" || method_name_str == "flat_map";
        let is_on_iterator = {
            let arena = self.type_arena();
            arena.unwrap_interface(object_type_id).is_some()
                || arena.unwrap_runtime_iterator(object_type_id).is_some()
        };
        is_transform_method && is_on_iterator && !func_type.params_id.is_empty()
    }

    /// Check a single argument in a map/flat_map transform context.
    /// Returns the inferred lambda return type if the argument is a lambda.
    fn check_map_transform_arg(
        &mut self,
        arg: &Expr,
        param_ty_id: ArenaTypeId,
        interner: &Interner,
    ) -> Result<Option<ArenaTypeId>, Vec<TypeError>> {
        let modified_expected = {
            let arena = self.type_arena();
            arena
                .unwrap_function(param_ty_id)
                .map(|(params, _ret, _)| params.to_vec())
        };
        let Some(input_params) = modified_expected else {
            // Not a function parameter - check normally
            let arg_ty_id = self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?;
            if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
            }
            return Ok(None);
        };

        // Analyze lambda with only parameter type hints
        let arg_ty_id = if let ExprKind::Lambda(lambda) = &arg.kind {
            let param_only_expected = FunctionType {
                is_closure: false,
                params_id: input_params.into(),
                return_type_id: ArenaTypeId::INVALID,
            };
            let lambda_ty_id =
                self.analyze_lambda(lambda, arg.id, Some(&param_only_expected), interner);
            self.record_expr_type_id(arg, lambda_ty_id);
            lambda_ty_id
        } else {
            self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?
        };

        // Extract the lambda's actual return type
        let lambda_return = {
            let arena = self.type_arena();
            arena
                .unwrap_function(arg_ty_id)
                .map(|(_params, ret, _)| ret)
        };
        Ok(lambda_return)
    }

    /// Compute the resolved return type, handling map/flat_map transform overrides.
    fn compute_resolved_return_type(
        &mut self,
        resolved: &ResolvedMethod,
        map_inferred_return_type: Option<ArenaTypeId>,
        method_call: &MethodCallExpr,
        interner: &Interner,
    ) -> ArenaTypeId {
        let Some(inferred_elem) = map_inferred_return_type else {
            return resolved.return_type_id();
        };

        let method_name_str = interner.resolve(method_call.method);
        let new_elem_type = if method_name_str == "flat_map" {
            self.type_arena()
                .unwrap_array(inferred_elem)
                .unwrap_or(inferred_elem)
        } else {
            inferred_elem
        };

        let iterator_interface_id = self
            .resolver(interner)
            .resolve_type_str_or_interface("Iterator", &self.entity_registry());
        if let Some(iface_id) = iterator_interface_id {
            self.type_arena_mut()
                .interface(iface_id, smallvec::smallvec![new_elem_type])
        } else {
            resolved.return_type_id()
        }
    }

    /// Compute and store the substituted return type for codegen.
    /// Handles generic class type argument substitution.
    fn compute_substituted_return_type(
        &mut self,
        expr: &Expr,
        object_type_id: ArenaTypeId,
        func_type: &FunctionType,
        resolved_return_id: ArenaTypeId,
    ) -> ArenaTypeId {
        // Check if this is a generic class with type args that need substitution
        let type_args_and_def = {
            let arena = self.type_arena();
            arena
                .unwrap_class_or_struct(object_type_id)
                .map(|(id, args, _)| (id, args.clone()))
        };
        if let Some((type_def_id, type_args)) = type_args_and_def
            && !type_args.is_empty()
        {
            let generic_info = self.entity_registry().type_generic_info(type_def_id);
            if let Some(generic_info) = generic_info {
                let subs: FxHashMap<_, _> = generic_info
                    .type_params
                    .iter()
                    .zip(type_args.iter())
                    .map(|(param, &arg)| (param.name_id, arg))
                    .collect();
                let substituted = self
                    .type_arena_mut()
                    .substitute(func_type.return_type_id, &subs);
                self.results
                    .substituted_return_types
                    .insert(expr.id, substituted);
                return substituted;
            }
        }

        // For interface methods, the return type is already substituted in resolved.
        // Store it for codegen to use.
        self.results
            .substituted_return_types
            .insert(expr.id, resolved_return_id);
        resolved_return_id
    }
}
