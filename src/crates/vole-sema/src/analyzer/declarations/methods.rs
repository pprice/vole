//! Declaration signature collection — method registration helpers.

use super::*;

impl Analyzer {
    /// Validate field default ordering and collect which fields have defaults.
    /// Returns a Vec<bool> indicating whether each field has a default.
    /// Emits errors if non-defaulted fields come after defaulted fields.
    pub(super) fn validate_field_defaults(
        &mut self,
        fields: &[AstFieldDef],
        interner: &Interner,
    ) -> Vec<bool> {
        let (_, has_default_vec) = validate_defaults(fields, interner, |field, span| {
            self.add_error(
                SemanticError::RequiredFieldAfterDefaulted {
                    field,
                    span: span.into(),
                },
                span,
            );
        });
        has_default_vec
    }

    /// Build method name IDs for registration.
    /// Returns (method_name_id, full_method_name_id).
    pub(super) fn build_method_names(
        &mut self,
        type_name: Symbol,
        method_name: Symbol,
        interner: &Interner,
    ) -> (NameId, NameId) {
        let builtin_mod = self.name_table_mut().builtin_module();
        let method_name_str = interner.resolve(method_name);
        let method_name_id = self
            .name_table_mut()
            .intern_raw(builtin_mod, &[method_name_str]);
        let type_name_str = interner.resolve(type_name);
        let full_method_name_id = self.name_table_mut().intern_raw(
            self.module.current_module,
            &[type_name_str, method_name_str],
        );
        (method_name_id, full_method_name_id)
    }

    /// Build a method signature by resolving params and return type.
    /// Uses the provided type param scope and optional self_type for resolution.
    pub(super) fn build_method_signature(
        &mut self,
        params: &[Param],
        return_type: &Option<TypeExpr>,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        self_type: Option<ArenaTypeId>,
    ) -> ArenaTypeId {
        let module_id = self.module.current_module;
        let params_id: Vec<ArenaTypeId> = params
            .iter()
            .map(|p| {
                if let Some(scope) = type_param_scope {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.ctx.db,
                        interner,
                        module_id,
                        scope,
                    );
                    ctx.self_type = self_type;
                    resolve_type_to_id(&p.ty, &mut ctx)
                } else if let Some(self_type_id) = self_type {
                    self.resolve_type_id_with_self(&p.ty, interner, Some(self_type_id))
                } else {
                    self.resolve_type_id(&p.ty, interner)
                }
            })
            .collect();

        // Check that never is not used in method parameters
        for (param, &type_id) in params.iter().zip(&params_id) {
            self.check_type_annotation_constraints(type_id, &param.ty, param.span);
        }

        let return_type_id = return_type
            .as_ref()
            .map(|t| {
                if let Some(scope) = type_param_scope {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.ctx.db,
                        interner,
                        module_id,
                        scope,
                    );
                    ctx.self_type = self_type;
                    resolve_type_to_id(t, &mut ctx)
                } else if let Some(self_type_id) = self_type {
                    self.resolve_type_id_with_self(t, interner, Some(self_type_id))
                } else {
                    self.resolve_type_id(t, interner)
                }
            })
            .unwrap_or_else(|| self.type_arena().void());

        FunctionType::from_ids(&params_id, return_type_id, false).intern(&mut self.type_arena_mut())
    }

    /// Validate a type expression and emit an error if it resolves to an unknown type.
    /// This is called during type resolution to provide proper error messages
    /// for unknown types in type annotations.
    pub(in crate::analyzer) fn validate_type_annotation(
        &mut self,
        type_expr: &TypeExpr,
        span: Span,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        // For TypeExprKind::Named, check if the type is resolvable
        match &type_expr.kind {
            TypeExprKind::Named(sym) => {
                let name_str = interner.resolve(*sym);
                // Skip primitive types, "void", and well-known sentinel types
                if matches!(name_str, "void" | "nil" | "Done") {
                    return;
                }
                // Check if it's a type parameter in scope
                if let Some(scope) = type_param_scope
                    && scope.get(*sym).is_some()
                {
                    return;
                }
                // Check from type_param_stack too
                if self
                    .env
                    .type_param_stack
                    .current()
                    .is_some_and(|s| s.get(*sym).is_some())
                {
                    return;
                }
                // Try to resolve the type (with interface/class fallback for prelude types)
                let resolved = self
                    .resolver(interner)
                    .resolve_type_or_interface(*sym, &self.entity_registry());
                if resolved.is_none() {
                    self.add_error(
                        SemanticError::UnknownType {
                            name: name_str.to_string(),
                            hint: unknown_type_hint(name_str),
                            span: span.into(),
                        },
                        span,
                    );
                }
            }
            TypeExprKind::Generic { name, args } => {
                // Validate the base type
                self.validate_type_annotation(
                    &TypeExpr::synthetic(TypeExprKind::Named(*name)),
                    span,
                    interner,
                    type_param_scope,
                );
                // Validate type arguments
                for arg in args {
                    self.validate_type_annotation(arg, span, interner, type_param_scope);
                }
            }
            TypeExprKind::Array(elem) | TypeExprKind::Optional(elem) => {
                self.validate_type_annotation(elem, span, interner, type_param_scope);
            }
            TypeExprKind::FixedArray { element, .. } => {
                self.validate_type_annotation(element, span, interner, type_param_scope);
            }
            TypeExprKind::Tuple(elements) => {
                for elem in elements {
                    self.validate_type_annotation(elem, span, interner, type_param_scope);
                }
            }
            TypeExprKind::Union(variants) => {
                for variant in variants {
                    self.validate_type_annotation(variant, span, interner, type_param_scope);
                    // Structs are allowed in unions via auto-boxing (v-7d4b)
                }
            }
            TypeExprKind::Function {
                params,
                return_type,
            } => {
                for param in params {
                    self.validate_type_annotation(param, span, interner, type_param_scope);
                }
                self.validate_type_annotation(return_type, span, interner, type_param_scope);
            }
            TypeExprKind::Fallible {
                success_type,
                error_type,
            } => {
                self.validate_type_annotation(success_type, span, interner, type_param_scope);
                self.validate_type_annotation(error_type, span, interner, type_param_scope);
            }
            // Primitives, SelfType, etc. don't need validation
            _ => {}
        }
    }

    /// Validate method parameter and return type annotations, emitting errors for unknown types.
    pub(super) fn validate_method_types(
        &mut self,
        params: &[Param],
        return_type: &Option<TypeExpr>,
        func_span: Span,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        for param in params {
            self.validate_type_annotation(&param.ty, param.span, interner, type_param_scope);
        }
        if let Some(ret_ty) = return_type {
            // Use the function span for return type errors since TypeExpr doesn't have its own span
            self.validate_type_annotation(ret_ty, func_span, interner, type_param_scope);
        }
    }

    /// Register an instance method from a FuncDecl.
    /// Used for class instance methods.
    pub(super) fn register_instance_method(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        method: &FuncDecl,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        self_type: Option<ArenaTypeId>,
    ) {
        // Validate type annotations to emit errors for unknown types
        self.validate_method_types(
            &method.params,
            &method.return_type,
            method.span,
            interner,
            type_param_scope,
        );

        let (method_name_id, full_method_name_id) =
            self.build_method_names(type_name, method.name, interner);
        // Filter out explicit `self` parameter — instance methods have self added
        // implicitly by codegen. Including it in the signature would double-count it.
        let non_self_params: Vec<_> = method
            .params
            .iter()
            .filter(|p| interner.resolve(p.name) != "self")
            .cloned()
            .collect();
        let signature_id = self.build_method_signature(
            &non_self_params,
            &method.return_type,
            interner,
            type_param_scope,
            self_type,
        );

        let required_params = self.validate_param_defaults(&non_self_params, interner);
        let param_defaults: Vec<Option<Box<Expr>>> = non_self_params
            .iter()
            .map(|p| p.default_value.clone())
            .collect();

        MethodDefBuilder::new(
            entity_type_id,
            method_name_id,
            full_method_name_id,
            signature_id,
        )
        .has_default(false) // instance methods don't have defaults (implementation defaults)
        .param_defaults(required_params, param_defaults)
        .register(&mut self.entity_registry_mut());
    }

    /// Register a static method from an InterfaceMethod.
    /// Used for class static methods.
    pub(super) fn register_static_method_helper(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        method: &InterfaceMethod,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        method_type_params: Vec<TypeParamInfo>,
    ) {
        let (method_name_id, full_method_name_id) =
            self.build_method_names(type_name, method.name, interner);

        // Build merged scope if method has its own type params
        let merged_scope: Option<TypeParamScope>;
        let scope_for_resolution = if !method.type_params.is_empty() {
            let mut scope = type_param_scope
                .cloned()
                .unwrap_or_else(TypeParamScope::new);
            let method_scope = self.build_unconstrained_scope(&method.type_params, interner);
            scope.extend(method_scope.params());
            merged_scope = Some(scope);
            merged_scope.as_ref()
        } else {
            type_param_scope
        };

        // Validate type annotations to emit errors for unknown types
        // Must be after building merged_scope so method's own type params are in scope
        self.validate_method_types(
            &method.params,
            &method.return_type,
            method.span,
            interner,
            scope_for_resolution,
        );

        let signature_id = self.build_method_signature(
            &method.params,
            &method.return_type,
            interner,
            scope_for_resolution,
            None, // static methods don't have self
        );

        let has_default = method.is_default || method.body.is_some();
        let required_params = self.validate_param_defaults(&method.params, interner);
        let param_defaults: Vec<Option<Box<Expr>>> = method
            .params
            .iter()
            .map(|p| p.default_value.clone())
            .collect();

        MethodDefBuilder::new(
            entity_type_id,
            method_name_id,
            full_method_name_id,
            signature_id,
        )
        .is_static(true)
        .has_default(has_default)
        .method_type_params(method_type_params)
        .param_defaults(required_params, param_defaults)
        .register(&mut self.entity_registry_mut());
    }

    /// Build method type params with resolved constraints for a static method.
    pub(super) fn build_method_type_params(
        &mut self,
        method: &InterfaceMethod,
        type_param_scope: Option<&TypeParamScope>,
        interner: &Interner,
    ) -> Vec<TypeParamInfo> {
        if method.type_params.is_empty() {
            return Vec::new();
        }

        // Build merged scope for constraint resolution (parent + method type params)
        let mut merged_scope = type_param_scope
            .cloned()
            .unwrap_or_else(TypeParamScope::new);
        let method_scope = self.build_unconstrained_scope(&method.type_params, interner);
        merged_scope.extend(method_scope.params());

        // Resolve constraints using merged scope
        method
            .type_params
            .iter()
            .map(|tp| {
                let mut info = self.intern_type_param(tp, interner);
                info.constraint = tp.constraint.as_ref().and_then(|c| {
                    self.resolve_type_param_constraint(c, &merged_scope, interner, tp.span)
                });
                info
            })
            .collect()
    }

    /// Register an external method from an ExternalFunc.
    /// Used for class external methods.
    pub(super) fn register_external_method(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        func: &ExternalFunc,
        module_path: &str,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        let (method_name_id, full_method_name_id) =
            self.build_method_names(type_name, func.vole_name, interner);
        let signature_id = self.build_method_signature(
            &func.params,
            &func.return_type,
            interner,
            type_param_scope,
            None, // external methods don't have self
        );

        let method_name_str = interner.resolve(func.vole_name);
        let native_name_str = func
            .native_name
            .clone()
            .unwrap_or_else(|| method_name_str.to_string());
        let builtin_mod = self.name_table_mut().builtin_module();

        self.entity_registry_mut().register_method_with_binding(
            entity_type_id,
            method_name_id,
            full_method_name_id,
            signature_id,
            false, // external methods don't have defaults
            Some(ExternalMethodInfo {
                module_path: self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[module_path]),
                native_name: self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[&native_name_str]),
            }),
        );
    }
}
