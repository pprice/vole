//! Declaration signature collection — implement block processing.

use super::*;

impl Analyzer {
    pub(super) fn collect_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
    ) {
        // Infer type param scope from the target class definition.
        // This enables `implement Iterator<K> for MapKeyIterator<K, V>` where K and V
        // are not explicitly declared but inferred from MapKeyIterator's type params.
        let inferred_scope = self.infer_implement_type_params(&impl_block.target_type, interner);
        let has_type_param_scope = !inferred_scope.is_empty();
        if has_type_param_scope {
            self.env.type_param_stack.push_scope(inferred_scope);
        }

        // Extract trait name symbol from trait_type (if present)
        let trait_name = impl_block.trait_type.as_ref().and_then(interface_base_name);

        // Resolve interface from trait_type if specified
        let resolved_interface = impl_block
            .trait_type
            .as_ref()
            .and_then(|trait_type| self.resolve_interface_path(trait_type, interner));

        // Validate trait exists if specified
        if impl_block.trait_type.is_some() && resolved_interface.is_none() {
            let trait_type = impl_block
                .trait_type
                .as_ref()
                .expect("trait_type checked is_some above");

            // Provide more specific error for qualified paths
            if is_qualified_path(trait_type) {
                if let TypeExprKind::QualifiedPath { segments, .. } = &trait_type.kind {
                    let first_sym = segments[0];
                    // Check if first segment is a module
                    if let Some(type_id) = self.get_variable_type_id(first_sym) {
                        if self.type_arena().unwrap_module(type_id).is_none() {
                            // First segment exists but is not a module
                            self.add_error(
                                SemanticError::ExpectedModule {
                                    name: interner.resolve(first_sym).to_string(),
                                    found: self.type_display_id(type_id),
                                    span: impl_block.span.into(),
                                },
                                impl_block.span,
                            );
                        } else {
                            // Module exists but interface not found in exports
                            self.add_error(
                                SemanticError::UnknownInterface {
                                    name: format_type_expr(trait_type, interner),
                                    span: impl_block.span.into(),
                                },
                                impl_block.span,
                            );
                        }
                    } else {
                        // First segment not found
                        self.add_error(
                            SemanticError::UndefinedVariable {
                                name: interner.resolve(first_sym).to_string(),
                                span: impl_block.span.into(),
                            },
                            impl_block.span,
                        );
                    }
                }
            } else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(trait_type, interner),
                        span: impl_block.span.into(),
                    },
                    impl_block.span,
                );
            }
        }

        let target_type_id = self.resolve_type_id(&impl_block.target_type, interner);

        // Validate target type exists
        if target_type_id.is_invalid() {
            let type_name = match &impl_block.target_type.kind {
                TypeExprKind::Named(sym) => interner.resolve(*sym).to_string(),
                _ => "unknown".to_string(),
            };
            self.add_error(
                SemanticError::UnknownImplementType {
                    name: type_name,
                    span: impl_block.span.into(),
                },
                impl_block.span,
            );
        }

        // Extract impl_type_id with borrow scoped to just this call
        let impl_type_id = {
            let arena = self.type_arena();
            ImplTypeId::from_type_id(target_type_id, &arena, &self.entity_registry())
        };

        if let Some(impl_type_id) = impl_type_id {
            // Get TypeDefId for the target type (for EntityRegistry updates)
            // Use impl_type_id.name_id() which we already have, avoiding name_id_for_type
            let entity_type_id = self
                .type_arena()
                .type_def_id(target_type_id)
                .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

            // Get interface TypeDefId if implementing an interface
            // Use resolved_interface if available, otherwise fall back to trait_name lookup
            let (interface_type_id, interface_type_arg_exprs) =
                if let Some((id, args)) = resolved_interface {
                    (Some(id), args)
                } else if let Some(name) = trait_name {
                    let iface_str = interner.resolve(name);
                    let id = self
                        .resolver(interner)
                        .resolve_type_str_or_interface(iface_str, &self.entity_registry());
                    (id, &[] as &[TypeExpr])
                } else {
                    (None, &[] as &[TypeExpr])
                };

            // Resolve interface type arguments (e.g., <i64> from implement Producer<i64>)
            let interface_type_args: Vec<ArenaTypeId> = interface_type_arg_exprs
                .iter()
                .map(|arg| self.resolve_type_id(arg, interner))
                .collect();

            // Extract target type args (e.g., [i64] from Box<i64>)
            let target_type_args: Vec<ArenaTypeId> = {
                let arena = self.type_arena();
                arena
                    .unwrap_nominal(target_type_id)
                    .map(|(_, args, _)| args.to_vec())
                    .unwrap_or_default()
            };

            // Check for duplicate implementation before registering
            // find_existing_implementation returns:
            // - None: no existing implementation
            // - Some(None): implementation from class declaration (no span) - OK to add implement block
            // - Some(Some(span)): implementation from another implement block - may be duplicate
            enum ImplAction {
                AddNew,
                SetSpan,
                Skip, // Same implement block already processed (e.g., module imported multiple times)
                Duplicate {
                    interface_name: String,
                    first_span: miette::SourceSpan,
                },
            }
            let current_span: miette::SourceSpan = impl_block.span.into();
            let action = if let Some(entity_type_id) = entity_type_id
                && let Some(iface_id) = interface_type_id
            {
                match self
                    .entity_registry()
                    .find_existing_implementation(entity_type_id, iface_id)
                {
                    Some(Some(first_span)) => {
                        // If the spans match, this is the same implement block being
                        // processed again (e.g., when a module is imported by multiple
                        // test files). Skip silently rather than reporting duplicate.
                        if first_span == current_span {
                            ImplAction::Skip
                        } else {
                            let interface_name = self
                                .name_table()
                                .last_segment_str(self.entity_registry().get_type(iface_id).name_id)
                                .unwrap_or_else(|| "?".to_string());
                            ImplAction::Duplicate {
                                interface_name,
                                first_span,
                            }
                        }
                    }
                    Some(None) => ImplAction::SetSpan,
                    None => ImplAction::AddNew,
                }
            } else {
                ImplAction::AddNew
            };

            match action {
                ImplAction::Duplicate {
                    interface_name,
                    first_span,
                } => {
                    let target_name = format_type_expr(&impl_block.target_type, interner);
                    self.add_error(
                        SemanticError::DuplicateImplementation {
                            interface: interface_name,
                            target: target_name,
                            span: impl_block.span.into(),
                            first_impl: first_span,
                        },
                        impl_block.span,
                    );
                    if has_type_param_scope {
                        self.env.type_param_stack.pop();
                    }
                    return; // Skip processing the duplicate implement block
                }
                ImplAction::Skip => {
                    // Same implement block already processed - skip silently
                    if has_type_param_scope {
                        self.env.type_param_stack.pop();
                    }
                    return;
                }
                ImplAction::SetSpan => {
                    if let Some(entity_type_id) = entity_type_id
                        && let Some(iface_id) = interface_type_id
                    {
                        self.entity_registry_mut().set_implementation_span(
                            entity_type_id,
                            iface_id,
                            impl_block.span.into(),
                        );
                    }
                }
                ImplAction::AddNew => {
                    if let Some(entity_type_id) = entity_type_id
                        && let Some(iface_id) = interface_type_id
                    {
                        self.entity_registry_mut()
                            .add_implementation_with_target_args(
                                entity_type_id,
                                iface_id,
                                interface_type_args,
                                target_type_args,
                                Some(impl_block.span.into()),
                            );
                    }
                }
            }

            for method in &impl_block.methods {
                // Validate type annotations to emit errors for unknown types
                self.validate_method_types(
                    &method.params,
                    &method.return_type,
                    method.span,
                    interner,
                    None,
                );

                // Use target_type_id as Self when resolving method signatures
                // This ensures `Self` in method params/return types resolves to the implementing type
                // Skip explicit `self` parameter — implement block methods have self added
                // implicitly by codegen (via SelfParam). Including it in the signature
                // would double-count it, causing argument count mismatches.
                let params_id: Vec<ArenaTypeId> = method
                    .params
                    .iter()
                    .filter(|p| interner.resolve(p.name) != "self")
                    .map(|p| self.resolve_type_id_with_self(&p.ty, interner, Some(target_type_id)))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id_with_self(t, interner, Some(target_type_id)))
                    .unwrap_or_else(|| self.type_arena().void());
                let func_type = FunctionType::from_ids(&params_id, return_type_id, false);

                let method_name_id = self.method_name_id(method.name, interner);

                // Only register in the ImplementRegistry for non-file-scoped methods.
                // File-scoped extension methods (extend Type {}) are registered only in
                // EntityRegistry with a module restriction. Registering them in the
                // ImplementRegistry would bypass the module restriction check since that
                // registry has no module awareness.
                if !impl_block.is_file_scoped {
                    let method_impl = MethodImpl::user_defined(func_type.clone());
                    let method_impl = match trait_name {
                        Some(name) => method_impl.with_trait_name(name),
                        None => method_impl,
                    };
                    self.implement_registry_mut().register_method(
                        impl_type_id,
                        method_name_id,
                        method_impl,
                    );
                }

                // Register in EntityRegistry.methods_by_type for all implement blocks
                // This enables codegen to look up method signatures via find_method_on_type
                if let Some(entity_type_id) = entity_type_id {
                    // Build full method name for entity registry
                    let type_name_str = match &impl_block.target_type.kind {
                        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                            interner.resolve(*sym).to_string()
                        }
                        TypeExprKind::Primitive(prim) => {
                            let name_id = self.name_table().primitives.from_ast(*prim);
                            self.name_table().display(name_id)
                        }
                        _ => "unknown".to_string(),
                    };
                    let method_name_str = interner.resolve(method.name);
                    let full_method_name_id = self.name_table_mut().intern_raw(
                        self.module.current_module,
                        &[&type_name_str, method_name_str],
                    );

                    // Intern the signature in the arena
                    let signature_id = func_type.clone().intern(&mut self.type_arena_mut());

                    // `extend Type { }` (no interface) produces file-scoped methods:
                    // only visible within the defining module. Mark with defining_module.
                    let is_file_scoped = impl_block.is_file_scoped;
                    let mut method_builder = MethodDefBuilder::new(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                    )
                    .has_default(false); // implement block methods don't have defaults
                    if is_file_scoped {
                        method_builder = method_builder.defining_module(self.module.current_module);
                    }
                    method_builder.register(&mut self.entity_registry_mut());

                    // Also add method binding if implementing an interface
                    if let Some(interface_type_id) = interface_type_id {
                        use crate::entity_defs::MethodBinding;
                        self.entity_registry_mut().add_method_binding(
                            entity_type_id,
                            interface_type_id,
                            MethodBinding {
                                method_name: method_name_id,
                                func_type,
                                is_builtin: false,
                                external_info: None,
                            },
                        );
                    }
                }
            }

            // Analyze external block if present
            if let Some(ref external) = impl_block.external {
                self.analyze_external_block(external, target_type_id, trait_name, interner);
            }

            // Register static methods from statics block (if present)
            if let Some(ref statics_block) = impl_block.statics {
                // Get entity type id for registering static methods
                // Use impl_type_id.name_id() which we already have
                let entity_type_id = self
                    .type_arena()
                    .type_def_id(target_type_id)
                    .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

                if let Some(entity_type_id) = entity_type_id {
                    let type_name_str = match &impl_block.target_type.kind {
                        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                            interner.resolve(*sym).to_string()
                        }
                        TypeExprKind::Primitive(prim) => {
                            let name_id = self.name_table().primitives.from_ast(*prim);
                            self.name_table_mut().display(name_id)
                        }
                        _ => "unknown".to_string(),
                    };

                    // Register static methods
                    for method in &statics_block.methods {
                        let method_name_str = interner.resolve(method.name).to_string();
                        let builtin_mod = self.name_table_mut().builtin_module();
                        let method_name_id = self
                            .name_table_mut()
                            .intern_raw(builtin_mod, &[&method_name_str]);
                        let full_method_name_id = self.name_table_mut().intern_raw(
                            self.module.current_module,
                            &[&type_name_str, &method_name_str],
                        );

                        let params_id: Vec<ArenaTypeId> = method
                            .params
                            .iter()
                            .map(|p| self.resolve_type_id(&p.ty, interner))
                            .collect();
                        let return_type_id = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type_id(t, interner))
                            .unwrap_or_else(|| self.type_arena().void());

                        let signature_id =
                            FunctionType::from_ids(&params_id, return_type_id, false)
                                .intern(&mut self.type_arena_mut());

                        let required_params =
                            self.validate_param_defaults(&method.params, interner);
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
                        .has_default(false) // has_default refers to interface method default body
                        .param_defaults(required_params, param_defaults)
                        .register(&mut self.entity_registry_mut());
                    }

                    // Register external static methods
                    for external in &statics_block.external_blocks {
                        for func in &external.functions {
                            let method_name_str = interner.resolve(func.vole_name).to_string();
                            let builtin_mod = self.name_table_mut().builtin_module();
                            let method_name_id = self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&method_name_str]);
                            let full_method_name_id = self.name_table_mut().intern_raw(
                                self.module.current_module,
                                &[&type_name_str, &method_name_str],
                            );

                            let params_id: Vec<ArenaTypeId> = func
                                .params
                                .iter()
                                .map(|p| self.resolve_type_id(&p.ty, interner))
                                .collect();
                            let return_type_id = func
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_id(t, interner))
                                .unwrap_or_else(|| self.type_arena().void());

                            let signature_id =
                                FunctionType::from_ids(&params_id, return_type_id, false)
                                    .intern(&mut self.type_arena_mut());

                            let native_name_str = func
                                .native_name
                                .clone()
                                .unwrap_or_else(|| method_name_str.clone());
                            // Compute NameIds before calling entity_registry_mut to avoid borrow conflicts
                            let builtin_mod = self.name_table_mut().builtin_module();
                            let module_path_id = self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&external.module_path]);
                            let native_name_id = self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]);

                            MethodDefBuilder::new(
                                entity_type_id,
                                method_name_id,
                                full_method_name_id,
                                signature_id,
                            )
                            .is_static(true)
                            .has_default(false)
                            .external_binding(Some(ExternalMethodInfo {
                                module_path: module_path_id,
                                native_name: native_name_id,
                            }))
                            .register(&mut self.entity_registry_mut());
                        }
                    }
                }
            }
        }

        // Pop the inferred type param scope if we pushed one
        if has_type_param_scope {
            self.env.type_param_stack.pop();
        }
    }

    /// Infer type parameter scope for a standalone implement block from its target class.
    ///
    /// When an implement block targets a generic class (e.g., `implement Iterator<K> for
    /// MapKeyIterator<K, V>`), the type params K and V are not declared in the AST node.
    /// This method looks up the target class definition to find its declared type params,
    /// then matches the syntax args from the implement block positionally to build a scope.
    ///
    /// Returns a non-empty scope only when the target type is generic and has unresolved
    /// type arguments (i.e., args that don't resolve to known concrete types).
    pub(in crate::analyzer) fn infer_implement_type_params(
        &mut self,
        target_type: &TypeExpr,
        interner: &Interner,
    ) -> TypeParamScope {
        let mut scope = TypeParamScope::new();

        // Only Generic target types can introduce type params
        let TypeExprKind::Generic { name, args } = &target_type.kind else {
            return scope;
        };

        // Look up the target class definition
        let name_str = interner.resolve(*name);
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(name_str, &self.entity_registry());
        let Some(type_def_id) = type_def_id else {
            return scope;
        };

        // Get the class's declared type params from its generic info
        let declared_param_count = self
            .entity_registry()
            .get_type(type_def_id)
            .generic_info
            .as_ref()
            .map(|info| info.type_params.len())
            .unwrap_or(0);

        if declared_param_count == 0 || args.len() != declared_param_count {
            return scope;
        }

        // Match each syntax arg against the class's declared params.
        // An arg is a type param if it's a Named symbol that doesn't resolve to a known type.
        let mut seen = Vec::new();
        for arg in args {
            if let TypeExprKind::Named(sym) = &arg.kind {
                let arg_name = interner.resolve(*sym);
                let is_known_type = self
                    .resolver(interner)
                    .resolve_type_str_or_interface(arg_name, &self.entity_registry())
                    .is_some();
                if !is_known_type && !seen.contains(sym) {
                    seen.push(*sym);
                    let builtin_mod = self.name_table_mut().builtin_module();
                    let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[arg_name]);
                    scope.add(TypeParamInfo {
                        name: *sym,
                        name_id: tp_name_id,
                        constraint: None,
                        type_param_id: None,
                        variance: TypeParamVariance::default(),
                    });
                }
            }
        }

        scope
    }
}
