//! Declaration signature collection — interface definition collection.

use super::*;

impl Analyzer {
    pub(super) fn collect_interface_def(
        &mut self,
        interface_decl: &InterfaceDecl,
        interner: &Interner,
    ) {
        // Build type params with resolved constraints
        let type_param_scope =
            self.build_type_params_with_constraints(&interface_decl.type_params, interner);

        // Use current_module for proper module-qualified NameIds
        let name_str = interner.resolve(interface_decl.name).to_string();
        let name_id = self
            .name_table_mut()
            .intern_raw(self.module.current_module, &[&name_str]);

        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("interface shell registered in register_all_type_shells");

        // Skip if already processed (e.g., from a previous analysis of the same module
        // in a shared cache scenario). Check if methods are already registered.
        if !self
            .entity_registry()
            .get_type(entity_type_id)
            .methods
            .is_empty()
        {
            return;
        }

        // Validate interface method type annotations
        for method in &interface_decl.methods {
            self.validate_method_types(
                &method.params,
                &method.return_type,
                method.span,
                interner,
                Some(&type_param_scope),
            );
        }

        let module_id = self.module.current_module;
        let mut type_ctx = TypeResolutionContext::with_type_params(
            &self.ctx.db,
            interner,
            module_id,
            &type_param_scope,
        );

        // Resolve field types directly to TypeId
        let resolved_fields: Vec<(Symbol, ArenaTypeId)> = interface_decl
            .fields
            .iter()
            .map(|f| (f.name, resolve_type_to_id(&f.ty, &mut type_ctx)))
            .collect();

        // Collect method names with default external bindings (from `default external` blocks)
        let default_external_methods: HashSet<Symbol> = interface_decl
            .external_blocks
            .iter()
            .filter(|ext| ext.is_default)
            .flat_map(|ext| ext.functions.iter().map(|f| f.vole_name))
            .collect();

        // Collect errors for methods with bodies that aren't marked as default
        let body_without_default_errors: Vec<_> = interface_decl
            .methods
            .iter()
            .filter(|m| {
                m.body.is_some() && !m.is_default && !default_external_methods.contains(&m.name)
            })
            .map(|m| (interner.resolve(m.name).to_string(), m.span))
            .collect();

        // Build interface_methods for Type and collect method data for EntityRegistry registration
        // We resolve types once to TypeId and reuse the data
        // Get void type before the loop to avoid borrowing db while type_ctx is borrowed
        let void_type = self.type_arena().void();
        let method_data: Vec<(Symbol, String, Vec<ArenaTypeId>, ArenaTypeId, bool)> =
            interface_decl
                .methods
                .iter()
                .map(|m| {
                    let name = m.name;
                    let name_str = interner.resolve(m.name).to_string();
                    let params_id: Vec<ArenaTypeId> = m
                        .params
                        .iter()
                        .map(|p| resolve_type_to_id(&p.ty, &mut type_ctx))
                        .collect();
                    let return_type_id = m
                        .return_type
                        .as_ref()
                        .map(|t| resolve_type_to_id(t, &mut type_ctx))
                        .unwrap_or(void_type);
                    let has_default = m.is_default
                        || m.body.is_some()
                        || default_external_methods.contains(&m.name);
                    (name, name_str, params_id, return_type_id, has_default)
                })
                .collect();

        let _interface_methods: Vec<crate::types::InterfaceMethodType> = method_data
            .iter()
            .map(|(name, _, params_id, return_type_id, has_default)| {
                let method_name_id = self.method_name_id(*name, interner);
                crate::types::InterfaceMethodType {
                    name: method_name_id,
                    has_default: *has_default,
                    params_id: params_id.iter().copied().collect(),
                    return_type_id: *return_type_id,
                }
            })
            .collect();

        // Emit errors for methods with bodies that aren't marked as default
        for (method_name, span) in body_without_default_errors {
            self.add_error(
                SemanticError::InterfaceMethodBodyWithoutDefault {
                    method: method_name,
                    span: span.into(),
                },
                span,
            );
        }

        // Collect method names for external block validation
        let method_names: HashSet<Symbol> = method_data.iter().map(|(name, ..)| *name).collect();

        let mut external_methods: FxHashMap<String, ExternalMethodInfo> = FxHashMap::default();
        for external in &interface_decl.external_blocks {
            for func in &external.functions {
                if !method_names.contains(&func.vole_name) {
                    let ty = interner.resolve(interface_decl.name).to_string();
                    let method = interner.resolve(func.vole_name).to_string();
                    self.add_error(
                        SemanticError::UnknownMethod {
                            ty,
                            method,
                            span: func.span.into(),
                        },
                        func.span,
                    );
                    continue;
                }
                let native_name_str = func
                    .native_name
                    .clone()
                    .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                let method_name_str = interner.resolve(func.vole_name).to_string();
                // Extract name IDs before struct literal to avoid overlapping borrows
                let (module_path, native_name) = {
                    let builtin_mod = self.name_table_mut().builtin_module();
                    let mut name_table = self.name_table_mut();
                    (
                        name_table.intern_raw(builtin_mod, &[&external.module_path]),
                        name_table.intern_raw(builtin_mod, &[&native_name_str]),
                    )
                };
                external_methods.insert(
                    method_name_str,
                    ExternalMethodInfo {
                        module_path,
                        native_name,
                    },
                );
            }
        }

        // Set type parameters in EntityRegistry (using NameIds only)
        self.register_type_params_on_entity(entity_type_id, &type_param_scope);

        // Register extends relationships
        // Collect parent type IDs first (separate from mutation to avoid borrow conflicts)
        let extends_parents: Vec<(NameId, Option<TypeDefId>)> = interface_decl
            .extends
            .iter()
            .map(|&parent_sym| {
                let parent_str = interner.resolve(parent_sym);
                let parent_name_id = self
                    .name_table_mut()
                    .intern_raw(self.module.current_module, &[parent_str]);
                let parent_type_id = self.entity_registry().type_by_name(parent_name_id);
                (parent_name_id, parent_type_id)
            })
            .collect();
        let _extends_type_ids: Vec<TypeDefId> = extends_parents
            .into_iter()
            .filter_map(|(_, parent_type_id)| {
                if let Some(parent_type_id) = parent_type_id {
                    self.entity_registry_mut()
                        .add_extends(entity_type_id, parent_type_id);
                    Some(parent_type_id)
                } else {
                    None
                }
            })
            .collect();

        // Register methods in EntityRegistry (with external bindings)
        for (_, method_name_str, params_id, return_type_id, has_default) in &method_data {
            let builtin_mod = self.name_table_mut().builtin_module();
            let method_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[method_name_str]);
            let full_method_name_id = self
                .name_table_mut()
                .intern_raw(self.module.current_module, &[&name_str, method_name_str]);
            let signature_id = FunctionType::from_ids(params_id, *return_type_id, false)
                .intern(&mut self.type_arena_mut());
            // Look up external binding for this method
            let external_binding = external_methods.get(method_name_str).copied();
            self.entity_registry_mut().register_method_with_binding(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature_id,
                *has_default,
                external_binding,
            );
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics_block) = interface_decl.statics {
            self.register_interface_statics(
                statics_block,
                entity_type_id,
                &name_str,
                &type_param_scope,
                interner,
            );
        }

        // Register fields in EntityRegistry (for interface field requirements)
        for (i, (field_name, field_type_id)) in resolved_fields.iter().enumerate() {
            let field_name_str = interner.resolve(*field_name).to_string();
            let builtin_mod = self.name_table_mut().builtin_module();
            let field_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[&field_name_str]);
            let full_field_name_id = self
                .name_table_mut()
                .intern_raw(self.module.current_module, &[&name_str, &field_name_str]);
            self.entity_registry_mut().register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                *field_type_id,
                i,
            );
        }
    }

    /// Register static methods from an interface's `statics` block.
    fn register_interface_statics(
        &mut self,
        statics_block: &StaticsBlock,
        entity_type_id: TypeDefId,
        name_str: &str,
        type_param_scope: &TypeParamScope,
        interner: &Interner,
    ) {
        let module_id = self.module.current_module;

        // Collect static method names with default external bindings
        let default_static_external_methods: HashSet<Symbol> = statics_block
            .external_blocks
            .iter()
            .filter(|ext| ext.is_default)
            .flat_map(|ext| ext.functions.iter().map(|f| f.vole_name))
            .collect();

        // Build external methods map for static methods
        let mut static_external_methods: FxHashMap<String, ExternalMethodInfo> =
            FxHashMap::default();
        for external in &statics_block.external_blocks {
            for func in &external.functions {
                let native_name_str = func
                    .native_name
                    .clone()
                    .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                let method_name_str = interner.resolve(func.vole_name).to_string();
                let builtin_mod = self.name_table_mut().builtin_module();
                static_external_methods.insert(
                    method_name_str,
                    ExternalMethodInfo {
                        module_path: self
                            .name_table_mut()
                            .intern_raw(builtin_mod, &[&external.module_path]),
                        native_name: self
                            .name_table_mut()
                            .intern_raw(builtin_mod, &[&native_name_str]),
                    },
                );
            }
        }

        // Register static methods
        for method in &statics_block.methods {
            let method_name_str = interner.resolve(method.name).to_string();
            let builtin_mod = self.name_table_mut().builtin_module();
            let method_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[&method_name_str]);
            let full_method_name_id = self
                .name_table_mut()
                .intern_raw(self.module.current_module, &[name_str, &method_name_str]);

            // Create a fresh type context for each static method
            let mut static_type_ctx = TypeResolutionContext::with_type_params(
                &self.ctx.db,
                interner,
                module_id,
                type_param_scope,
            );

            let params_id: Vec<ArenaTypeId> = method
                .params
                .iter()
                .map(|p| resolve_type_to_id(&p.ty, &mut static_type_ctx))
                .collect();
            let return_type_id = method
                .return_type
                .as_ref()
                .map(|t| resolve_type_to_id(t, &mut static_type_ctx))
                .unwrap_or_else(|| self.type_arena().void());
            let has_default = method.is_default
                || method.body.is_some()
                || default_static_external_methods.contains(&method.name);

            let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                .intern(&mut self.type_arena_mut());

            let external_binding = static_external_methods.get(&method_name_str).copied();
            MethodDefBuilder::new(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature_id,
            )
            .is_static(true)
            .has_default(has_default)
            .external_binding(external_binding)
            .register(&mut self.entity_registry_mut());
        }
    }

    /// Resolve a qualified interface path like `mod.Interface` or `mod.Interface<T>`.
    /// Returns (interface_type_def_id, type_arg_exprs) if successful.
    /// The type_arg_exprs are left unresolved and should be resolved by the caller.
    /// For non-qualified paths, delegates to the standard resolver.
    pub(super) fn resolve_interface_path<'a>(
        &self,
        trait_type: &'a TypeExpr,
        interner: &Interner,
    ) -> Option<(TypeDefId, &'a [TypeExpr])> {
        match &trait_type.kind {
            TypeExprKind::QualifiedPath { segments, args } => {
                // Qualified path: mod.Interface or mod.sub.Interface
                if segments.is_empty() {
                    return None;
                }

                // First segment should be a module variable
                let first_sym = segments[0];
                let module_type_id = self.get_variable_type_id(first_sym)?;

                // Walk through the segments
                let mut current_type_id = module_type_id;
                for (i, &segment_sym) in segments.iter().enumerate().skip(1) {
                    let segment_name = interner.resolve(segment_sym);
                    let arena = self.type_arena();

                    // Must be a module type
                    let module_info = arena.unwrap_module(current_type_id);
                    let Some(module) = module_info else {
                        // Not a module - emit error (will be handled by caller)
                        return None;
                    };

                    // Find the export
                    let name_id = self.module_name_id(module.module_id, segment_name)?;
                    let export_type_id = module.export_type(name_id)?;

                    // Last segment should be an interface
                    if i == segments.len() - 1 {
                        // This should be an interface
                        let type_def_id = arena.type_def_id(export_type_id)?;

                        // Verify it's an interface (resolve through aliases if needed)
                        let kind = self.entity_registry().type_kind(type_def_id);
                        let aliased_type = self.entity_registry().type_aliased(type_def_id);

                        let final_type_def_id = if kind == TypeDefKind::Alias {
                            // For aliases, check the underlying type
                            let Some(aliased_type_id) = aliased_type else {
                                return None; // Alias has no underlying type
                            };
                            let arena = self.type_arena();
                            let Some((underlying_def_id, _)) =
                                arena.unwrap_interface(aliased_type_id)
                            else {
                                return None; // Alias doesn't point to an interface
                            };
                            underlying_def_id
                        } else if kind == TypeDefKind::Interface {
                            type_def_id
                        } else {
                            return None; // Not an interface
                        };

                        // Return type args as references for caller to resolve
                        return Some((final_type_def_id, args.as_slice()));
                    } else {
                        // Not the last segment - must be a module
                        current_type_id = export_type_id;
                    }
                }
                None
            }
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                // Non-qualified: use standard resolver
                let iface_str = interner.resolve(*sym);
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry())?;

                // Verify it's an interface (resolve through aliases if needed)
                let kind = self.entity_registry().type_kind(type_def_id);
                let aliased_type = self.entity_registry().type_aliased(type_def_id);
                let final_type_def_id = if kind == TypeDefKind::Alias {
                    // For aliases, check the underlying type
                    let Some(aliased_type_id) = aliased_type else {
                        return None; // Alias has no underlying type
                    };
                    let arena = self.type_arena();
                    let Some((underlying_def_id, _)) = arena.unwrap_interface(aliased_type_id)
                    else {
                        return None; // Alias doesn't point to an interface
                    };
                    underlying_def_id
                } else if kind == TypeDefKind::Interface {
                    type_def_id
                } else {
                    return None; // Not an interface
                };
                let type_def_id = final_type_def_id;

                // Return type args as references for caller to resolve
                let type_args: &[TypeExpr] = match &trait_type.kind {
                    TypeExprKind::Generic { args, .. } => args.as_slice(),
                    _ => &[],
                };

                Some((type_def_id, type_args))
            }
            _ => None,
        }
    }
}
