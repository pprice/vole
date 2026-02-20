//! Declaration signature collection — external block registration.

use super::*;

impl Analyzer {
    /// Register external block functions as top-level functions
    /// This is called for standalone external blocks (not inside implement blocks)
    pub(super) fn collect_external_block(
        &mut self,
        ext_block: &ExternalBlock,
        interner: &Interner,
    ) {
        let builtin_mod = self.name_table_mut().builtin_module();

        for func in &ext_block.functions {
            // For generic external functions in prelude, use builtin_mod so they're globally accessible
            // (can be called from any module without import). For non-prelude modules, use the
            // current module so explicit import is required.
            let name_module = if !func.type_params.is_empty() && self.module.loading_prelude {
                builtin_mod
            } else {
                self.module.current_module
            };
            let name_id = self
                .name_table_mut()
                .intern(name_module, &[func.vole_name], interner);

            // Validate parameter default ordering and count required params
            let required_params = self.validate_param_defaults(&func.params, interner);

            // Clone the default expressions for storage
            let param_defaults: Vec<Option<Box<Expr>>> = func
                .params
                .iter()
                .map(|p| p.default_value.clone())
                .collect();

            // Collect parameter names for named argument resolution
            let param_names: Vec<String> = func
                .params
                .iter()
                .map(|p| interner.resolve(p.name).to_string())
                .collect();

            // For generic external functions, set up type param scope and register with GenericFuncInfo
            if !func.type_params.is_empty() {
                let reg_data = FuncRegistrationData {
                    name_id,
                    required_params,
                    param_defaults,
                    param_names,
                };
                self.collect_generic_external_func(
                    func,
                    &ext_block.module_path,
                    builtin_mod,
                    reg_data,
                    interner,
                );
            } else {
                // Non-generic external function
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

                let func_type = FunctionType::from_ids(&params_id, return_type_id, false);

                // Type-check parameter default expressions so their types are recorded for codegen
                if let Err(errs) =
                    self.check_param_defaults(&func.params, &func_type.params_id, interner)
                {
                    self.diagnostics.errors.extend(errs);
                }

                // Register the function with its Vole name (Symbol)
                self.symbols
                    .functions
                    .insert(func.vole_name, func_type.clone());

                // Also register by string name for cross-interner lookups (prelude functions)
                let name_str = interner.resolve(func.vole_name).to_string();
                self.symbols
                    .functions_by_name
                    .insert(name_str.clone(), func_type.clone());

                // Register in EntityRegistry with default expressions
                self.entity_registry_mut().register_function_full(
                    name_id,
                    name_id,
                    self.module.current_module,
                    func_type,
                    required_params,
                    param_defaults,
                    param_names,
                    true, // is_external
                );

                // Store the external info (module path and native name) for codegen
                let native_name_str = func.native_name.clone().unwrap_or_else(|| name_str.clone());
                // Extract name IDs before calling implement_registry_mut to avoid overlapping borrows
                let (module_path, native_name) = {
                    let mut name_table = self.name_table_mut();
                    (
                        name_table.intern_raw(builtin_mod, &[&ext_block.module_path]),
                        name_table.intern_raw(builtin_mod, &[&native_name_str]),
                    )
                };
                self.implement_registry_mut().register_external_func(
                    name_str,
                    ExternalMethodInfo {
                        module_path,
                        native_name,
                    },
                );
            }
        }
    }

    /// Register a generic external function from an external block.
    /// Handles type param resolution, constraint checking, EntityRegistry registration,
    /// and external info storage for codegen.
    fn collect_generic_external_func(
        &mut self,
        func: &ExternalFunc,
        module_path: &str,
        builtin_mod: ModuleId,
        reg_data: FuncRegistrationData,
        interner: &Interner,
    ) {
        // Build type params with resolved constraints
        let type_param_scope = self.build_type_params_with_constraints(&func.type_params, interner);

        // Resolve with type params in scope
        let module_id = self.module.current_module;
        let mut ctx = TypeResolutionContext::with_type_params(
            &self.ctx.db,
            interner,
            module_id,
            &type_param_scope,
        );
        // Resolve directly to TypeId
        let param_type_ids: Vec<ArenaTypeId> = func
            .params
            .iter()
            .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
            .collect();
        let return_type_id = func
            .return_type
            .as_ref()
            .map(|t| resolve_type_to_id(t, &mut ctx))
            .unwrap_or_else(|| self.type_arena().void());

        // Create signature from TypeIds
        let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);

        // Type-check parameter default expressions so their types are recorded for codegen
        if let Err(errs) = self.check_param_defaults(&func.params, &signature.params_id, interner) {
            self.diagnostics.errors.extend(errs);
        }

        // Register in EntityRegistry with default expressions (like regular generic functions)
        let func_id = self.entity_registry_mut().register_function_full(
            reg_data.name_id,
            reg_data.name_id,
            self.module.current_module,
            signature.clone(),
            reg_data.required_params,
            reg_data.param_defaults,
            reg_data.param_names,
            true, // is_external
        );
        // Extract type params from scope (consumes scope, avoids clone)
        let type_params = type_param_scope.into_params();
        self.entity_registry_mut().set_function_generic_info(
            func_id,
            GenericFuncInfo {
                type_params,
                param_types: param_type_ids,
                return_type: return_type_id,
            },
        );

        // NOTE: Don't register in self.symbols.functions for generic externals!
        // The call handler checks self.symbols.functions first without doing type inference.
        // Generic functions must go through EntityRegistry's generic_info path.

        // Store external info for codegen
        let name_str = interner.resolve(func.vole_name).to_string();

        // If the function has type_mappings, register as GenericExternalInfo
        if let Some(ref mappings) = func.type_mappings {
            let module_path_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[module_path]);

            // Resolve each type mapping to TypeId
            let type_mappings = self.resolve_type_mappings(mappings, interner);

            self.implement_registry_mut().register_generic_external(
                name_str,
                GenericExternalInfo {
                    module_path: module_path_id,
                    type_mappings,
                },
            );
        } else {
            // No type mappings, use the native_name as before
            let native_name_str = func.native_name.clone().unwrap_or_else(|| name_str.clone());
            // Extract name IDs before calling implement_registry_mut to avoid overlapping borrows
            let (module_path_id, native_name) = {
                let mut name_table = self.name_table_mut();
                (
                    name_table.intern_raw(builtin_mod, &[module_path]),
                    name_table.intern_raw(builtin_mod, &[&native_name_str]),
                )
            };
            self.implement_registry_mut().register_external_func(
                name_str,
                ExternalMethodInfo {
                    module_path: module_path_id,
                    native_name,
                },
            );
        }
    }

    /// Resolve type mappings from a where block to TypeMappingEntry list.
    /// Each TypeMapping (AST) is converted to TypeMappingEntry (resolved TypeId + key).
    pub(super) fn resolve_type_mappings(
        &mut self,
        mappings: &[TypeMapping],
        interner: &Interner,
    ) -> Vec<TypeMappingEntry> {
        let mut resolved = Vec::with_capacity(mappings.len());
        let mut seen_exact: FxHashMap<ArenaTypeId, Span> = FxHashMap::default();
        let mut default_span: Option<Span> = None;

        for mapping in mappings {
            match &mapping.arm {
                TypeMappingArm::Exact(type_expr) => {
                    let type_id = self.resolve_type_id(type_expr, interner);
                    if let Some(first_span) = seen_exact.insert(type_id, mapping.span) {
                        let ty_display = self.type_arena().display_basic(type_id);
                        self.add_error(
                            SemanticError::DuplicateGenericExternalTypeMapping {
                                ty: ty_display,
                                span: mapping.span.into(),
                                first: first_span.into(),
                            },
                            mapping.span,
                        );
                        continue;
                    }

                    resolved.push(TypeMappingEntry {
                        kind: crate::implement_registry::TypeMappingKind::Exact(type_id),
                        intrinsic_key: mapping.intrinsic_key.clone(),
                    });
                }
                TypeMappingArm::Default => {
                    if let Some(first_span) = default_span {
                        self.add_error(
                            SemanticError::DuplicateGenericExternalDefaultMapping {
                                span: mapping.span.into(),
                                first: first_span.into(),
                            },
                            mapping.span,
                        );
                        continue;
                    }
                    default_span = Some(mapping.span);
                    resolved.push(TypeMappingEntry {
                        kind: crate::implement_registry::TypeMappingKind::Default,
                        intrinsic_key: mapping.intrinsic_key.clone(),
                    });
                }
            }
        }

        resolved
    }
}
