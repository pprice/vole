//! Declaration signature collection — class signature collection.

use super::*;

impl Analyzer {
    pub(super) fn collect_class_signature(&mut self, class: &ClassDecl, interner: &Interner) {
        let name_id =
            self.name_table_mut()
                .intern(self.module.current_module, &[class.name], interner);

        // Dispatch to appropriate handler based on whether class is generic
        if class.type_params.is_empty() {
            self.collect_class_signature_non_generic(class, name_id, interner);
        } else {
            self.collect_class_signature_generic(class, name_id, interner);
        }
    }

    /// Collect signature for a non-generic class.
    pub(super) fn collect_class_signature_non_generic(
        &mut self,
        class: &ClassDecl,
        name_id: NameId,
        interner: &Interner,
    ) {
        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("class shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Validate field defaults and collect field info
        let field_has_default = self.validate_field_defaults(&class.fields, interner);
        let (field_names, field_type_ids) = self.collect_field_info(&class.fields, interner, None);

        // Set generic_info (with empty type_params for non-generic classes)
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: vec![],
                field_names: field_names.clone(),
                field_types: field_type_ids.clone(),
                field_has_default,
            },
        );

        // Register fields in EntityRegistry
        self.register_type_fields(
            entity_type_id,
            class.name,
            &class.fields,
            &field_names,
            &field_type_ids,
            interner,
        );

        // Register and validate implements list
        self.validate_and_register_implements(
            entity_type_id,
            &class.implements,
            class.span,
            interner,
        );

        // Build self_type_id for method signatures
        let self_type_id = self
            .type_arena_mut()
            .class(entity_type_id, TypeIdVec::new());
        self.entity_registry_mut()
            .set_base_type_id(entity_type_id, self_type_id);

        // Register all methods
        self.register_class_methods(
            entity_type_id,
            class,
            interner,
            None, // no type param scope
            self_type_id,
        );
    }

    /// Collect signature for a generic class.
    pub(super) fn collect_class_signature_generic(
        &mut self,
        class: &ClassDecl,
        name_id: NameId,
        interner: &Interner,
    ) {
        // Validate field defaults
        let field_has_default = self.validate_field_defaults(&class.fields, interner);

        // Build type params with resolved constraints
        let type_param_scope =
            self.build_type_params_with_constraints(&class.type_params, interner);

        // Collect field info with type params in scope
        let (field_names, field_type_ids) =
            self.collect_field_info(&class.fields, interner, Some(&type_param_scope));

        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("class shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Set type params on the type definition (needed for method substitutions)
        self.register_type_params_on_entity(entity_type_id, &type_param_scope);

        // Set generic info for type inference during struct literal checking
        // Use to_params() since we still need type_param_scope below
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: type_param_scope.to_params(),
                field_names: field_names.clone(),
                field_types: field_type_ids.clone(),
                field_has_default,
            },
        );

        // Register fields with placeholder types
        self.register_type_fields(
            entity_type_id,
            class.name,
            &class.fields,
            &field_names,
            &field_type_ids,
            interner,
        );

        // Register and validate implements list
        self.validate_and_register_implements(
            entity_type_id,
            &class.implements,
            class.span,
            interner,
        );

        // Build self_type_id with type param placeholders
        let type_arg_ids = self.build_type_arg_placeholders(&type_param_scope);
        let self_type_id = self.type_arena_mut().class(entity_type_id, type_arg_ids);
        let base_type_id = self
            .type_arena_mut()
            .class(entity_type_id, TypeIdVec::new());
        self.entity_registry_mut()
            .set_base_type_id(entity_type_id, base_type_id);

        // Register all methods with type params in scope
        self.register_class_methods(
            entity_type_id,
            class,
            interner,
            Some(&type_param_scope),
            self_type_id,
        );
    }

    /// Collect field names and types for a class.
    /// If type_param_scope is provided, resolves types with type params in scope.
    pub(super) fn collect_field_info(
        &mut self,
        fields: &[AstFieldDef],
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) -> (Vec<NameId>, Vec<ArenaTypeId>) {
        let builtin_mod = self.name_table_mut().builtin_module();

        // Convert Symbol field names to NameId
        let field_names: Vec<NameId> = fields
            .iter()
            .map(|f| {
                let name_str = interner.resolve(f.name);
                self.name_table_mut().intern_raw(builtin_mod, &[name_str])
            })
            .collect();

        // Resolve field types (with or without type params)
        let field_type_ids: Vec<ArenaTypeId> = if let Some(scope) = type_param_scope {
            let module_id = self.module.current_module;
            let mut ctx =
                TypeResolutionContext::with_type_params(&self.ctx.db, interner, module_id, scope);
            fields
                .iter()
                .map(|f| resolve_type_to_id(&f.ty, &mut ctx))
                .collect()
        } else {
            fields
                .iter()
                .map(|f| self.resolve_type_id(&f.ty, interner))
                .collect()
        };

        // Check that never is not used in class fields
        for (field, &type_id) in fields.iter().zip(&field_type_ids) {
            self.check_type_annotation_constraints(type_id, &field.ty, field.span);
        }

        (field_names, field_type_ids)
    }

    /// Register fields in the EntityRegistry for a class.
    pub(super) fn register_type_fields(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        fields: &[AstFieldDef],
        field_names: &[NameId],
        field_type_ids: &[ArenaTypeId],
        interner: &Interner,
    ) {
        for (i, field) in fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let full_field_name_id = self.name_table_mut().intern_raw(
                self.module.current_module,
                &[interner.resolve(type_name), field_name_str],
            );
            self.entity_registry_mut().register_field(
                entity_type_id,
                field_names[i],
                full_field_name_id,
                field_type_ids[i],
                i,
            );
        }
    }

    /// Register all methods (instance, static, external) for a class.
    pub(super) fn register_class_methods(
        &mut self,
        entity_type_id: TypeDefId,
        class: &ClassDecl,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        self_type_id: ArenaTypeId,
    ) {
        // Register instance methods
        for method in &class.methods {
            self.register_instance_method(
                entity_type_id,
                class.name,
                method,
                interner,
                type_param_scope,
                Some(self_type_id),
            );
        }

        // Register static methods
        if let Some(ref statics) = class.statics {
            for method in &statics.methods {
                let method_type_params =
                    self.build_method_type_params(method, type_param_scope, interner);
                self.register_static_method_helper(
                    entity_type_id,
                    class.name,
                    method,
                    interner,
                    type_param_scope,
                    method_type_params,
                );
            }
        }

        // Register external methods
        if let Some(ref external) = class.external {
            for func in &external.functions {
                self.register_external_method(
                    entity_type_id,
                    class.name,
                    func,
                    &external.module_path,
                    interner,
                    type_param_scope,
                );
            }
        }
    }
}
