//! Declaration signature collection — struct and sentinel signature collection.

use super::*;

impl Analyzer {
    pub(super) fn collect_struct_signature(
        &mut self,
        struct_decl: &StructDecl,
        interner: &Interner,
    ) {
        let name_id =
            self.name_table_mut()
                .intern(self.current_module, &[struct_decl.name], interner);

        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("struct shell registered in register_all_type_shells");

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
        let field_has_default = self.validate_field_defaults(&struct_decl.fields, interner);
        let (field_names, field_type_ids) =
            self.collect_field_info(&struct_decl.fields, interner, None);

        // Set generic_info (with empty type_params for non-generic structs)
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
            struct_decl.name,
            &struct_decl.fields,
            &field_names,
            &field_type_ids,
            interner,
        );

        // Register the struct's base TypeId
        let self_type_id = self
            .type_arena_mut()
            .struct_type(entity_type_id, TypeIdVec::new());
        self.entity_registry_mut()
            .set_base_type_id(entity_type_id, self_type_id);

        // Register instance methods
        for method in &struct_decl.methods {
            self.register_instance_method(
                entity_type_id,
                struct_decl.name,
                method,
                interner,
                None, // no type_param_scope for non-generic structs
                Some(self_type_id),
            );
        }

        // Register static methods
        if let Some(ref statics) = struct_decl.statics {
            for method in &statics.methods {
                let method_type_params = self.build_method_type_params(method, None, interner);
                self.register_static_method_helper(
                    entity_type_id,
                    struct_decl.name,
                    method,
                    interner,
                    None, // no type_param_scope for non-generic structs
                    method_type_params,
                );
            }
        }
    }

    /// Collect the signature for a sentinel declaration (zero-field struct).
    pub(super) fn collect_sentinel_signature(
        &mut self,
        sentinel_decl: &SentinelDecl,
        interner: &Interner,
    ) {
        let name_id =
            self.name_table_mut()
                .intern(self.current_module, &[sentinel_decl.name], interner);

        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("sentinel shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Set generic_info with empty everything (zero-field struct)
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: vec![],
                field_names: vec![],
                field_types: vec![],
                field_has_default: vec![],
            },
        );

        // Check if this is a well-known sentinel (Done or nil) that has a reserved TypeId.
        // If so, rebind the reserved slot to point to the sentinel's struct type instead
        // of creating a new TypeId. This ensures TypeId::DONE and TypeId::NIL remain the
        // canonical identifiers for these types.
        let sentinel_name = interner.resolve(sentinel_decl.name);
        let well_known_type_id = match sentinel_name {
            "Done" => Some(ArenaTypeId::DONE),
            "nil" => Some(ArenaTypeId::NIL),
            _ => None,
        };

        if let Some(reserved_id) = well_known_type_id {
            use crate::type_arena::SemaType;
            // Rebind the reserved TypeId slot to point to the sentinel's struct type
            self.type_arena_mut().rebind(
                reserved_id,
                SemaType::Struct {
                    type_def_id: entity_type_id,
                    type_args: TypeIdVec::new(),
                },
            );
            self.type_arena_mut().mark_sentinel(reserved_id);
            self.entity_registry_mut()
                .set_base_type_id(entity_type_id, reserved_id);
        } else {
            // Non-well-known sentinel: create a new TypeId as usual
            let self_type_id = self
                .type_arena_mut()
                .struct_type(entity_type_id, TypeIdVec::new());
            self.type_arena_mut().mark_sentinel(self_type_id);
            self.entity_registry_mut()
                .set_base_type_id(entity_type_id, self_type_id);
        }
    }

    /// Validate and register interface implementations for a type.
    /// Reports errors for unknown interfaces.
    pub(super) fn validate_and_register_implements(
        &mut self,
        entity_type_id: TypeDefId,
        implements: &[TypeExpr],
        span: Span,
        interner: &Interner,
    ) {
        for iface_type in implements {
            let Some(iface_sym) = interface_base_name(iface_type) else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(iface_type, interner),
                        span: span.into(),
                    },
                    span,
                );
                continue;
            };

            let iface_str = interner.resolve(iface_sym);
            let Some(interface_type_id) = self
                .resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry())
            else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(iface_type, interner),
                        span: span.into(),
                    },
                    span,
                );
                continue;
            };

            // Extract and resolve type arguments directly to TypeId
            let type_arg_ids: Vec<ArenaTypeId> = match &iface_type.kind {
                TypeExprKind::Generic { args, .. } => args
                    .iter()
                    .map(|arg| self.resolve_type_id(arg, interner))
                    .collect(),
                _ => Vec::new(),
            };

            // Validate that type args match interface's type params
            let expected_count = self.entity_registry().type_params(interface_type_id).len();
            let found_count = type_arg_ids.len();
            if expected_count != found_count {
                self.add_error(
                    SemanticError::WrongTypeArgCount {
                        expected: expected_count,
                        found: found_count,
                        span: span.into(),
                    },
                    span,
                );
                continue;
            }
            // Check for duplicate implementation (e.g., `class Foo: IFace, IFace`)
            // find_existing_implementation returns Some(_) if this interface is already registered
            if self
                .entity_registry()
                .find_existing_implementation(entity_type_id, interface_type_id)
                .is_some()
            {
                let interface_name = self
                    .name_table()
                    .last_segment_str(self.entity_registry().get_type(interface_type_id).name_id)
                    .unwrap_or_else(|| "?".to_string());
                let target_name = self
                    .name_table()
                    .last_segment_str(self.entity_registry().get_type(entity_type_id).name_id)
                    .unwrap_or_else(|| "?".to_string());
                self.add_error(
                    SemanticError::DuplicateImplementation {
                        interface: interface_name,
                        target: target_name,
                        span: span.into(),
                        first_impl: span.into(), // Same span since both are in the class declaration
                    },
                    span,
                );
                continue;
            }
            // Note: We don't set a span here because class declarations that declare
            // `: Interface` are complementary to `implement Interface for Class` blocks.
            // Duplicate detection is only for multiple implement blocks.
            self.entity_registry_mut().add_implementation(
                entity_type_id,
                interface_type_id,
                type_arg_ids.clone(),
                None, // No span - class declaration, not implement block
            );

            // Register interface default methods on the implementing type
            // so that find_method_on_type works for inherited default methods.
            {
                let mut entities = self.entity_registry_mut();
                let mut names = self.name_table_mut();
                entities.register_interface_default_methods_on_implementing_type(
                    entity_type_id,
                    interface_type_id,
                    &mut names,
                );
            }

            // Pre-compute substituted method signatures for codegen's lookup_substitute
            self.precompute_interface_method_substitutions(interface_type_id, &type_arg_ids);
        }
    }
}
