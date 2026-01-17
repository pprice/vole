use super::super::*;
use crate::sema::entity_defs::GenericTypeInfo;
use crate::sema::type_arena::TypeIdVec;
use crate::sema::types::{LegacyType, NominalType};

impl Analyzer {
    pub(super) fn check_struct_literal_expr(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        interner: &Interner,
    ) -> Result<LegacyType, Vec<TypeError>> {
        // Look up the type (class or record) via Resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(struct_lit.name, &self.entity_registry);

        // Check if this is a generic type (record or class with type parameters)
        // Non-generic types have generic_info for field storage but empty type_params
        if let Some(type_id) = type_id_opt {
            let type_def = self.entity_registry.get_type(type_id);
            if let Some(ref generic_info) = type_def.generic_info {
                // Only use generic literal checking if there are actual type parameters to infer
                if !generic_info.type_params.is_empty() {
                    let generic_info = generic_info.clone();
                    return match type_def.kind {
                        TypeDefKind::Record => self.check_generic_struct_literal(
                            expr,
                            struct_lit,
                            type_id,
                            &generic_info,
                            interner,
                        ),
                        TypeDefKind::Class => self.check_generic_class_literal(
                            expr,
                            struct_lit,
                            type_id,
                            &generic_info,
                            interner,
                        ),
                        _ => Ok(self.ty_invalid()),
                    };
                }
            }
        }

        // Helper to get fields from TypeDef
        // Borrows arena to convert TypeIds to LegacyTypes
        let arena = &self.type_arena;
        let get_fields_from_typedef = |type_def: &crate::sema::entity_defs::TypeDef,
                                       name_table: &NameTable|
         -> Vec<StructField> {
            type_def
                .generic_info
                .as_ref()
                .map(|gi| {
                    gi.field_names
                        .iter()
                        .zip(gi.field_types.iter())
                        .enumerate()
                        .filter_map(|(i, (name_id, &ty_id))| {
                            // Convert TypeId to LegacyType
                            let ty = arena.borrow().to_type(ty_id);
                            Some(StructField {
                                name: name_table.last_segment_str(*name_id)?,
                                ty,
                                slot: i,
                            })
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        let (type_name, fields, result_type) = if let Some(type_id) = type_id_opt {
            let type_def = self.entity_registry.get_type(type_id);
            match type_def.kind {
                TypeDefKind::Class => {
                    if let Some(class_type) = self.entity_registry.build_class_type(type_id) {
                        let fields = get_fields_from_typedef(type_def, &self.name_table);
                        (
                            interner.resolve(struct_lit.name).to_string(),
                            fields,
                            LegacyType::Nominal(NominalType::Class(class_type)),
                        )
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(struct_lit.name).to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(self.ty_invalid());
                    }
                }
                TypeDefKind::Record => {
                    if let Some(record_type) = self.entity_registry.build_record_type(type_id) {
                        let fields = get_fields_from_typedef(type_def, &self.name_table);
                        (
                            interner.resolve(struct_lit.name).to_string(),
                            fields,
                            LegacyType::Nominal(NominalType::Record(record_type)),
                        )
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(struct_lit.name).to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(self.ty_invalid());
                    }
                }
                _ => {
                    self.add_error(
                        SemanticError::UnknownType {
                            name: interner.resolve(struct_lit.name).to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(self.ty_invalid());
                }
            }
        } else {
            self.add_error(
                SemanticError::UnknownType {
                    name: interner.resolve(struct_lit.name).to_string(),
                    span: expr.span.into(),
                },
                expr.span,
            );
            return Ok(self.ty_invalid());
        };

        // Check that all required fields are present
        let provided_fields: HashSet<String> = struct_lit
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();

        for field in &fields {
            if !provided_fields.contains(&field.name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: field.name.clone(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field
        for field_init in &struct_lit.fields {
            let field_init_name = interner.resolve(field_init.name);
            if let Some(expected_field) = fields.iter().find(|f| f.name == field_init_name) {
                // check_expr_expecting will report errors if types don't match
                self.check_expr_expecting(&field_init.value, Some(&expected_field.ty), interner)?;
            } else {
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name.clone(),
                        field: interner.resolve(field_init.name).to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
                // Still check the value for more errors
                self.check_expr(&field_init.value, interner)?;
            }
        }

        // Return the appropriate type
        Ok(result_type)
    }

    /// Check a struct literal for a generic record, inferring type parameters from field values
    fn check_generic_struct_literal(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        type_def_id: TypeDefId,
        generic_info: &GenericTypeInfo,
        interner: &Interner,
    ) -> Result<LegacyType, Vec<TypeError>> {
        let type_name = interner.resolve(struct_lit.name).to_string();

        // First, type-check all field values to get their actual types
        // Use string keys since Symbols may be from different interners
        let mut field_value_types: HashMap<String, LegacyType> = HashMap::new();
        for field_init in &struct_lit.fields {
            let field_ty_id = self.check_expr(&field_init.value, interner)?;
            let field_ty = self.id_to_type(field_ty_id);
            field_value_types.insert(interner.resolve(field_init.name).to_string(), field_ty);
        }

        // Build parallel arrays of expected types (from generic def) and actual types (from values)
        // for type parameter inference
        let mut expected_types = Vec::new();
        let mut actual_types = Vec::new();

        // Convert field types from TypeId to LegacyType
        let field_types: Vec<LegacyType> = generic_info
            .field_types
            .iter()
            .map(|&t| self.type_arena.borrow().to_type(t))
            .collect();

        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            if let Some(field_name_str) = self.name_table.last_segment_str(*field_name_id)
                && let Some(actual_ty) = field_value_types.get(&field_name_str)
            {
                expected_types.push(field_types[i].clone());
                actual_types.push(actual_ty.clone());
            }
        }

        // Infer type parameters from field values
        let inferred =
            self.infer_type_params(&generic_info.type_params, &expected_types, &actual_types);

        // Check type parameter constraints
        self.check_type_param_constraints(
            &generic_info.type_params,
            &inferred,
            expr.span,
            interner,
        );

        // Substitute inferred types into field types to get concrete field types via arena
        let concrete_field_types: Vec<LegacyType> = {
            let mut arena = self.type_arena.borrow_mut();
            let subs_id: hashbrown::HashMap<_, _> = inferred
                .iter()
                .map(|(&k, v)| (k, arena.from_type(v)))
                .collect();
            let substituted_ids: Vec<_> = generic_info
                .field_types
                .iter()
                .map(|&t| arena.substitute(t, &subs_id))
                .collect();
            substituted_ids.iter().map(|&t| arena.to_type(t)).collect()
        };

        // Check that all required fields are present - compare by string value
        let provided_fields: HashSet<String> = struct_lit
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();

        for field_name_id in &generic_info.field_names {
            let field_name_str = self
                .name_table
                .last_segment_str(*field_name_id)
                .unwrap_or_default();
            if !provided_fields.contains(&field_name_str) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: field_name_str,
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field against the concrete (substituted) type
        for field_init in &struct_lit.fields {
            let field_init_name_str = interner.resolve(field_init.name);
            // Find the field index - compare by string value since Symbols may differ
            if let Some(idx) = generic_info.field_names.iter().position(|name_id| {
                self.name_table.last_segment_str(*name_id).as_deref() == Some(field_init_name_str)
            }) {
                let actual_ty = field_value_types
                    .get(field_init_name_str)
                    .expect("field was validated in type check phase");
                let expected_ty = &concrete_field_types[idx];

                // Convert to TypeId for compatibility check (Phase 2 migration)
                let actual_ty_id = self.type_to_id(actual_ty);
                let expected_ty_id = self.type_to_id(expected_ty);
                if !self.types_compatible_id(actual_ty_id, expected_ty_id, interner) {
                    self.add_type_mismatch_id(expected_ty_id, actual_ty_id, field_init.value.span);
                }
            } else {
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name.clone(),
                        field: field_init_name_str.to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
            }
        }

        // Build type_args from inferred types in order of type params
        let type_args: Vec<LegacyType> = generic_info
            .type_params
            .iter()
            .filter_map(|tp| inferred.get(&tp.name_id).cloned())
            .collect();

        let concrete_record = RecordType {
            type_def_id,
            type_args: type_args.into(),
            type_args_id: TypeIdVec::new(),
        };
        Ok(LegacyType::Nominal(NominalType::Record(concrete_record)))
    }

    /// Check a struct literal for a generic class, inferring type parameters from field values
    fn check_generic_class_literal(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        type_def_id: TypeDefId,
        generic_info: &GenericTypeInfo,
        interner: &Interner,
    ) -> Result<LegacyType, Vec<TypeError>> {
        let type_name = interner.resolve(struct_lit.name).to_string();

        // First, type-check all field values to get their actual types
        // Use string keys since Symbols may be from different interners
        let mut field_value_types: HashMap<String, LegacyType> = HashMap::new();
        for field_init in &struct_lit.fields {
            let field_ty_id = self.check_expr(&field_init.value, interner)?;
            let field_ty = self.id_to_type(field_ty_id);
            field_value_types.insert(interner.resolve(field_init.name).to_string(), field_ty);
        }

        // Build parallel arrays of expected types (from generic def) and actual types (from values)
        // for type parameter inference
        let mut expected_types = Vec::new();
        let mut actual_types = Vec::new();

        // Convert field types from TypeId to LegacyType
        let field_types: Vec<LegacyType> = generic_info
            .field_types
            .iter()
            .map(|&t| self.type_arena.borrow().to_type(t))
            .collect();

        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            if let Some(field_name_str) = self.name_table.last_segment_str(*field_name_id)
                && let Some(actual_ty) = field_value_types.get(&field_name_str)
            {
                expected_types.push(field_types[i].clone());
                actual_types.push(actual_ty.clone());
            }
        }

        // Infer type parameters from field values
        let inferred =
            self.infer_type_params(&generic_info.type_params, &expected_types, &actual_types);

        // Check type parameter constraints
        self.check_type_param_constraints(
            &generic_info.type_params,
            &inferred,
            expr.span,
            interner,
        );

        // Substitute inferred types into field types to get concrete field types via arena
        let concrete_field_types: Vec<LegacyType> = {
            let mut arena = self.type_arena.borrow_mut();
            let subs_id: hashbrown::HashMap<_, _> = inferred
                .iter()
                .map(|(&k, v)| (k, arena.from_type(v)))
                .collect();
            let substituted_ids: Vec<_> = generic_info
                .field_types
                .iter()
                .map(|&t| arena.substitute(t, &subs_id))
                .collect();
            substituted_ids.iter().map(|&t| arena.to_type(t)).collect()
        };

        // Check that all required fields are present - compare by string value
        let provided_fields: HashSet<String> = struct_lit
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();

        for field_name_id in &generic_info.field_names {
            let field_name_str = self
                .name_table
                .last_segment_str(*field_name_id)
                .unwrap_or_default();
            if !provided_fields.contains(&field_name_str) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: field_name_str,
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field against the concrete (substituted) type
        for field_init in &struct_lit.fields {
            let field_init_name_str = interner.resolve(field_init.name);
            // Find the field index - compare by string value since Symbols may differ
            if let Some(idx) = generic_info.field_names.iter().position(|name_id| {
                self.name_table.last_segment_str(*name_id).as_deref() == Some(field_init_name_str)
            }) {
                let actual_ty = field_value_types
                    .get(field_init_name_str)
                    .expect("field was validated in type check phase");
                let expected_ty = &concrete_field_types[idx];

                // Convert to TypeId for compatibility check (Phase 2 migration)
                let actual_ty_id = self.type_to_id(actual_ty);
                let expected_ty_id = self.type_to_id(expected_ty);
                if !self.types_compatible_id(actual_ty_id, expected_ty_id, interner) {
                    self.add_type_mismatch_id(expected_ty_id, actual_ty_id, field_init.value.span);
                }
            } else {
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name.clone(),
                        field: field_init_name_str.to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
            }
        }

        // Convert inferred substitutions to ordered type_args based on type param order
        // When inference fails, fall back to type params from current scope (for same-type struct literals in methods)
        let type_args: Vec<LegacyType> = generic_info
            .type_params
            .iter()
            .map(|param| {
                // First try inferred type
                if let Some(ty) = inferred.get(&param.name_id) {
                    return ty.clone();
                }
                // Fall back to current type param scope - this handles cases like
                // GenericContainer { _ptr: ... } inside GenericContainer<K,V>.new()
                if let Some(scope) = self.type_param_stack.current() {
                    // Look up by matching the type param name in the current scope
                    let param_name = self.name_table.last_segment_str(param.name_id);
                    if let Some(param_name) = param_name {
                        for scope_param in scope.params() {
                            let scope_param_name =
                                self.name_table.last_segment_str(scope_param.name_id);
                            if scope_param_name.as_deref() == Some(&param_name) {
                                return LegacyType::TypeParam(scope_param.name_id);
                            }
                        }
                    }
                }
                LegacyType::unknown()
            })
            .collect();

        let concrete_class = ClassType {
            type_def_id,
            type_args: type_args.into(),
            type_args_id: TypeIdVec::new(),
        };
        Ok(LegacyType::Nominal(NominalType::Class(concrete_class)))
    }
}
