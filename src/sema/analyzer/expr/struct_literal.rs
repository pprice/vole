use super::super::*;
use crate::sema::entity_defs::GenericTypeInfo;

impl Analyzer {
    pub(super) fn check_struct_literal_expr(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // Look up the type (class or record) via Resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(struct_lit.name, &self.entity_registry);

        // Check if this is a generic type (record or class with generic_info)
        if let Some(type_id) = type_id_opt {
            let type_def = self.entity_registry.get_type(type_id);
            if let Some(ref generic_info) = type_def.generic_info {
                let generic_info = generic_info.clone();
                let name_id = type_def.name_id;
                return match type_def.kind {
                    TypeDefKind::Record => {
                        self.check_generic_struct_literal(
                            expr,
                            struct_lit,
                            name_id,
                            &generic_info,
                            interner,
                        )
                    }
                    TypeDefKind::Class => {
                        self.check_generic_class_literal(
                            expr,
                            struct_lit,
                            name_id,
                            &generic_info,
                            interner,
                        )
                    }
                    _ => Ok(Type::Error),
                };
            }
        }

        let (type_name, fields, result_type) = if let Some(type_id) = type_id_opt {
            let type_def = self.entity_registry.get_type(type_id);
            match type_def.kind {
                TypeDefKind::Class => {
                    if let Some(class_type) = self
                        .entity_registry
                        .build_class_type(type_id, &self.name_table)
                    {
                        (
                            interner.resolve(struct_lit.name).to_string(),
                            class_type.fields.clone(),
                            Type::Class(class_type),
                        )
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(struct_lit.name).to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::Error);
                    }
                }
                TypeDefKind::Record => {
                    if let Some(record_type) = self
                        .entity_registry
                        .build_record_type(type_id, &self.name_table)
                    {
                        (
                            interner.resolve(struct_lit.name).to_string(),
                            record_type.fields.clone(),
                            Type::Record(record_type),
                        )
                    } else {
                        self.add_error(
                            SemanticError::UnknownType {
                                name: interner.resolve(struct_lit.name).to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::Error);
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
                    return Ok(Type::Error);
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
            return Ok(Type::Error);
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
        name_id: NameId,
        generic_info: &GenericTypeInfo,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let type_name = interner.resolve(struct_lit.name).to_string();

        // First, type-check all field values to get their actual types
        let mut field_value_types = HashMap::new();
        for field_init in &struct_lit.fields {
            let field_ty = self.check_expr(&field_init.value, interner)?;
            field_value_types.insert(field_init.name, field_ty);
        }

        // Build parallel arrays of expected types (from generic def) and actual types (from values)
        // for type parameter inference
        let mut expected_types = Vec::new();
        let mut actual_types = Vec::new();

        for (i, field_name) in generic_info.field_names.iter().enumerate() {
            if let Some(actual_ty) = field_value_types.get(field_name) {
                expected_types.push(generic_info.field_types[i].clone());
                actual_types.push(actual_ty.clone());
            }
        }

        // Infer type parameters from field values
        let inferred =
            self.infer_type_params(&generic_info.type_params, &expected_types, &actual_types);

        // Check type parameter constraints
        self.check_type_param_constraints(&generic_info.type_params, &inferred, expr.span, interner);

        // Substitute inferred types into field types to get concrete field types
        let concrete_field_types: Vec<Type> = generic_info
            .field_types
            .iter()
            .map(|t| substitute_type(t, &inferred))
            .collect();

        // Check that all required fields are present
        let provided_fields: HashSet<Symbol> = struct_lit.fields.iter().map(|f| f.name).collect();

        for field_name in &generic_info.field_names {
            if !provided_fields.contains(field_name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: interner.resolve(*field_name).to_string(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field against the concrete (substituted) type
        for field_init in &struct_lit.fields {
            // Find the field index - compare Symbols directly since field_names is Vec<Symbol>
            if let Some(idx) = generic_info
                .field_names
                .iter()
                .position(|n| *n == field_init.name)
            {
                let actual_ty = field_value_types.get(&field_init.name).unwrap();
                let expected_ty = &concrete_field_types[idx];

                if !self.types_compatible(actual_ty, expected_ty, interner) {
                    let expected = self.type_display(expected_ty);
                    let found = self.type_display(actual_ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found,
                            span: field_init.value.span.into(),
                        },
                        field_init.value.span,
                    );
                }
            } else {
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name.clone(),
                        field: interner.resolve(field_init.name).to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
            }
        }

        // Build the concrete record type with substituted field types
        let concrete_fields: Vec<StructField> = generic_info
            .field_names
            .iter()
            .enumerate()
            .map(|(i, name)| StructField {
                name: interner.resolve(*name).to_string(),
                ty: concrete_field_types[i].clone(),
                slot: i,
            })
            .collect();

        // Build type_args from inferred types in order of type params
        let type_args: Vec<Type> = generic_info
            .type_params
            .iter()
            .filter_map(|tp| inferred.get(&tp.name_id).cloned())
            .collect();

        let concrete_record = RecordType {
            name_id,
            fields: concrete_fields,
            type_args,
        };
        Ok(Type::Record(concrete_record))
    }

    /// Check a struct literal for a generic class, inferring type parameters from field values
    fn check_generic_class_literal(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        name_id: NameId,
        generic_info: &GenericTypeInfo,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let type_name = interner.resolve(struct_lit.name).to_string();

        // First, type-check all field values to get their actual types
        let mut field_value_types = HashMap::new();
        for field_init in &struct_lit.fields {
            let field_ty = self.check_expr(&field_init.value, interner)?;
            field_value_types.insert(field_init.name, field_ty);
        }

        // Build parallel arrays of expected types (from generic def) and actual types (from values)
        // for type parameter inference
        let mut expected_types = Vec::new();
        let mut actual_types = Vec::new();

        for (i, field_name) in generic_info.field_names.iter().enumerate() {
            if let Some(actual_ty) = field_value_types.get(field_name) {
                expected_types.push(generic_info.field_types[i].clone());
                actual_types.push(actual_ty.clone());
            }
        }

        // Infer type parameters from field values
        let inferred =
            self.infer_type_params(&generic_info.type_params, &expected_types, &actual_types);

        // Check type parameter constraints
        self.check_type_param_constraints(&generic_info.type_params, &inferred, expr.span, interner);

        // Substitute inferred types into field types to get concrete field types
        let concrete_field_types: Vec<Type> = generic_info
            .field_types
            .iter()
            .map(|t| substitute_type(t, &inferred))
            .collect();

        // Check that all required fields are present
        let provided_fields: HashSet<Symbol> = struct_lit.fields.iter().map(|f| f.name).collect();

        for field_name in &generic_info.field_names {
            if !provided_fields.contains(field_name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: interner.resolve(*field_name).to_string(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field against the concrete (substituted) type
        for field_init in &struct_lit.fields {
            // Find the field index - compare Symbols directly since field_names is Vec<Symbol>
            if let Some(idx) = generic_info
                .field_names
                .iter()
                .position(|n| *n == field_init.name)
            {
                let actual_ty = field_value_types.get(&field_init.name).unwrap();
                let expected_ty = &concrete_field_types[idx];

                if !self.types_compatible(actual_ty, expected_ty, interner) {
                    let expected = self.type_display(expected_ty);
                    let found = self.type_display(actual_ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found,
                            span: field_init.value.span.into(),
                        },
                        field_init.value.span,
                    );
                }
            } else {
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name.clone(),
                        field: interner.resolve(field_init.name).to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
            }
        }

        // Build the concrete class type with substituted field types
        let concrete_fields: Vec<StructField> = generic_info
            .field_names
            .iter()
            .enumerate()
            .map(|(i, name)| StructField {
                name: interner.resolve(*name).to_string(),
                ty: concrete_field_types[i].clone(),
                slot: i,
            })
            .collect();

        let concrete_class = ClassType {
            name_id,
            fields: concrete_fields,
        };
        Ok(Type::Class(concrete_class))
    }
}
