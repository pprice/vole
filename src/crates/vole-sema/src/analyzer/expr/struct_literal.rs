use super::super::*;
use crate::entity_defs::GenericTypeInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use crate::type_arena::TypeIdVec;
use crate::types::StructFieldId;
use rustc_hash::FxHashMap;
use vole_frontend::ast::ExprKind;

impl Analyzer {
    /// Check if a shorthand field value refers to an undefined variable.
    /// If so, emit a specialized error and return true.
    /// This provides better error messages for shorthand syntax like `Point { x }`.
    fn check_shorthand_undefined(
        &mut self,
        field_init: &StructFieldInit,
        interner: &Interner,
    ) -> bool {
        // Only check shorthand fields
        if !field_init.shorthand {
            return false;
        }

        // Shorthand fields have an identifier value that matches the field name
        if let ExprKind::Identifier(sym) = &field_init.value.kind {
            // Check if the variable is defined
            let has_variable = self.get_variable_type_id(*sym).is_some();
            let has_function = self.get_function_type(*sym, interner).is_some();

            if !has_variable && !has_function {
                let name = interner.resolve(*sym).to_string();
                self.add_error(
                    SemanticError::UndefinedShorthandVariable {
                        name,
                        span: field_init.value.span.into(),
                    },
                    field_init.value.span,
                );
                return true;
            }
        }
        false
    }

    pub(super) fn check_struct_literal_expr(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Look up the type (class or record) via Resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(struct_lit.name, &self.entity_registry());

        // Check if this is a generic type (record or class with type parameters)
        // Non-generic types have generic_info for field storage but empty type_params
        if let Some(type_id) = type_id_opt {
            let (kind, generic_info_opt) = {
                let registry = self.entity_registry();
                let type_def = registry.get_type(type_id);
                (type_def.kind, type_def.generic_info.clone())
            };
            if let Some(ref generic_info) = generic_info_opt {
                // Only use generic literal checking if there are actual type parameters to infer
                if !generic_info.type_params.is_empty() {
                    let generic_info = generic_info.clone();
                    return match kind {
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
                        _ => Ok(self.ty_invalid_id()),
                    };
                }
            }
        }

        let get_fields_from_generic_info = |gi: &GenericTypeInfo| -> Vec<StructFieldId> {
            gi.field_names
                .iter()
                .zip(gi.field_types.iter())
                .enumerate()
                .map(|(i, (&name_id, &ty))| StructFieldId {
                    name_id,
                    ty,
                    slot: i,
                })
                .collect()
        };

        let (type_name, fields, field_has_default, result_type_id) =
            if let Some(type_id) = type_id_opt {
                // Extract type info before doing mutable operations
                let (kind, generic_info, is_class_valid, is_record_valid) = {
                    let registry = self.entity_registry();
                    let type_def = registry.get_type(type_id);
                    (
                        type_def.kind,
                        type_def.generic_info.clone(),
                        registry.build_class_type(type_id).is_some(),
                        registry.build_record_type(type_id).is_some(),
                    )
                };
                let fields = generic_info
                    .as_ref()
                    .map(get_fields_from_generic_info)
                    .unwrap_or_default();
                let field_defaults = generic_info
                    .as_ref()
                    .map(|gi| gi.field_has_default.clone())
                    .unwrap_or_default();
                match kind {
                    TypeDefKind::Class => {
                        if is_class_valid {
                            let result_id = self.type_arena_mut().class(type_id, vec![]);
                            (
                                interner.resolve(struct_lit.name).to_string(),
                                fields,
                                field_defaults,
                                result_id,
                            )
                        } else {
                            self.add_error(
                                SemanticError::UnknownType {
                                    name: interner.resolve(struct_lit.name).to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            return Ok(self.ty_invalid_id());
                        }
                    }
                    TypeDefKind::Record => {
                        if is_record_valid {
                            let result_id = self.type_arena_mut().record(type_id, vec![]);
                            (
                                interner.resolve(struct_lit.name).to_string(),
                                fields,
                                field_defaults,
                                result_id,
                            )
                        } else {
                            self.add_error(
                                SemanticError::UnknownType {
                                    name: interner.resolve(struct_lit.name).to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            return Ok(self.ty_invalid_id());
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
                        return Ok(self.ty_invalid_id());
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
                return Ok(self.ty_invalid_id());
            };

        // Check that all required fields are present (fields without defaults)
        let provided_fields: HashSet<String> = struct_lit
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();

        for (i, field) in fields.iter().enumerate() {
            // Skip fields that have defaults - they are optional
            let has_default = field_has_default.get(i).copied().unwrap_or(false);
            if has_default {
                continue;
            }

            let field_name = {
                let table = self.name_table();
                table.last_segment_str(field.name_id)
            };
            if let Some(field_name) = field_name
                && !provided_fields.contains(&field_name)
            {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: field_name,
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field
        for field_init in &struct_lit.fields {
            // Check for shorthand syntax with undefined variable first
            if self.check_shorthand_undefined(field_init, interner) {
                // Error already reported, skip normal type checking for this field
                continue;
            }

            let field_init_name = interner.resolve(field_init.name);
            if let Some(expected_field) = fields.iter().find(|f| {
                self.name_table()
                    .last_segment_str(f.name_id)
                    .is_some_and(|n| n == field_init_name)
            }) {
                // check_expr_expecting_id will report errors if types don't match
                self.check_expr_expecting_id(&field_init.value, Some(expected_field.ty), interner)?;
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
        Ok(result_type_id)
    }

    /// Check a struct literal for a generic record, inferring type parameters from field values
    fn check_generic_struct_literal(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        type_def_id: TypeDefId,
        generic_info: &GenericTypeInfo,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let type_name = interner.resolve(struct_lit.name).to_string();

        // First, type-check all field values to get their actual types (as TypeId)
        // Use string keys since Symbols may be from different interners
        let mut field_value_type_ids: FxHashMap<String, ArenaTypeId> = FxHashMap::default();
        for field_init in &struct_lit.fields {
            // Check for shorthand syntax with undefined variable first
            if self.check_shorthand_undefined(field_init, interner) {
                // Error already reported, use invalid type for this field
                field_value_type_ids.insert(
                    interner.resolve(field_init.name).to_string(),
                    ArenaTypeId::INVALID,
                );
                continue;
            }
            let field_ty_id = self.check_expr(&field_init.value, interner)?;
            field_value_type_ids.insert(interner.resolve(field_init.name).to_string(), field_ty_id);
        }

        // Build parallel arrays of expected types (from generic def) and actual types (from values)
        // for type parameter inference - using TypeId directly
        let mut expected_type_ids = Vec::new();
        let mut actual_type_ids = Vec::new();

        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            if let Some(field_name_str) = self.name_table().last_segment_str(*field_name_id)
                && let Some(&actual_ty_id) = field_value_type_ids.get(&field_name_str)
            {
                expected_type_ids.push(generic_info.field_types[i]);
                actual_type_ids.push(actual_ty_id);
            }
        }

        // Infer type parameters from field values (using TypeId version)
        let inferred_id = self.infer_type_params_id(
            &generic_info.type_params,
            &expected_type_ids,
            &actual_type_ids,
        );

        // Check type parameter constraints
        self.check_type_param_constraints_id(
            &generic_info.type_params,
            &inferred_id,
            expr.span,
            interner,
        );

        // Substitute inferred types into field types to get concrete field types via arena
        let subs: FxHashMap<_, _> = inferred_id.iter().map(|(&k, &v)| (k, v)).collect();
        let concrete_field_type_ids: Vec<ArenaTypeId> = {
            let mut arena = self.type_arena_mut();
            generic_info
                .field_types
                .iter()
                .map(|&t| arena.substitute(t, &subs))
                .collect()
        };

        // Check that all required fields are present - compare by string value
        // Fields with defaults are optional
        let provided_fields: HashSet<String> = struct_lit
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();

        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            // Skip fields that have defaults - they are optional
            let has_default = generic_info
                .field_has_default
                .get(i)
                .copied()
                .unwrap_or(false);
            if has_default {
                continue;
            }

            let field_name_str = self
                .name_table()
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
                self.name_table().last_segment_str(*name_id).as_deref() == Some(field_init_name_str)
            }) {
                // Use TypeId directly for compatibility check
                let actual_ty_id = *field_value_type_ids
                    .get(field_init_name_str)
                    .expect("field was validated in type check phase");
                let expected_ty_id = concrete_field_type_ids[idx];
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

        // Build type_args from inferred types in order of type params (already TypeId)
        let type_args_id: TypeIdVec = generic_info
            .type_params
            .iter()
            .filter_map(|tp| inferred_id.get(&tp.name_id).copied())
            .collect();

        // Pre-compute substituted field types so codegen can use lookup_substitute
        self.precompute_field_substitutions(type_def_id, &type_args_id);

        Ok(self
            .type_arena_mut()
            .record(type_def_id, type_args_id.to_vec()))
    }

    /// Check a struct literal for a generic class, inferring type parameters from field values
    fn check_generic_class_literal(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        type_def_id: TypeDefId,
        generic_info: &GenericTypeInfo,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let type_name = interner.resolve(struct_lit.name).to_string();

        // First, type-check all field values to get their actual types (as TypeId)
        // Use string keys since Symbols may be from different interners
        let mut field_value_type_ids: FxHashMap<String, ArenaTypeId> = FxHashMap::default();
        for field_init in &struct_lit.fields {
            // Check for shorthand syntax with undefined variable first
            if self.check_shorthand_undefined(field_init, interner) {
                // Error already reported, use invalid type for this field
                field_value_type_ids.insert(
                    interner.resolve(field_init.name).to_string(),
                    ArenaTypeId::INVALID,
                );
                continue;
            }
            let field_ty_id = self.check_expr(&field_init.value, interner)?;
            field_value_type_ids.insert(interner.resolve(field_init.name).to_string(), field_ty_id);
        }

        // Build parallel arrays of expected types (from generic def) and actual types (from values)
        // for type parameter inference - using TypeId directly
        let mut expected_type_ids = Vec::new();
        let mut actual_type_ids = Vec::new();

        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            if let Some(field_name_str) = self.name_table().last_segment_str(*field_name_id)
                && let Some(&actual_ty_id) = field_value_type_ids.get(&field_name_str)
            {
                expected_type_ids.push(generic_info.field_types[i]);
                actual_type_ids.push(actual_ty_id);
            }
        }

        // Infer type parameters from field values (using TypeId version)
        let inferred_id = self.infer_type_params_id(
            &generic_info.type_params,
            &expected_type_ids,
            &actual_type_ids,
        );

        // Check type parameter constraints
        self.check_type_param_constraints_id(
            &generic_info.type_params,
            &inferred_id,
            expr.span,
            interner,
        );

        // Substitute inferred types into field types to get concrete field types via arena
        let subs: FxHashMap<_, _> = inferred_id.iter().map(|(&k, &v)| (k, v)).collect();
        let concrete_field_type_ids: Vec<ArenaTypeId> = {
            let mut arena = self.type_arena_mut();
            generic_info
                .field_types
                .iter()
                .map(|&t| arena.substitute(t, &subs))
                .collect()
        };

        // Check that all required fields are present - compare by string value
        // Fields with defaults are optional
        let provided_fields: HashSet<String> = struct_lit
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();

        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            // Skip fields that have defaults - they are optional
            let has_default = generic_info
                .field_has_default
                .get(i)
                .copied()
                .unwrap_or(false);
            if has_default {
                continue;
            }

            let field_name_str = self
                .name_table()
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
                self.name_table().last_segment_str(*name_id).as_deref() == Some(field_init_name_str)
            }) {
                // Use TypeId directly for compatibility check
                let actual_ty_id = *field_value_type_ids
                    .get(field_init_name_str)
                    .expect("field was validated in type check phase");
                let expected_ty_id = concrete_field_type_ids[idx];
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
        let type_args_id: TypeIdVec = generic_info
            .type_params
            .iter()
            .map(|param| {
                // First try inferred type (already TypeId)
                if let Some(&ty_id) = inferred_id.get(&param.name_id) {
                    return ty_id;
                }
                // Fall back to current type param scope - this handles cases like
                // GenericContainer { _ptr: ... } inside GenericContainer<K,V>.new()
                if let Some(scope) = self.type_param_stack.current() {
                    // Look up by matching the type param name in the current scope
                    let param_name = self.name_table().last_segment_str(param.name_id);
                    if let Some(param_name) = param_name {
                        for scope_param in scope.params() {
                            let scope_param_name =
                                self.name_table().last_segment_str(scope_param.name_id);
                            if scope_param_name.as_deref() == Some(&param_name) {
                                return self.type_arena_mut().type_param(scope_param.name_id);
                            }
                        }
                    }
                }
                ArenaTypeId::INVALID // Unknown type
            })
            .collect();

        // Pre-compute substituted field types so codegen can use lookup_substitute
        self.precompute_field_substitutions(type_def_id, &type_args_id);

        Ok(self
            .type_arena_mut()
            .class(type_def_id, type_args_id.to_vec()))
    }
}
