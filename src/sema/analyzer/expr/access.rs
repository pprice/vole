use super::super::*;
use crate::identity::{NameId, TypeDefId};
use crate::sema::generic::{
    ClassMethodMonomorphInstance, ClassMethodMonomorphKey, StaticMethodMonomorphInstance,
    StaticMethodMonomorphKey, TypeParamInfo, merge_type_params,
};
use crate::sema::implement_registry::ExternalMethodInfo;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::{LegacyType, NominalType};
use std::collections::HashMap;

impl Analyzer {
    /// Get field type from a struct-like type by looking up the type definition
    /// and substituting type arguments if needed.
    fn get_field_type(
        &self,
        type_def_id: TypeDefId,
        type_args: &[LegacyType],
        type_args_id: &[crate::sema::type_arena::TypeId],
        field_name: &str,
    ) -> Option<(String, LegacyType)> {
        let type_def = self.entity_registry.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;

        // Find the field by name and get substituted type
        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            let name = self.name_table.last_segment_str(*field_name_id);
            if name.as_deref() == Some(field_name) {
                let field_type_id = generic_info.field_types[i];

                // Prefer arena-based substitution when type_args_id is available
                let substituted = if !type_args_id.is_empty() {
                    let subst_id = self.entity_registry.substitute_type_id_with_args(
                        type_def_id,
                        type_args_id,
                        field_type_id,
                        &mut self.type_arena.borrow_mut(),
                    );
                    self.type_arena.borrow().to_type(subst_id)
                } else if type_args.is_empty() {
                    self.type_arena.borrow().to_type(field_type_id)
                } else {
                    // Fall back to LegacyType substitution
                    let field_type = self.type_arena.borrow().to_type(field_type_id);
                    self.entity_registry.substitute_type_with_args(
                        type_def_id,
                        type_args,
                        &field_type,
                    )
                };

                let type_name = self
                    .name_table
                    .last_segment_str(type_def.name_id)
                    .unwrap_or_else(|| "struct".to_string());
                return Some((type_name, substituted));
            }
        }

        None
    }

    /// Get the type name and list of field names for a struct-like type (for error messages)
    fn get_struct_info(&self, ty: &LegacyType) -> Option<(String, Vec<String>)> {
        let (type_def_id, _type_args) = match ty {
            LegacyType::Nominal(NominalType::Class(c)) => (c.type_def_id, &c.type_args),
            LegacyType::Nominal(NominalType::Record(r)) => (r.type_def_id, &r.type_args),
            _ => return None,
        };

        let type_def = self.entity_registry.get_type(type_def_id);
        let type_name = self
            .name_table
            .last_segment_str(type_def.name_id)
            .unwrap_or_else(|| "struct".to_string());

        let field_names: Vec<String> = type_def
            .generic_info
            .as_ref()
            .map(|gi| {
                gi.field_names
                    .iter()
                    .filter_map(|name_id| self.name_table.last_segment_str(*name_id))
                    .collect()
            })
            .unwrap_or_default();

        Some((type_name, field_names))
    }

    pub(super) fn check_field_access_expr(
        &mut self,
        field_access: &FieldAccessExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let object_type_id = self.check_expr(&field_access.object, interner)?;
        let object_type = self.id_to_type(object_type_id);

        // Handle module field access
        if let LegacyType::Module(ref module_type) = object_type {
            let field_name = interner.resolve(field_access.field);
            if let Some(name_id) = self.module_name_id(module_type.module_id, field_name)
                && let Some(export_type) = module_type.exports.get(&name_id)
            {
                return Ok(self.type_to_id(export_type));
            } else {
                let module_path = self
                    .name_table
                    .module_path(module_type.module_id)
                    .to_string();
                self.add_error(
                    SemanticError::ModuleNoExport {
                        module: module_path,
                        name: field_name.to_string(),
                        span: field_access.field_span.into(),
                    },
                    field_access.field_span,
                );
                return Ok(self.ty_invalid_traced_id("module_no_export"));
            }
        }

        // Handle Invalid type early - propagate
        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Get fields from object type (Class or Record)
        let field_name = interner.resolve(field_access.field);

        // Extract type_def_id and type_args from the object type
        let LegacyType::Nominal(n) = &object_type else {
            self.type_error_id("class or record", object_type_id, field_access.object.span);
            return Ok(self.ty_invalid_traced_id("field_access_non_struct"));
        };
        if !n.is_struct_like() {
            self.type_error_id("class or record", object_type_id, field_access.object.span);
            return Ok(self.ty_invalid_traced_id("field_access_non_struct"));
        }
        let (type_def_id, type_args, type_args_id) =
            (n.type_def_id(), n.type_args(), n.type_args_id());

        // Try to find the field
        if let Some((_type_name, field_type)) =
            self.get_field_type(type_def_id, type_args, type_args_id, field_name)
        {
            return Ok(self.type_to_id(&field_type));
        }

        // Field not found - get struct info for error message
        let (type_name, available_fields) = self
            .get_struct_info(&object_type)
            .unwrap_or_else(|| ("unknown".to_string(), vec![]));

        self.add_error(
            SemanticError::UnknownField {
                ty: type_name.clone(),
                field: field_name.to_string(),
                span: field_access.field_span.into(),
            },
            field_access.field_span,
        );
        let context = format!(
            "field '{}' not found on {} '{}' (available: {})",
            field_name,
            if matches!(&object_type, LegacyType::Nominal(NominalType::Class(_))) {
                "class"
            } else {
                "record"
            },
            type_name,
            if available_fields.is_empty() {
                "none".to_string()
            } else {
                available_fields.join(", ")
            }
        );
        Ok(self.ty_invalid_traced_id(&context))
    }

    pub(super) fn check_optional_chain_expr(
        &mut self,
        opt_chain: &OptionalChainExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let object_type_id = self.check_expr(&opt_chain.object, interner)?;

        // Handle errors early
        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // The object must be an optional type (union with nil)
        // Check via arena if it's optional and unwrap
        let inner_type_id = if let Some(inner_id) = self.unwrap_optional_id(object_type_id) {
            inner_id
        } else {
            // If not optional, treat it as regular field access wrapped in optional
            // This allows `obj?.field` where obj is not optional (returns T?)
            object_type_id
        };

        // Handle Invalid early
        if inner_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Get type_def_id and type_args from inner type
        let inner_type = self.id_to_type(inner_type_id);
        let LegacyType::Nominal(n) = &inner_type else {
            self.type_error_id(
                "optional class or record",
                object_type_id,
                opt_chain.object.span,
            );
            return Ok(self.ty_invalid_traced_id("optional_chain_non_struct"));
        };
        if !n.is_struct_like() {
            self.type_error_id(
                "optional class or record",
                object_type_id,
                opt_chain.object.span,
            );
            return Ok(self.ty_invalid_traced_id("optional_chain_non_struct"));
        }
        let (type_def_id, type_args, type_args_id) =
            (n.type_def_id(), n.type_args(), n.type_args_id());

        // Find the field
        let field_name = interner.resolve(opt_chain.field);
        if let Some((_type_name, field_type)) =
            self.get_field_type(type_def_id, type_args, type_args_id, field_name)
        {
            let field_type_id = self.type_to_id(&field_type);
            // Result is always optional (field_type | nil)
            // But if field type is already optional, don't double-wrap
            if self.unwrap_optional_id(field_type_id).is_some() {
                Ok(field_type_id)
            } else {
                Ok(self.ty_optional_id(field_type_id))
            }
        } else {
            let (type_name, _) = self
                .get_struct_info(&inner_type)
                .unwrap_or_else(|| ("unknown".to_string(), vec![]));
            self.add_error(
                SemanticError::UnknownField {
                    ty: type_name,
                    field: field_name.to_string(),
                    span: opt_chain.field_span.into(),
                },
                opt_chain.field_span,
            );
            Ok(self.ty_invalid_traced_id("unknown_optional_field"))
        }
    }

    pub(super) fn check_method_call_expr(
        &mut self,
        expr: &Expr,
        method_call: &MethodCallExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check for static method call: TypeName.method()
        // Handle both identifier types (Point.create) and primitive keywords (i32.default_value)
        if let Some((type_def_id, type_name_str)) =
            self.resolve_static_call_target(&method_call.object, interner)
        {
            return self.check_static_method_call(
                expr,
                type_def_id,
                &type_name_str,
                method_call.method,
                &method_call.type_args,
                &method_call.args,
                method_call.method_span,
                interner,
            );
        }

        let object_type_id = self.check_expr(&method_call.object, interner)?;
        let object_type = self.id_to_type(object_type_id);
        let method_name = interner.resolve(method_call.method);

        // Handle Invalid early
        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Optional/union method calls require explicit narrowing.
        if self.is_optional_id(object_type_id) {
            let ty = self.type_display_id(object_type_id);
            self.add_error(
                SemanticError::MethodOnOptional {
                    ty,
                    method: method_name.to_string(),
                    span: method_call.method_span.into(),
                },
                method_call.method_span,
            );
            for arg in &method_call.args {
                self.check_expr(arg, interner)?;
            }
            return Ok(self.ty_invalid_traced_id("method_on_optional"));
        }

        if matches!(object_type, LegacyType::Union(_)) {
            let ty = self.type_display_id(object_type_id);
            self.add_error(
                SemanticError::MethodOnUnion {
                    ty,
                    method: method_name.to_string(),
                    span: method_call.method_span.into(),
                },
                method_call.method_span,
            );
            for arg in &method_call.args {
                self.check_expr(arg, interner)?;
            }
            return Ok(self.ty_invalid_traced_id("method_on_union"));
        }

        // Handle module method calls (e.g., math.sqrt(16.0))
        if let LegacyType::Module(ref module_type) = object_type {
            let method_name_str = interner.resolve(method_call.method);
            let name_id = self.module_name_id(module_type.module_id, method_name_str);

            // Look up the method in module exports
            if let Some(name_id) = name_id
                && let Some(export_type) = module_type.exports.get(&name_id)
            {
                if let LegacyType::Function(func_type) = export_type {
                    // Check argument count
                    if method_call.args.len() != func_type.params.len() {
                        self.add_wrong_arg_count(
                            func_type.params.len(),
                            method_call.args.len(),
                            expr.span,
                        );
                    }

                    // Check argument types
                    for (arg, param_ty) in method_call.args.iter().zip(func_type.params.iter()) {
                        let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                        let arg_ty_id = self.type_to_id(&arg_ty);
                        let param_ty_id = self.type_to_id(param_ty);
                        if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                            self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
                        }
                    }

                    // Record resolution for codegen
                    // Only set external_info for functions in the external_funcs set
                    let external_info = if module_type.external_funcs.contains(&name_id) {
                        Some(ExternalMethodInfo {
                            module_path: self
                                .name_table
                                .module_path(module_type.module_id)
                                .to_string(),
                            native_name: method_name_str.to_string(),
                            return_type: Some(Box::new((*func_type.return_type).clone())),
                        })
                    } else {
                        None
                    };

                    self.method_resolutions.insert(
                        expr.id,
                        ResolvedMethod::Implemented {
                            trait_name: None,
                            func_type: func_type.clone(),
                            is_builtin: false,
                            external_info,
                        },
                    );

                    return Ok(self.type_to_id(&func_type.return_type));
                } else {
                    self.type_error("function", export_type, method_call.method_span);
                    return Ok(ArenaTypeId::INVALID);
                }
            } else {
                self.add_error(
                    SemanticError::ModuleNoExport {
                        module: self
                            .name_table
                            .module_path(module_type.module_id)
                            .to_string(),
                        name: method_name_str.to_string(),
                        span: method_call.method_span.into(),
                    },
                    method_call.method_span,
                );
                return Ok(ArenaTypeId::INVALID);
            }
        }

        // Get a descriptive type name for error messages
        let type_name = self.type_display_id(object_type_id);

        if let Some(resolved) =
            self.resolve_method_via_entity_registry(&object_type, method_call.method, interner)
        {
            if resolved.is_builtin()
                && let Some(func_type) = self.check_builtin_method(
                    &object_type,
                    method_name,
                    &method_call.args,
                    interner,
                )
            {
                let updated = match resolved {
                    ResolvedMethod::Implemented {
                        trait_name,
                        is_builtin,
                        external_info,
                        ..
                    } => ResolvedMethod::Implemented {
                        trait_name,
                        func_type: func_type.clone(),
                        is_builtin,
                        external_info,
                    },
                    other => other,
                };
                self.method_resolutions.insert(expr.id, updated);
                return Ok(self.type_to_id(&func_type.return_type));
            }

            let func_type = resolved.func_type().clone();

            // Mark side effects if inside lambda
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }

            // Check argument count
            if method_call.args.len() != func_type.params.len() {
                self.add_wrong_arg_count(func_type.params.len(), method_call.args.len(), expr.span);
            }

            // Check argument types
            for (arg, param_ty) in method_call.args.iter().zip(func_type.params.iter()) {
                let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                let arg_ty_id = self.type_to_id(&arg_ty);
                let param_ty_id = self.type_to_id(param_ty);
                if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
                }
            }

            // Get external_info before moving resolved
            let external_info = resolved.external_info().cloned();

            self.method_resolutions.insert(expr.id, resolved);

            // Record class method monomorphization for generic classes/records
            self.record_class_method_monomorph(
                expr,
                &object_type,
                method_call.method,
                &func_type,
                external_info,
                interner,
            );

            return Ok(self.type_to_id(&func_type.return_type));
        }

        // No method found - report error
        self.add_error(
            SemanticError::UnknownMethod {
                ty: type_name,
                method: interner.resolve(method_call.method).to_string(),
                span: method_call.method_span.into(),
            },
            method_call.method_span,
        );
        // Still check args for more errors
        for arg in &method_call.args {
            self.check_expr(arg, interner)?;
        }
        Ok(ArenaTypeId::INVALID)
    }

    /// Try to resolve a static method call target from an expression.
    /// Returns (TypeDefId, type_name) if this is a valid static call target.
    /// Handles both identifier types (Point.create) and primitive keywords (i32.default_value)
    fn resolve_static_call_target(
        &self,
        object: &Expr,
        interner: &Interner,
    ) -> Option<(TypeDefId, String)> {
        match &object.kind {
            // Named types: Point.create(), MyClass.static_method()
            ExprKind::Identifier(type_sym) => {
                // Only consider this a static call if it's not a variable
                if self.get_variable_type(*type_sym).is_some() {
                    return None;
                }
                let type_name_str = interner.resolve(*type_sym).to_string();
                // Use resolve_type_or_interface to also find prelude classes like Map/Set
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type_or_interface(*type_sym, &self.entity_registry)?;
                tracing::trace!(type_name = %type_name_str, ?type_def_id, "resolved static call target (identifier)");
                Some((type_def_id, type_name_str))
            }
            // Primitive type keywords: i32.default_value(), bool.default_value()
            ExprKind::TypeLiteral(type_expr) => {
                use crate::frontend::ast::TypeExpr;
                if let TypeExpr::Primitive(prim) = type_expr {
                    let name_id = self.name_table.primitives.from_ast(*prim);
                    let type_def_id = self.entity_registry.type_by_name(name_id)?;
                    let type_name = self.name_table.display(name_id);
                    tracing::trace!(%type_name, ?type_def_id, "resolved static call target (primitive)");
                    Some((type_def_id, type_name))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Check a static method call: TypeName.method(args) or TypeName.method<T, U>(args)
    #[allow(clippy::too_many_arguments)]
    fn check_static_method_call(
        &mut self,
        expr: &Expr,
        type_def_id: TypeDefId,
        type_name_str: &str,
        method_sym: Symbol,
        explicit_type_args: &[TypeExpr],
        args: &[Expr],
        method_span: Span,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let method_name_str = interner.resolve(method_sym);
        let method_name_id = self.method_name_id(method_sym, interner);

        // Look up the static method on this type
        if let Some(method_id) = self
            .entity_registry
            .find_static_method_on_type(type_def_id, method_name_id)
        {
            let method_def = self.entity_registry.get_method(method_id);
            let func_type = method_def.signature.clone();
            let method_type_params = method_def.method_type_params.clone();

            // Check argument count
            if args.len() != func_type.params.len() {
                self.add_wrong_arg_count(func_type.params.len(), args.len(), expr.span);
            }

            // Get type params from the generic class/record definition
            let type_def = self.entity_registry.get_type(type_def_id);
            let generic_info = type_def.generic_info.clone();

            // First pass: type-check arguments to get their types (as TypeId, then convert to LegacyType for inference)
            let mut arg_type_ids = Vec::new();
            for arg in args {
                let arg_ty_id = self.check_expr(arg, interner)?;
                arg_type_ids.push(arg_ty_id);
            }
            // Convert to LegacyType for type inference (still uses LegacyType)
            let arg_types: Vec<LegacyType> =
                arg_type_ids.iter().map(|&id| self.id_to_type(id)).collect();

            // Get class-level type params (if any)
            let class_type_params: Vec<TypeParamInfo> = generic_info
                .as_ref()
                .map(|info| info.type_params.clone())
                .unwrap_or_default();

            // Combine class and method type params for inference
            let all_type_params = merge_type_params(&class_type_params, &method_type_params);

            // Infer type params if there are any (class-level or method-level)
            let (final_params, final_return_id, maybe_inferred) = if !all_type_params.is_empty() {
                // Build substitution map from explicit type args if provided
                let inferred = if !explicit_type_args.is_empty() {
                    // Resolve explicit type args and map to class type params
                    if explicit_type_args.len() != class_type_params.len() {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: class_type_params.len(),
                                found: explicit_type_args.len(),
                                span: method_span.into(),
                            },
                            method_span,
                        );
                    }
                    let mut explicit_map = std::collections::HashMap::new();
                    for (param, type_expr) in
                        class_type_params.iter().zip(explicit_type_args.iter())
                    {
                        let resolved = self.resolve_type(type_expr, interner);
                        explicit_map.insert(param.name_id, resolved);
                    }
                    explicit_map
                } else {
                    // Infer type params from argument types
                    self.infer_type_params(&all_type_params, &func_type.params, &arg_types)
                };

                // Substitute inferred types into param types and return type using arena
                let (substituted_params, substituted_return) = if let LegacyType::Function(ft) =
                    LegacyType::Function(func_type.clone())
                        .substitute_with_arena(&inferred, &mut self.type_arena.borrow_mut())
                {
                    (ft.params.to_vec(), (*ft.return_type).clone())
                } else {
                    unreachable!("substitute_with_arena on Function returns Function")
                };

                // Check type parameter constraints for class type params
                if !class_type_params.is_empty() {
                    self.check_type_param_constraints(
                        &class_type_params,
                        &inferred,
                        expr.span,
                        interner,
                    );
                }

                // Check type parameter constraints for method type params
                if !method_type_params.is_empty() {
                    self.check_type_param_constraints(
                        &method_type_params,
                        &inferred,
                        expr.span,
                        interner,
                    );
                }

                (
                    substituted_params,
                    self.type_to_id(&substituted_return),
                    Some(inferred),
                )
            } else {
                (
                    func_type.params.to_vec(),
                    self.type_to_id(&func_type.return_type),
                    None,
                )
            };

            // Second pass: check argument types against (potentially substituted) param types
            for (arg, (arg_ty_id, param_ty)) in args
                .iter()
                .zip(arg_type_ids.iter().zip(final_params.iter()))
            {
                let param_ty_id = self.type_to_id(param_ty);
                if !self.types_compatible_id(*arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, *arg_ty_id, arg.span);
                }
            }

            // Record resolution for codegen
            self.method_resolutions.insert(
                expr.id,
                ResolvedMethod::Static {
                    type_def_id,
                    method_id,
                    func_type: func_type.clone(),
                },
            );

            // Record static method monomorphization if there are any type params
            if let Some(ref inferred) = maybe_inferred
                && !inferred.is_empty()
            {
                self.record_static_method_monomorph(
                    expr,
                    type_def_id,
                    method_sym,
                    &func_type,
                    &class_type_params,
                    &method_type_params,
                    inferred,
                    interner,
                );
            }

            return Ok(final_return_id);
        }

        // No static method found - report error
        self.add_error(
            SemanticError::UnknownMethod {
                ty: type_name_str.to_string(),
                method: method_name_str.to_string(),
                span: method_span.into(),
            },
            method_span,
        );

        // Still check args for more errors
        for arg in args {
            self.check_expr(arg, interner)?;
        }

        Ok(ArenaTypeId::INVALID)
    }

    /// Record a class method monomorphization for generic class/record method calls.
    /// Creates or retrieves a monomorphized instance and records the call site.
    fn record_class_method_monomorph(
        &mut self,
        expr: &Expr,
        object_type: &LegacyType,
        method_sym: Symbol,
        func_type: &FunctionType,
        external_info: Option<ExternalMethodInfo>,
        interner: &Interner,
    ) {
        // Extract type_def_id and type_args
        // Note: We only record monomorphs for concrete types (Class/Record) that have
        // method bodies to compile. Interface types use vtable dispatch and don't need monomorphs.
        tracing::debug!(object_type = ?object_type, "record_class_method_monomorph called");
        let (class_type_def_id, type_args) = match object_type {
            LegacyType::Nominal(NominalType::Class(c)) if !c.type_args.is_empty() => {
                (c.type_def_id, &c.type_args)
            }
            LegacyType::Nominal(NominalType::Record(r)) if !r.type_args.is_empty() => {
                (r.type_def_id, &r.type_args)
            }
            _ => {
                tracing::debug!("returning early - not a generic class/record");
                return; // Not a generic class/record, nothing to record
            }
        };

        let class_name_id = self.entity_registry.get_type(class_type_def_id).name_id;
        tracing::debug!(
            class_name_id = ?class_name_id,
            type_args = ?type_args,
            "extracted generic type info"
        );

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Create type keys for the type arguments
        let type_keys: Vec<_> = type_args
            .iter()
            .map(|t| self.entity_registry.type_table.key_for_type(t))
            .collect();

        // Create the monomorph key
        let key = ClassMethodMonomorphKey::new(class_name_id, method_name_id, type_keys);

        // Create/cache the monomorph instance
        if !self
            .entity_registry
            .class_method_monomorph_cache
            .contains(&key)
        {
            // Get the generic type definition for substitution info
            let type_def = self.entity_registry.get_type(class_type_def_id);
            let substitutions = if let Some(generic_info) = &type_def.generic_info {
                let mut subs = HashMap::new();
                let mut arena = self.type_arena.borrow_mut();
                for (param, arg) in generic_info.type_params.iter().zip(type_args.iter()) {
                    subs.insert(param.name_id, arena.from_type(arg));
                }
                subs
            } else {
                HashMap::new()
            };

            // Generate unique mangled name
            let instance_id = self
                .entity_registry
                .class_method_monomorph_cache
                .next_unique_id();
            let class_name = self
                .name_table
                .last_segment_str(class_name_id)
                .unwrap_or_else(|| "class".to_string());
            let method_name = interner.resolve(method_sym);
            let mangled_name_str = format!(
                "{}__method_{}__mono_{}",
                class_name, method_name, instance_id
            );
            let mangled_name = self
                .name_table
                .intern_raw(self.current_module, &[&mangled_name_str]);

            let instance = ClassMethodMonomorphInstance {
                class_name: class_name_id,
                method_name: method_name_id,
                mangled_name,
                instance_id,
                func_type: func_type.clone(),
                substitutions,
                external_info,
            };

            tracing::debug!(
                mangled_name = %mangled_name_str,
                "inserting class method monomorph instance"
            );
            self.entity_registry
                .class_method_monomorph_cache
                .insert(key.clone(), instance);
        }

        // Record the call site → key mapping
        tracing::debug!(expr_id = ?expr.id, key = ?key, "recording call site");
        self.class_method_calls.insert(expr.id, key);
    }

    /// Record a static method monomorphization for generic class/record static method calls.
    /// Creates or retrieves a monomorphized instance and records the call site.
    #[allow(clippy::too_many_arguments)]
    fn record_static_method_monomorph(
        &mut self,
        expr: &Expr,
        type_def_id: TypeDefId,
        method_sym: Symbol,
        func_type: &FunctionType,
        class_type_params: &[TypeParamInfo],
        method_type_params: &[TypeParamInfo],
        inferred: &std::collections::HashMap<NameId, LegacyType>,
        interner: &Interner,
    ) {
        // Get the type def to extract name and type args
        let type_def = self.entity_registry.get_type(type_def_id);
        let class_name_id = type_def.name_id;

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Create type keys for class type params (in type param order)
        let class_type_keys: Vec<_> = class_type_params
            .iter()
            .filter_map(|tp| inferred.get(&tp.name_id))
            .map(|t| self.entity_registry.type_table.key_for_type(t))
            .collect();

        // Create type keys for method type params (in type param order)
        let method_type_keys: Vec<_> = method_type_params
            .iter()
            .filter_map(|tp| inferred.get(&tp.name_id))
            .map(|t| self.entity_registry.type_table.key_for_type(t))
            .collect();

        // Create the monomorph key with separate class and method type keys
        let key = StaticMethodMonomorphKey::new(
            class_name_id,
            method_name_id,
            class_type_keys,
            method_type_keys,
        );

        // Create/cache the monomorph instance
        if !self
            .entity_registry
            .static_method_monomorph_cache
            .contains(&key)
        {
            // Build substitutions from type params to inferred types
            let legacy_substitutions: HashMap<NameId, LegacyType> = inferred.clone();

            // Generate unique mangled name
            let instance_id = self
                .entity_registry
                .static_method_monomorph_cache
                .next_unique_id();
            let class_name = self
                .name_table
                .last_segment_str(class_name_id)
                .unwrap_or_else(|| "class".to_string());
            let method_name = interner.resolve(method_sym);
            let mangled_name_str = format!(
                "{}__static_{}__mono_{}",
                class_name, method_name, instance_id
            );
            let mangled_name = self
                .name_table
                .intern_raw(self.current_module, &[&mangled_name_str]);

            // Create the substituted function type using arena
            let substituted_func_type = if let LegacyType::Function(ft) =
                LegacyType::Function(func_type.clone())
                    .substitute_with_arena(&legacy_substitutions, &mut self.type_arena.borrow_mut())
            {
                ft
            } else {
                unreachable!("substitute_with_arena on Function returns Function")
            };

            // Convert substitutions to TypeId for storage
            let substitutions = {
                let mut arena = self.type_arena.borrow_mut();
                legacy_substitutions
                    .iter()
                    .map(|(k, v)| (*k, arena.from_type(v)))
                    .collect()
            };

            let instance = StaticMethodMonomorphInstance {
                class_name: class_name_id,
                method_name: method_name_id,
                mangled_name,
                instance_id,
                func_type: substituted_func_type,
                substitutions,
            };

            tracing::debug!(
                mangled_name = %mangled_name_str,
                "inserting static method monomorph instance"
            );
            self.entity_registry
                .static_method_monomorph_cache
                .insert(key.clone(), instance);
        }

        // Record the call site → key mapping
        tracing::debug!(expr_id = ?expr.id, key = ?key, "recording static method call site");
        self.static_method_calls.insert(expr.id, key);
    }
}
