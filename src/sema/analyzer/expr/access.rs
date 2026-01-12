use super::super::*;
use crate::identity::{NameId, TypeDefId};
use crate::sema::generic::substitute_type;
use std::collections::HashMap;

impl Analyzer {
    /// Get struct name and fields from a type (for field access operations).
    /// Returns None for non-struct types.
    fn get_struct_info<'a>(&self, ty: &'a Type) -> Option<(String, &'a [StructField])> {
        match ty {
            Type::Class(class_type) => Some((
                self.name_table
                    .last_segment_str(class_type.name_id)
                    .unwrap_or_else(|| "class".to_string()),
                &class_type.fields,
            )),
            Type::Record(record_type) => Some((
                self.name_table
                    .last_segment_str(record_type.name_id)
                    .unwrap_or_else(|| "record".to_string()),
                &record_type.fields,
            )),
            _ => None,
        }
    }

    /// Get field type from a GenericInstance type by looking up the generic definition
    /// and substituting type arguments.
    fn get_generic_instance_field(
        &self,
        def: &NameId,
        args: &[Type],
        field_name: &str,
        interner: &Interner,
    ) -> Option<(String, Type)> {
        // Look up the type definition
        let type_def_id = self.entity_registry.type_by_name(*def)?;
        let type_def = self.entity_registry.get_type(type_def_id);

        // Get the generic info (field names and types with type params)
        let generic_info = type_def.generic_info.as_ref()?;

        // Build substitution map: type param NameId -> concrete type
        let mut substitutions = HashMap::new();
        for (param, arg) in generic_info.type_params.iter().zip(args.iter()) {
            substitutions.insert(param.name_id, arg.clone());
        }

        // Find the field by name
        for (i, field_sym) in generic_info.field_names.iter().enumerate() {
            let name = interner.resolve(*field_sym);
            if name == field_name {
                // Substitute type arguments in field type
                let field_type = &generic_info.field_types[i];
                let substituted = substitute_type(field_type, &substitutions);
                let type_name = self
                    .name_table
                    .last_segment_str(*def)
                    .unwrap_or_else(|| "generic".to_string());
                return Some((type_name, substituted));
            }
        }

        None
    }

    pub(super) fn check_field_access_expr(
        &mut self,
        field_access: &FieldAccessExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let object_type = self.check_expr(&field_access.object, interner)?;

        // Handle module field access
        if let Type::Module(ref module_type) = object_type {
            let field_name = interner.resolve(field_access.field);
            if let Some(name_id) = self.module_name_id(module_type.module_id, field_name)
                && let Some(export_type) = module_type.exports.get(&name_id)
            {
                return Ok(export_type.clone());
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
                return Ok(Type::Error);
            }
        }

        // Handle Type::Error early
        if matches!(object_type, Type::Error) {
            return Ok(Type::Error);
        }

        // Get fields from object type
        let field_name = interner.resolve(field_access.field);
        if let Some((type_name, fields)) = self.get_struct_info(&object_type) {
            // Try to find the field
            if let Some(field) = fields.iter().find(|f| f.name == field_name) {
                return Ok(field.ty.clone());
            }
            // Field not found on struct type
            self.add_error(
                SemanticError::UnknownField {
                    ty: type_name,
                    field: field_name.to_string(),
                    span: field_access.field_span.into(),
                },
                field_access.field_span,
            );
            return Ok(Type::Error);
        }

        // Handle GenericInstance (e.g., Container<i64>)
        if let Type::GenericInstance { def, args } = &object_type {
            if let Some((_type_name, field_type)) =
                self.get_generic_instance_field(def, args, field_name, interner)
            {
                return Ok(field_type);
            }
            // GenericInstance but field not found - report error
            let type_name = self
                .name_table
                .last_segment_str(*def)
                .unwrap_or_else(|| "generic".to_string());
            self.add_error(
                SemanticError::UnknownField {
                    ty: type_name,
                    field: field_name.to_string(),
                    span: field_access.field_span.into(),
                },
                field_access.field_span,
            );
            return Ok(Type::Error);
        }

        // Not a struct type
        self.type_error("class or record", &object_type, field_access.object.span);
        Ok(Type::Error)
    }

    pub(super) fn check_optional_chain_expr(
        &mut self,
        opt_chain: &OptionalChainExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let object_type = self.check_expr(&opt_chain.object, interner)?;

        // Handle errors early
        if matches!(object_type, Type::Error) {
            return Ok(Type::Error);
        }

        // The object must be an optional type (union with nil)
        let inner_type = if object_type.is_optional() {
            object_type.unwrap_optional().unwrap_or(Type::Error)
        } else {
            // If not optional, treat it as regular field access wrapped in optional
            // This allows `obj?.field` where obj is not optional (returns T?)
            object_type.clone()
        };

        // Handle Type::Error early
        if matches!(inner_type, Type::Error) {
            return Ok(Type::Error);
        }

        // Get fields from inner type
        let Some((type_name, fields)) = self.get_struct_info(&inner_type) else {
            self.type_error(
                "optional class or record",
                &object_type,
                opt_chain.object.span,
            );
            return Ok(Type::Error);
        };

        // Find the field
        let field_name = interner.resolve(opt_chain.field);
        if let Some(field) = fields.iter().find(|f| f.name == field_name) {
            // Result is always optional (field_type | nil)
            // But if field type is already optional, don't double-wrap
            if field.ty.is_optional() {
                Ok(field.ty.clone())
            } else {
                Ok(Type::optional(field.ty.clone()))
            }
        } else {
            self.add_error(
                SemanticError::UnknownField {
                    ty: type_name,
                    field: field_name.to_string(),
                    span: opt_chain.field_span.into(),
                },
                opt_chain.field_span,
            );
            Ok(Type::Error)
        }
    }

    pub(super) fn check_method_call_expr(
        &mut self,
        expr: &Expr,
        method_call: &MethodCallExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
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
                &method_call.args,
                method_call.method_span,
                interner,
            );
        }

        let object_type = self.check_expr(&method_call.object, interner)?;
        let method_name = interner.resolve(method_call.method);

        // Handle Type::Error early
        if matches!(object_type, Type::Error) {
            return Ok(Type::Error);
        }

        // Optional/union method calls require explicit narrowing.
        if object_type.is_optional() {
            let ty = self.type_display(&object_type);
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
            return Ok(Type::Error);
        }

        if matches!(object_type, Type::Union(_)) {
            let ty = self.type_display(&object_type);
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
            return Ok(Type::Error);
        }

        // Handle module method calls (e.g., math.sqrt(16.0))
        if let Type::Module(ref module_type) = object_type {
            let method_name_str = interner.resolve(method_call.method);
            let name_id = self.module_name_id(module_type.module_id, method_name_str);

            // Look up the method in module exports
            if let Some(name_id) = name_id
                && let Some(export_type) = module_type.exports.get(&name_id)
            {
                if let Type::Function(func_type) = export_type {
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
                        if !self.types_compatible(&arg_ty, param_ty, interner) {
                            self.add_type_mismatch(param_ty, &arg_ty, arg.span);
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

                    return Ok(*func_type.return_type.clone());
                } else {
                    self.type_error("function", export_type, method_call.method_span);
                    return Ok(Type::Error);
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
                return Ok(Type::Error);
            }
        }

        // Get a descriptive type name for error messages
        let type_name = self.type_display(&object_type);

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
                return Ok(*func_type.return_type);
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
                if !self.types_compatible(&arg_ty, param_ty, interner) {
                    self.add_type_mismatch(param_ty, &arg_ty, arg.span);
                }
            }

            self.method_resolutions.insert(expr.id, resolved);
            return Ok(*func_type.return_type);
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
        Ok(Type::Error)
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
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type(*type_sym, &self.entity_registry)?;
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

    /// Check a static method call: TypeName.method(args)
    #[allow(clippy::too_many_arguments)]
    fn check_static_method_call(
        &mut self,
        expr: &Expr,
        type_def_id: TypeDefId,
        type_name_str: &str,
        method_sym: Symbol,
        args: &[Expr],
        method_span: Span,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let method_name_str = interner.resolve(method_sym);
        let method_name_id = self.method_name_id(method_sym, interner);

        // Look up the static method on this type
        if let Some(method_id) = self
            .entity_registry
            .find_static_method_on_type(type_def_id, method_name_id)
        {
            let method_def = self.entity_registry.get_method(method_id);
            let func_type = method_def.signature.clone();

            // Check argument count
            if args.len() != func_type.params.len() {
                self.add_wrong_arg_count(func_type.params.len(), args.len(), expr.span);
            }

            // Check argument types
            for (arg, param_ty) in args.iter().zip(func_type.params.iter()) {
                let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                if !self.types_compatible(&arg_ty, param_ty, interner) {
                    self.add_type_mismatch(param_ty, &arg_ty, arg.span);
                }
            }

            let return_type = (*func_type.return_type).clone();

            // Record resolution for codegen
            self.method_resolutions.insert(
                expr.id,
                ResolvedMethod::Static {
                    type_def_id,
                    method_id,
                    func_type: func_type.clone(),
                },
            );

            return Ok(return_type);
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

        Ok(Type::Error)
    }
}
