use super::super::*;

impl Analyzer {
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

        // Get fields from object type
        let (type_name, fields) = match &object_type {
            Type::Class(class_type) => (
                self.name_table
                    .last_segment_str(class_type.name_id)
                    .unwrap_or_else(|| "class".to_string()),
                Some(&class_type.fields),
            ),
            Type::Record(record_type) => (
                self.name_table
                    .last_segment_str(record_type.name_id)
                    .unwrap_or_else(|| "record".to_string()),
                Some(&record_type.fields),
            ),
            Type::Error => return Ok(Type::Error),
            _ => (self.type_display(&object_type), None),
        };

        // Try to find the field (for class/record types)
        let field_name = interner.resolve(field_access.field);
        if let Some(fields) = fields
            && let Some(field) = fields.iter().find(|f| f.name == field_name)
        {
            return Ok(field.ty.clone());
        }

        // No field found - report appropriate error
        if fields.is_some() {
            self.add_error(
                SemanticError::UnknownField {
                    ty: type_name,
                    field: interner.resolve(field_access.field).to_string(),
                    span: field_access.field_span.into(),
                },
                field_access.field_span,
            );
        } else {
            let found = self.type_display(&object_type);
            self.add_error(
                SemanticError::TypeMismatch {
                    expected: "class or record".to_string(),
                    found,
                    span: field_access.object.span.into(),
                },
                field_access.object.span,
            );
        }
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

        // Get fields from inner type
        let (type_name, fields) = match &inner_type {
            Type::Class(class_type) => (
                self.name_table
                    .last_segment_str(class_type.name_id)
                    .unwrap_or_else(|| "class".to_string()),
                &class_type.fields,
            ),
            Type::Record(record_type) => (
                self.name_table
                    .last_segment_str(record_type.name_id)
                    .unwrap_or_else(|| "record".to_string()),
                &record_type.fields,
            ),
            Type::Error => return Ok(Type::Error),
            _ => {
                let found = self.type_display(&object_type);
                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "optional class or record".to_string(),
                        found,
                        span: opt_chain.object.span.into(),
                    },
                    opt_chain.object.span,
                );
                return Ok(Type::Error);
            }
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
                    field: interner.resolve(opt_chain.field).to_string(),
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
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: func_type.params.len(),
                                found: method_call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }

                    // Check argument types
                    for (arg, param_ty) in method_call.args.iter().zip(func_type.params.iter()) {
                        let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                        if !self.types_compatible(&arg_ty, param_ty, interner) {
                            let expected = self.type_display(param_ty);
                            let found = self.type_display(&arg_ty);
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected,
                                    found,
                                    span: arg.span.into(),
                                },
                                arg.span,
                            );
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
                    let found = self.type_display(export_type);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "function".to_string(),
                            found,
                            span: method_call.method_span.into(),
                        },
                        method_call.method_span,
                    );
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
                self.add_error(
                    SemanticError::WrongArgumentCount {
                        expected: func_type.params.len(),
                        found: method_call.args.len(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }

            // Check argument types
            for (arg, param_ty) in method_call.args.iter().zip(func_type.params.iter()) {
                let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                if !self.types_compatible(&arg_ty, param_ty, interner) {
                    let expected = self.type_display(param_ty);
                    let found = self.type_display(&arg_ty);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected,
                            found,
                            span: arg.span.into(),
                        },
                        arg.span,
                    );
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
}
