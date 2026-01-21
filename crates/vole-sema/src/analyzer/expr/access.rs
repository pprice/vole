use super::super::*;
use crate::generic::{
    ClassMethodMonomorphInstance, ClassMethodMonomorphKey, StaticMethodMonomorphInstance,
    StaticMethodMonomorphKey, TypeParamInfo, merge_type_params,
};
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
use std::collections::HashMap;
use vole_identity::{NameId, TypeDefId};

impl Analyzer {
    /// Get field type from a struct-like type by looking up the type definition
    /// and substituting type arguments if needed. Returns TypeId directly.
    fn get_field_type_id(
        &self,
        type_def_id: TypeDefId,
        type_args_id: &[crate::type_arena::TypeId],
        field_name: &str,
    ) -> Option<ArenaTypeId> {
        // Get generic info (cloning to avoid holding borrow)
        let generic_info = {
            let registry = self.entity_registry();
            let type_def = registry.get_type(type_def_id);
            type_def.generic_info.clone()?
        };

        // Find the field by name and get substituted type
        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            let name = self.name_table().last_segment_str(*field_name_id);
            if name.as_deref() == Some(field_name) {
                let field_type_id = generic_info.field_types[i];

                // Use arena-based substitution - get raw pointer to arena to avoid borrow conflict
                let mut db = self.db.borrow_mut();
                let arena = &mut db.types as *mut _;
                let substituted_id = db.entities.substitute_type_id_with_args(
                    type_def_id,
                    type_args_id,
                    field_type_id,
                    unsafe { &mut *arena },
                );
                return Some(substituted_id);
            }
        }

        None
    }

    pub(super) fn check_field_access_expr(
        &mut self,
        field_access: &FieldAccessExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let object_type_id = self.check_expr(&field_access.object, interner)?;

        // Extract module data while holding the borrow, then release before calling add_error
        let module_info = {
            let arena = self.type_arena();
            arena.unwrap_module(object_type_id).map(|module| {
                let field_name = interner.resolve(field_access.field);
                let module_id = module.module_id;
                // Find export type if name matches
                let export_type_id =
                    self.module_name_id(module_id, field_name)
                        .and_then(|name_id| {
                            module
                                .exports
                                .iter()
                                .find(|(n, _)| *n == name_id)
                                .map(|&(_, type_id)| type_id)
                        });
                (module_id, field_name.to_string(), export_type_id)
            })
        };
        if let Some((module_id, field_name, export_type_id)) = module_info {
            if let Some(type_id) = export_type_id {
                return Ok(type_id);
            }
            // Export not found - emit error
            let module_path = self.name_table().module_path(module_id).to_string();
            self.add_error(
                SemanticError::ModuleNoExport {
                    module: module_path,
                    name: field_name,
                    span: field_access.field_span.into(),
                },
                field_access.field_span,
            );
            return Ok(self.ty_invalid_traced_id("module_no_export"));
        }

        // Handle Invalid type early - propagate
        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Get fields from object type (Class or Record)
        let field_name = interner.resolve(field_access.field);

        let struct_info = {
            let arena = self.type_arena();
            if let Some((id, args)) = arena.unwrap_class(object_type_id) {
                Some((id, args.clone(), true)) // is_class = true
            } else if let Some((id, args)) = arena.unwrap_record(object_type_id) {
                Some((id, args.clone(), false)) // is_class = false
            } else {
                None
            }
        };
        let Some((type_def_id, type_args_id, is_class)) = struct_info else {
            self.type_error_id("class or record", object_type_id, field_access.object.span);
            return Ok(self.ty_invalid_traced_id("field_access_non_struct"));
        };

        // Try to find the field
        if let Some(field_type_id) = self.get_field_type_id(type_def_id, &type_args_id, field_name)
        {
            return Ok(field_type_id);
        }

        // Field not found - get struct info for error message using type_def_id
        let (type_name, available_fields) = {
            let registry = self.entity_registry();
            let type_def = registry.get_type(type_def_id);
            let type_name = self
                .name_table()
                .last_segment_str(type_def.name_id)
                .unwrap_or_else(|| "struct".to_string());
            let available_fields: Vec<String> = type_def
                .generic_info
                .as_ref()
                .map(|gi| {
                    gi.field_names
                        .iter()
                        .filter_map(|name_id| self.name_table().last_segment_str(*name_id))
                        .collect()
                })
                .unwrap_or_default();
            (type_name, available_fields)
        };

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
            if is_class { "class" } else { "record" },
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

        // Get type_def_id and type_args from inner type using arena queries
        let struct_info = {
            let arena = self.type_arena();
            if let Some((id, args)) = arena.unwrap_class(inner_type_id) {
                Some((id, args.clone()))
            } else if let Some((id, args)) = arena.unwrap_record(inner_type_id) {
                Some((id, args.clone()))
            } else {
                None
            }
        };
        let Some((type_def_id, type_args_id)) = struct_info else {
            self.type_error_id(
                "optional class or record",
                object_type_id,
                opt_chain.object.span,
            );
            return Ok(self.ty_invalid_traced_id("optional_chain_non_struct"));
        };

        // Find the field
        let field_name = interner.resolve(opt_chain.field);
        if let Some(field_type_id) = self.get_field_type_id(type_def_id, &type_args_id, field_name)
        {
            // Result is always optional (field_type | nil)
            // But if field type is already optional, don't double-wrap
            if self.unwrap_optional_id(field_type_id).is_some() {
                Ok(field_type_id)
            } else {
                Ok(self.ty_optional_id(field_type_id))
            }
        } else {
            // Get type name for error message using type_def_id
            let name_id = {
                let registry = self.entity_registry();
                registry.get_type(type_def_id).name_id
            };
            let type_name = self
                .name_table()
                .last_segment_str(name_id)
                .unwrap_or_else(|| "struct".to_string());
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

        if self.type_arena().is_union(object_type_id) {
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

        // Handle module method calls (e.g., math.sqrt(16.0)) using TypeId-based lookup
        let module_info = {
            let arena = self.type_arena();
            arena.unwrap_module(object_type_id).map(|m| {
                let method_name_str = interner.resolve(method_call.method);
                let name_id = self.module_name_id(m.module_id, method_name_str);
                // Find export type if name matches
                let export_type_id = name_id.and_then(|nid| {
                    m.exports
                        .iter()
                        .find(|(n, _)| *n == nid)
                        .map(|&(_, type_id)| type_id)
                });
                (
                    m.module_id,
                    method_name_str.to_string(),
                    name_id,
                    export_type_id,
                )
            })
        };
        if let Some((module_id, method_name_str, name_id, export_type_id)) = module_info {
            let module_path = self.name_table().module_path(module_id).to_string();
            let Some(name_id) = name_id else {
                self.add_error(
                    SemanticError::ModuleNoExport {
                        module: module_path,
                        name: method_name_str,
                        span: method_call.method_span.into(),
                    },
                    method_call.method_span,
                );
                return Ok(ArenaTypeId::INVALID);
            };
            let Some(export_type_id) = export_type_id else {
                self.add_error(
                    SemanticError::ModuleNoExport {
                        module: module_path,
                        name: method_name_str,
                        span: method_call.method_span.into(),
                    },
                    method_call.method_span,
                );
                return Ok(ArenaTypeId::INVALID);
            };

            // Check if export is a function using arena
            let func_info = {
                let arena = self.type_arena();
                arena
                    .unwrap_function(export_type_id)
                    .map(|(params, ret, is_closure)| (params.clone(), ret, is_closure))
            };
            let Some((param_ids, return_id, _is_closure)) = func_info else {
                self.type_error_id("function", export_type_id, method_call.method_span);
                return Ok(ArenaTypeId::INVALID);
            };

            // Check arguments using TypeId-based checking
            self.check_call_args_id(
                &method_call.args,
                &param_ids,
                return_id,
                expr.span,
                interner,
            )?;

            // Build FunctionType for resolution storage (still needed for codegen)
            let func_type = FunctionType::from_ids(&param_ids, return_id, false);
            let func_type_id = func_type.intern(&mut self.type_arena_mut());

            // Get external_funcs from module metadata
            let is_external = self
                .type_arena()
                .module_metadata(module_id)
                .is_some_and(|meta| meta.external_funcs.contains(&name_id));

            let external_info = if is_external {
                // Extract values before struct construction to avoid RefMut lifetime overlap
                let builtin_module = self.name_table_mut().builtin_module();
                let module_path_str = self.name_table().module_path(module_id).to_string();
                let module_path_id = self
                    .name_table_mut()
                    .intern_raw(builtin_module, &[&module_path_str]);
                let native_name_id = self
                    .name_table_mut()
                    .intern_raw(builtin_module, &[&method_name_str]);
                Some(ExternalMethodInfo {
                    module_path: module_path_id,
                    native_name: native_name_id,
                })
            } else {
                None
            };

            self.method_resolutions.insert(
                expr.id,
                ResolvedMethod::Implemented {
                    trait_name: None,
                    func_type_id,
                    is_builtin: false,
                    external_info,
                },
            );

            return Ok(return_id);
        }

        // Get a descriptive type name for error messages
        let type_name = self.type_display_id(object_type_id);

        if let Some(resolved) =
            self.resolve_method_via_entity_registry_id(object_type_id, method_call.method, interner)
        {
            if resolved.is_builtin()
                && let Some(func_type) = self.check_builtin_method_id(
                    object_type_id,
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
                    } => {
                        let func_type_id = func_type.intern(&mut self.type_arena_mut());
                        ResolvedMethod::Implemented {
                            trait_name,
                            func_type_id,
                            is_builtin,
                            external_info,
                        }
                    }
                    other => other,
                };
                self.method_resolutions.insert(expr.id, updated);
                return Ok(func_type.return_type_id);
            }

            // Reconstruct FunctionType from arena for arg checking and monomorph recording
            let func_type = {
                let arena = self.type_arena();
                let (params, ret, is_closure) = arena
                    .unwrap_function(resolved.func_type_id())
                    .expect("resolved method must have function type");
                FunctionType {
                    is_closure,
                    params_id: params.clone(),
                    return_type_id: ret,
                }
            };

            // Mark side effects if inside lambda
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }

            // Check argument count
            if method_call.args.len() != func_type.params_id.len() {
                self.add_wrong_arg_count(
                    func_type.params_id.len(),
                    method_call.args.len(),
                    expr.span,
                );
            }

            // Check argument types using TypeId directly
            for (arg, &param_ty_id) in method_call.args.iter().zip(func_type.params_id.iter()) {
                let arg_ty_id = self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?;
                if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
                }
            }

            // Get external_info before moving resolved
            let external_info = resolved.external_info().copied();

            self.method_resolutions.insert(expr.id, resolved);

            // Record class method monomorphization for generic classes/records
            self.record_class_method_monomorph(
                expr,
                object_type_id,
                method_call.method,
                &func_type,
                external_info,
                interner,
            );

            // Compute and store substituted return type for generic class methods
            // so codegen doesn't need to recompute
            let final_return_id = {
                // Check if this is a generic class/record with type args that need substitution
                let type_args_and_def = {
                    let arena = self.type_arena();
                    arena
                        .unwrap_class(object_type_id)
                        .or_else(|| arena.unwrap_record(object_type_id))
                        .map(|(id, args)| (id, args.clone()))
                };
                if let Some((type_def_id, type_args)) = type_args_and_def
                    && !type_args.is_empty()
                {
                    let generic_info = {
                        let registry = self.entity_registry();
                        registry.get_type(type_def_id).generic_info.clone()
                    };
                    if let Some(ref generic_info) = generic_info {
                        // Build substitution map: T -> i32, etc.
                        let subs: FxHashMap<_, _> = generic_info
                            .type_params
                            .iter()
                            .zip(type_args.iter())
                            .map(|(param, &arg)| (param.name_id, arg))
                            .collect();
                        let substituted = self
                            .type_arena_mut()
                            .substitute(func_type.return_type_id, &subs);
                        if substituted != func_type.return_type_id {
                            self.substituted_return_types.insert(expr.id, substituted);
                        }
                        return Ok(substituted);
                    }
                }
                func_type.return_type_id
            };

            return Ok(final_return_id);
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
                if self.get_variable_type_id(*type_sym).is_some() {
                    return None;
                }
                let type_name_str = interner.resolve(*type_sym).to_string();
                // Use resolve_type_or_interface to also find prelude classes like Map/Set
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type_or_interface(*type_sym, &self.entity_registry())?;
                tracing::trace!(type_name = %type_name_str, ?type_def_id, "resolved static call target (identifier)");
                Some((type_def_id, type_name_str))
            }
            // Primitive type keywords: i32.default_value(), bool.default_value()
            ExprKind::TypeLiteral(type_expr) => {
                use vole_frontend::ast::TypeExpr;
                if let TypeExpr::Primitive(prim) = type_expr {
                    let name_id = self.name_table().primitives.from_ast(*prim);
                    let type_def_id = self.entity_registry().type_by_name(name_id)?;
                    let type_name = self.name_table().display(name_id);
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
        let maybe_method_id = {
            let registry = self.entity_registry();
            registry.find_static_method_on_type(type_def_id, method_name_id)
        };
        if let Some(method_id) = maybe_method_id {
            let (method_type_params, signature_id) = {
                let registry = self.entity_registry();
                let method_def = registry.get_method(method_id);
                (
                    method_def.method_type_params.clone(),
                    method_def.signature_id,
                )
            };

            // Get signature components from arena
            let (param_type_ids, return_type_id, _is_closure) = {
                let arena = self.type_arena();
                let (params, ret, is_closure) = arena
                    .unwrap_function(signature_id)
                    .expect("method signature must be a function type");
                (params.to_vec(), ret, is_closure)
            };

            // Check argument count
            if args.len() != param_type_ids.len() {
                self.add_wrong_arg_count(param_type_ids.len(), args.len(), expr.span);
            }

            // Get type params from the generic class/record definition
            let generic_info = {
                let registry = self.entity_registry();
                let type_def = registry.get_type(type_def_id);
                type_def.generic_info.clone()
            };

            // First pass: type-check arguments to get their types (as TypeId)
            let mut arg_type_ids = Vec::new();
            for arg in args {
                let arg_ty_id = self.check_expr(arg, interner)?;
                arg_type_ids.push(arg_ty_id);
            }

            // Get class-level type params (if any)
            let class_type_params: Vec<TypeParamInfo> = generic_info
                .as_ref()
                .map(|info| info.type_params.clone())
                .unwrap_or_default();

            // Combine class and method type params for inference
            let all_type_params = merge_type_params(&class_type_params, &method_type_params);

            // Infer type params if there are any (class-level or method-level)
            let (final_param_ids, final_return_id, maybe_inferred) = if !all_type_params.is_empty()
            {
                // Build substitution map from explicit type args if provided (TypeId version)
                let inferred: HashMap<NameId, ArenaTypeId> = if !explicit_type_args.is_empty() {
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
                    let mut explicit_map = HashMap::new();
                    for (param, type_expr) in
                        class_type_params.iter().zip(explicit_type_args.iter())
                    {
                        let resolved_id = self.resolve_type_id(type_expr, interner);
                        explicit_map.insert(param.name_id, resolved_id);
                    }
                    explicit_map
                } else {
                    // Infer type params from argument types (TypeId version)
                    self.infer_type_params_id(&all_type_params, &param_type_ids, &arg_type_ids)
                };

                // Substitute inferred types into param types and return type using arena
                let (substituted_param_ids, substituted_return_id) = {
                    let mut arena = self.type_arena_mut();
                    // Convert to FxHashMap for arena.substitute()
                    let inferred_hb: FxHashMap<NameId, ArenaTypeId> =
                        inferred.iter().map(|(&k, &v)| (k, v)).collect();
                    let params: Vec<ArenaTypeId> = param_type_ids
                        .iter()
                        .map(|&p| arena.substitute(p, &inferred_hb))
                        .collect();
                    let ret = arena.substitute(return_type_id, &inferred_hb);
                    (params, ret)
                };

                // Check type parameter constraints for class type params (TypeId version)
                if !class_type_params.is_empty() {
                    self.check_type_param_constraints_id(
                        &class_type_params,
                        &inferred,
                        expr.span,
                        interner,
                    );
                }

                // Check type parameter constraints for method type params (TypeId version)
                if !method_type_params.is_empty() {
                    self.check_type_param_constraints_id(
                        &method_type_params,
                        &inferred,
                        expr.span,
                        interner,
                    );
                }

                (substituted_param_ids, substituted_return_id, Some(inferred))
            } else {
                (param_type_ids, return_type_id, None)
            };

            // Second pass: check argument types against (potentially substituted) param types
            for (arg, (&arg_ty_id, &param_ty_id)) in args
                .iter()
                .zip(arg_type_ids.iter().zip(final_param_ids.iter()))
            {
                if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                    self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
                }
            }

            // Record resolution for codegen
            // Keep local func_type for record_static_method_monomorph below
            let func_type = FunctionType {
                is_closure: false,
                params_id: final_param_ids.into(),
                return_type_id: final_return_id,
            };
            self.method_resolutions.insert(
                expr.id,
                ResolvedMethod::Static {
                    type_def_id,
                    method_id,
                    func_type_id: signature_id,
                },
            );

            // Record substituted return type if generic substitution occurred
            if maybe_inferred.is_some() && final_return_id != return_type_id {
                self.substituted_return_types
                    .insert(expr.id, final_return_id);
            }

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
        object_type_id: ArenaTypeId,
        method_sym: Symbol,
        func_type: &FunctionType,
        external_info: Option<ExternalMethodInfo>,
        interner: &Interner,
    ) {
        // Extract type_def_id and type_args_id using arena queries
        // Note: We only record monomorphs for concrete types (Class/Record) that have
        // method bodies to compile. Interface types use vtable dispatch and don't need monomorphs.
        tracing::debug!(object_type_id = ?object_type_id, "record_class_method_monomorph called");
        let generic_info = {
            let arena = self.type_arena();
            if let Some((id, args)) = arena.unwrap_class(object_type_id) {
                if args.is_empty() {
                    None
                } else {
                    Some((id, args.clone()))
                }
            } else if let Some((id, args)) = arena.unwrap_record(object_type_id) {
                if args.is_empty() {
                    None
                } else {
                    Some((id, args.clone()))
                }
            } else {
                None
            }
        };
        let Some((class_type_def_id, type_args_id)) = generic_info else {
            tracing::debug!("returning early - not a generic class/record");
            return;
        };

        let class_name_id = self.entity_registry().get_type(class_type_def_id).name_id;
        tracing::debug!(
            class_name_id = ?class_name_id,
            type_args_id = ?type_args_id,
            "extracted generic type info"
        );

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Use TypeIds directly as keys
        let type_keys: Vec<_> = type_args_id.iter().copied().collect();

        // Create the monomorph key
        let key = ClassMethodMonomorphKey::new(class_name_id, method_name_id, type_keys);

        // Create/cache the monomorph instance
        if !self
            .entity_registry_mut()
            .class_method_monomorph_cache
            .contains(&key)
        {
            // Get the generic type definition for substitution info
            let generic_info = {
                let registry = self.entity_registry();
                registry.get_type(class_type_def_id).generic_info.clone()
            };
            let substitutions = if let Some(generic_info) = &generic_info {
                let mut subs = HashMap::new();
                for (param, &arg_id) in generic_info.type_params.iter().zip(type_args_id.iter()) {
                    subs.insert(param.name_id, arg_id);
                }
                subs
            } else {
                HashMap::new()
            };

            // Generate unique mangled name
            let instance_id = self
                .entity_registry_mut()
                .class_method_monomorph_cache
                .next_unique_id();
            let class_name = self
                .name_table()
                .last_segment_str(class_name_id)
                .unwrap_or_else(|| "class".to_string());
            let method_name = interner.resolve(method_sym);
            let mangled_name_str = format!(
                "{}__method_{}__mono_{}",
                class_name, method_name, instance_id
            );
            let mangled_name = self
                .name_table_mut()
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
            self.entity_registry_mut()
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
        inferred: &HashMap<NameId, ArenaTypeId>,
        interner: &Interner,
    ) {
        // Get the type def to extract name and type args
        let class_name_id = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).name_id
        };

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Use TypeIds directly as keys for class type params
        let class_type_keys: Vec<_> = class_type_params
            .iter()
            .filter_map(|tp| inferred.get(&tp.name_id).copied())
            .collect();

        // Use TypeIds directly as keys for method type params
        let method_type_keys: Vec<_> = method_type_params
            .iter()
            .filter_map(|tp| inferred.get(&tp.name_id).copied())
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
            .entity_registry_mut()
            .static_method_monomorph_cache
            .contains(&key)
        {
            // Generate unique mangled name
            let instance_id = self
                .entity_registry_mut()
                .static_method_monomorph_cache
                .next_unique_id();
            let class_name = self
                .name_table()
                .last_segment_str(class_name_id)
                .unwrap_or_else(|| "class".to_string());
            let method_name = interner.resolve(method_sym);
            let mangled_name_str = format!(
                "{}__static_{}__mono_{}",
                class_name, method_name, instance_id
            );
            let mangled_name = self
                .name_table_mut()
                .intern_raw(self.current_module, &[&mangled_name_str]);

            // Get param TypeIds from func_type
            let param_type_ids: Vec<ArenaTypeId> = func_type.params_id.iter().copied().collect();
            let return_type_id: ArenaTypeId = func_type.return_type_id;

            // Create the substituted function type using arena substitution (TypeId-based)
            let inferred_hb: FxHashMap<NameId, ArenaTypeId> =
                inferred.iter().map(|(&k, &v)| (k, v)).collect();
            let (subst_param_ids, subst_return_id) = {
                let mut arena = self.type_arena_mut();
                let params: Vec<ArenaTypeId> = param_type_ids
                    .iter()
                    .map(|&p| arena.substitute(p, &inferred_hb))
                    .collect();
                let ret = arena.substitute(return_type_id, &inferred_hb);
                (params, ret)
            };

            // Build substituted FunctionType from TypeIds
            let substituted_func_type =
                FunctionType::from_ids(&subst_param_ids, subst_return_id, func_type.is_closure);

            // Convert back to std::collections::HashMap for storage
            let substitutions: HashMap<NameId, ArenaTypeId> =
                inferred_hb.iter().map(|(&k, &v)| (k, v)).collect();

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
            self.entity_registry_mut()
                .static_method_monomorph_cache
                .insert(key.clone(), instance);
        }

        // Record the call site → key mapping
        tracing::debug!(expr_id = ?expr.id, key = ?key, "recording static method call site");
        self.static_method_calls.insert(expr.id, key);
    }
}
