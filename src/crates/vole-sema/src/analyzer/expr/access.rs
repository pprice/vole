use super::super::*;
use crate::generic::{
    ClassMethodMonomorphInstance, ClassMethodMonomorphKey, StaticMethodMonomorphInstance,
    StaticMethodMonomorphKey, TypeParamInfo, merge_type_params,
};
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
use vole_identity::{NameId, TypeDefId};

/// Generic context for recording method monomorphizations.
struct GenericContext<'a> {
    class_type_params: &'a [TypeParamInfo],
    method_type_params: &'a [TypeParamInfo],

    inferred: &'a FxHashMap<NameId, ArenaTypeId>,
}
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
        let generic_info = self.entity_registry().type_generic_info(type_def_id)?;

        // Find the field by name and get substituted type
        for (i, field_name_id) in generic_info.field_names.iter().enumerate() {
            let name = self.name_table().last_segment_str(*field_name_id);
            if name.as_deref() == Some(field_name) {
                let field_type_id = generic_info.field_types[i];

                // Use arena-based substitution - get raw pointer to arena to avoid borrow conflict
                // Rc::make_mut provides copy-on-write (free when refcount is 1)
                let mut db = self.ctx.db.borrow_mut();
                let arena = Rc::make_mut(&mut db.types) as *mut _;
                let substituted_id = Rc::make_mut(&mut db.entities).substitute_type_id_with_args(
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
            let Some(type_id) = export_type_id else {
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
            };
            return Ok(type_id);
        }

        // Handle Invalid type early - propagate
        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Get fields from object type (Class, Record, or Structural)
        let field_name = interner.resolve(field_access.field);

        // Check for structural type first (duck typing)
        let structural_opt = self.type_arena().unwrap_structural(object_type_id).cloned();
        if let Some(structural) = structural_opt {
            // Look up field in structural type's fields
            for (name_id, field_type_id) in &structural.fields {
                let name = self.name_table().last_segment_str(*name_id);
                if name.as_deref() == Some(field_name) {
                    return Ok(*field_type_id);
                }
            }
            // Field not found in structural type
            self.add_error(
                SemanticError::UnknownField {
                    ty: self.type_display_id(object_type_id),
                    field: field_name.to_string(),
                    span: field_access.field_span.into(),
                },
                field_access.field_span,
            );
            return Ok(self.ty_invalid_traced_id("structural_field_not_found"));
        }

        let struct_info = {
            let arena = self.type_arena();
            arena
                .unwrap_nominal(object_type_id)
                .filter(|(_, _, kind)| kind.is_class_or_struct())
                .map(|(id, args, kind)| (id, args.clone(), kind))
        };
        let Some((type_def_id, type_args_id, nominal_kind)) = struct_info else {
            self.type_error_id("class or struct", object_type_id, field_access.object.span);
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
        let kind_str = match nominal_kind {
            crate::type_arena::NominalKind::Class => "class",
            crate::type_arena::NominalKind::Struct => "struct",
            crate::type_arena::NominalKind::Interface => "interface",
            crate::type_arena::NominalKind::Error => "error type",
        };
        let context = format!(
            "field '{}' not found on {} '{}' (available: {})",
            field_name,
            kind_str,
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

        // Get type_def_id and type_args from inner type using arena queries (class only)
        let struct_info = {
            let arena = self.type_arena();
            arena
                .unwrap_nominal(inner_type_id)
                .filter(|(_, _, kind)| kind.is_class_or_struct())
                .map(|(id, args, _)| (id, args.clone()))
        };
        let Some((type_def_id, type_args_id)) = struct_info else {
            self.type_error_id(
                "optional class or struct",
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
            let name_id = self.entity_registry().name_id(type_def_id);
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
                method_call,
                interner,
            );
        }

        // Fallback: variables holding imported class/struct types can call static methods.
        // e.g., `let { Array } = import "std:array"; Array.filled<i64>(5, 0)`
        // resolve_static_call_target skips variables, so check here if the variable's
        // type has the requested static method before falling through to instance methods.
        if let ExprKind::Identifier(sym) = &method_call.object.kind
            && let Some(var_type_id) = self.get_variable_type_id(*sym)
        {
            let arena = self.type_arena();
            if let Some((type_def_id, _, kind)) = arena.unwrap_nominal(var_type_id)
                && kind.is_class_or_struct()
            {
                drop(arena);
                let method_name_id = self.method_name_id(method_call.method, interner);
                let has_static = self
                    .entity_registry()
                    .find_static_method_on_type(type_def_id, method_name_id)
                    .is_some();
                if has_static {
                    let type_name_str = interner.resolve(*sym).to_string();
                    return self.check_static_method_call(
                        expr,
                        type_def_id,
                        &type_name_str,
                        method_call,
                        interner,
                    );
                }
            }
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

            // Check if this is a generic function (has TypeParams in signature)
            let has_type_params = {
                let arena = self.type_arena();
                param_ids
                    .iter()
                    .any(|&p| arena.unwrap_type_param(p).is_some())
                    || arena.unwrap_type_param(return_id).is_some()
            };

            // For generic functions, infer type params and check arguments against concrete types
            let (concrete_param_ids, concrete_return_id) = if has_type_params {
                // Look up GenericFuncInfo from EntityRegistry
                let generic_info =
                    self.entity_registry()
                        .function_by_name(name_id)
                        .and_then(|fid| {
                            self.entity_registry()
                                .get_function(fid)
                                .generic_info
                                .clone()
                        });

                if let Some(generic_def) = generic_info {
                    // Type-check arguments to get their types
                    let arg_type_ids: Vec<ArenaTypeId> = method_call
                        .args
                        .iter()
                        .map(|arg| self.check_expr(arg, interner))
                        .collect::<Result<Vec<_>, _>>()?;

                    // Infer type parameters
                    let inferred_id = self.infer_type_params_id(
                        &generic_def.type_params,
                        &generic_def.param_types,
                        &arg_type_ids,
                    );
                    self.check_type_param_constraints_id(
                        &generic_def.type_params,
                        &inferred_id,
                        expr.span,
                        interner,
                    );

                    // Create concrete types by substitution
                    let subs: FxHashMap<_, _> = inferred_id.iter().map(|(&k, &v)| (k, v)).collect();
                    let (concrete_params, concrete_ret) = {
                        let mut arena = self.type_arena_mut();
                        let params: Vec<_> = generic_def
                            .param_types
                            .iter()
                            .map(|&t| arena.substitute(t, &subs))
                            .collect();
                        let ret = arena.substitute(generic_def.return_type, &subs);
                        (params, ret)
                    };

                    // Check arguments against concrete params
                    for (i, (arg, &expected_id)) in method_call
                        .args
                        .iter()
                        .zip(concrete_params.iter())
                        .enumerate()
                    {
                        let arg_ty_id = arg_type_ids[i];
                        if !self.types_compatible_id(arg_ty_id, expected_id, interner) {
                            self.add_type_mismatch_id(expected_id, arg_ty_id, arg.span);
                        }
                    }

                    // Create monomorph instance for codegen
                    let type_args_id: Vec<ArenaTypeId> = generic_def
                        .type_params
                        .iter()
                        .filter_map(|tp| inferred_id.get(&tp.name_id).copied())
                        .collect();
                    let type_keys: Vec<_> = type_args_id.to_vec();
                    let key = MonomorphKey::new(name_id, type_keys);

                    if !self.entity_registry_mut().monomorph_cache.contains(&key) {
                        let id = self.entity_registry_mut().monomorph_cache.next_unique_id();
                        let base_str = self
                            .name_table()
                            .last_segment_str(name_id)
                            .unwrap_or_else(|| method_name_str.clone());
                        let mangled_name = {
                            let mut table = self.name_table_mut();
                            let mut namer = Namer::new(&mut table, interner);
                            namer.monomorph_str(module_id, &base_str, id)
                        };
                        let substitutions: FxHashMap<NameId, ArenaTypeId> = inferred_id.clone();
                        let func_type =
                            FunctionType::from_ids(&concrete_params, concrete_ret, false);
                        self.entity_registry_mut().monomorph_cache.insert(
                            key.clone(),
                            MonomorphInstance {
                                original_name: name_id,
                                mangled_name,
                                instance_id: id,
                                func_type,
                                substitutions,
                            },
                        );
                    }

                    // Record the call -> monomorph key mapping for codegen
                    self.generic_calls.insert(expr.id, key);

                    (concrete_params, concrete_ret)
                } else {
                    // No generic info found - fall back to non-generic path
                    self.check_call_args_id(
                        &method_call.args,
                        &param_ids,
                        return_id,
                        expr.span,
                        interner,
                    )?;
                    (param_ids.to_vec(), return_id)
                }
            } else {
                // Non-generic function - check arguments directly
                self.check_call_args_id(
                    &method_call.args,
                    &param_ids,
                    return_id,
                    expr.span,
                    interner,
                )?;
                (param_ids.to_vec(), return_id)
            };

            // Build FunctionType for resolution storage (still needed for codegen)
            let func_type = FunctionType::from_ids(&concrete_param_ids, concrete_return_id, false);
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

            // For module method calls, use name_id as method_name_id
            self.method_resolutions.insert(
                expr.id,
                ResolvedMethod::Implemented {
                    type_def_id: None, // Module methods don't have a TypeDefId
                    method_name_id: name_id,
                    trait_name: None,
                    func_type_id,
                    return_type_id: concrete_return_id,
                    is_builtin: false,
                    external_info,
                    concrete_return_hint: None,
                },
            );

            return Ok(concrete_return_id);
        }

        // Handle structural type method calls (duck typing)
        let structural_opt = self.type_arena().unwrap_structural(object_type_id).cloned();
        if let Some(structural) = structural_opt {
            for method in &structural.methods {
                let m_name = self.name_table().last_segment_str(method.name);
                if m_name.as_deref() == Some(method_name) {
                    // Check argument count
                    if method_call.args.len() != method.params.len() {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: method.params.len(),
                                found: method_call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        for arg in &method_call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(ArenaTypeId::INVALID);
                    }

                    // Check argument types
                    for (arg, &param_type) in method_call.args.iter().zip(method.params.iter()) {
                        let arg_type = self.check_expr(arg, interner)?;
                        if !self.types_compatible_id(arg_type, param_type, interner) {
                            self.add_type_mismatch_id(param_type, arg_type, arg.span);
                        }
                    }

                    // Create FunctionType for resolution storage
                    let func_type =
                        FunctionType::from_ids(&method.params, method.return_type, false);
                    let return_type_id = func_type.return_type_id;
                    let func_type_id = func_type.intern(&mut self.type_arena_mut());

                    // Store resolution as a structural method call
                    // Use method.name as method_name_id for structural methods
                    self.method_resolutions.insert(
                        expr.id,
                        ResolvedMethod::Implemented {
                            type_def_id: None, // Structural methods don't have a TypeDefId
                            method_name_id: method.name,
                            trait_name: None,
                            func_type_id,
                            return_type_id,
                            is_builtin: false,
                            external_info: None,
                            concrete_return_hint: None,
                        },
                    );

                    return Ok(method.return_type);
                }
            }
            // Method not found in structural type - fall through to error
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
                        type_def_id,
                        method_name_id,
                        trait_name,
                        is_builtin,
                        external_info,
                        concrete_return_hint,
                        ..
                    } => {
                        let return_type_id = func_type.return_type_id;
                        let func_type_id = func_type.intern(&mut self.type_arena_mut());
                        ResolvedMethod::Implemented {
                            type_def_id,
                            method_name_id,
                            trait_name,
                            func_type_id,
                            return_type_id,
                            is_builtin,
                            external_info,
                            concrete_return_hint,
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

            // Look up required_params from method definition if available
            let required_params = if let Some(method_id) = resolved.method_id() {
                self.entity_registry().get_method(method_id).required_params
            } else {
                func_type.params_id.len()
            };
            let total_params = func_type.params_id.len();

            // Check argument count with defaults support
            let provided = method_call.args.len();
            if provided < required_params || provided > total_params {
                // For error message, show the range if defaults are present
                if required_params < total_params {
                    self.add_wrong_arg_count_range(
                        required_params,
                        total_params,
                        provided,
                        expr.span,
                    );
                } else {
                    self.add_wrong_arg_count(total_params, provided, expr.span);
                }
            }

            // Detect type-transforming iterator methods (map, flat_map).
            // These methods have signatures like `(T) -> T` but should support
            // type-changing lambdas `(T) -> U`, returning `Iterator<U>`.
            // We detect this case and infer the actual output type from the lambda.
            let is_map_transform = {
                let method_name_str = interner.resolve(method_call.method);
                let is_transform_method = method_name_str == "map" || method_name_str == "flat_map";
                let is_on_iterator = {
                    let arena = self.type_arena();
                    arena.unwrap_interface(object_type_id).is_some()
                        || arena.unwrap_runtime_iterator(object_type_id).is_some()
                };
                is_transform_method && is_on_iterator && !func_type.params_id.is_empty()
            };

            // For type-transforming iterator methods, we modify the expected type
            // so the lambda return type is inferred from its body rather than constrained.
            let mut map_inferred_return_type: Option<ArenaTypeId> = None;

            // Check argument types using TypeId directly
            for (arg, &param_ty_id) in method_call.args.iter().zip(func_type.params_id.iter()) {
                if is_map_transform {
                    // For map/flat_map on iterators, the param is a function type like (T) -> T.
                    // We want the lambda's parameter type to be inferred from T, but allow
                    // the return type to be freely inferred from the lambda body.
                    let modified_expected = {
                        let arena = self.type_arena();
                        arena.unwrap_function(param_ty_id).map(|(params, _ret, _)| {
                            // Create expected type with only parameter types (no return constraint)
                            // by using the params from the expected type but void as return
                            // This lets analyze_lambda infer param types but freely infer return type
                            params.to_vec()
                        })
                    };
                    if let Some(input_params) = modified_expected {
                        // Analyze lambda with only parameter type hints
                        let arg_ty_id = if let ExprKind::Lambda(lambda) = &arg.kind {
                            // Build expected with correct params but let return be inferred.
                            // INVALID signals to analyze_lambda to skip expected return type.
                            let param_only_expected = FunctionType {
                                is_closure: false,
                                params_id: input_params.into(),
                                return_type_id: ArenaTypeId::INVALID,
                            };
                            let lambda_ty_id =
                                self.analyze_lambda(lambda, Some(&param_only_expected), interner);
                            self.record_expr_type_id(arg, lambda_ty_id);
                            lambda_ty_id
                        } else {
                            self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?
                        };

                        // Extract the lambda's actual return type
                        let lambda_return = {
                            let arena = self.type_arena();
                            arena
                                .unwrap_function(arg_ty_id)
                                .map(|(_params, ret, _)| ret)
                        };
                        if let Some(ret_ty) = lambda_return {
                            map_inferred_return_type = Some(ret_ty);
                        }
                        // Don't emit type mismatch for the lambda - the return type is intentionally different
                    } else {
                        // Not a function parameter - check normally
                        let arg_ty_id =
                            self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?;
                        if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                            self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
                        }
                    }
                } else {
                    let arg_ty_id =
                        self.check_expr_expecting_id(arg, Some(param_ty_id), interner)?;
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.span);
                    }
                }
            }

            // Get external_info and return_type_id before moving resolved
            let external_info = resolved.external_info().copied();
            let resolved_return_id = if let Some(inferred_elem) = map_inferred_return_type {
                // For type-transforming iterator methods, override the return type.
                // map: Iterator<T> -> Iterator<U> where U is the lambda return type
                // flat_map: Iterator<T> -> Iterator<U> where U is the element type of [U]
                let method_name_str = interner.resolve(method_call.method);
                let new_elem_type = if method_name_str == "flat_map" {
                    // flat_map lambda returns [U], so unwrap the array to get U
                    self.type_arena()
                        .unwrap_array(inferred_elem)
                        .unwrap_or(inferred_elem)
                } else {
                    // map lambda returns U directly
                    inferred_elem
                };
                // Create Iterator<U> return type
                let iterator_interface_id = self
                    .resolver(interner)
                    .resolve_type_str_or_interface("Iterator", &self.entity_registry());
                if let Some(iface_id) = iterator_interface_id {
                    self.type_arena_mut()
                        .interface(iface_id, smallvec::smallvec![new_elem_type])
                } else {
                    resolved.return_type_id()
                }
            } else {
                resolved.return_type_id()
            };

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

            // Store the substituted return type for codegen so it doesn't need to recompute.
            // The resolved method already has the substituted return type in most cases
            // (InterfaceMethod, DefaultMethod), but we also handle class methods
            // where we need to compute the substitution.
            let final_return_id = {
                // Check if this is a generic class with type args that need substitution
                let type_args_and_def = {
                    let arena = self.type_arena();
                    arena
                        .unwrap_nominal(object_type_id)
                        .filter(|(_, _, kind)| kind.is_class_or_struct())
                        .map(|(id, args, _)| (id, args.clone()))
                };
                if let Some((type_def_id, type_args)) = type_args_and_def
                    && !type_args.is_empty()
                {
                    let generic_info = self.entity_registry().type_generic_info(type_def_id);
                    if let Some(generic_info) = generic_info {
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
                        self.substituted_return_types.insert(expr.id, substituted);
                        return Ok(substituted);
                    }
                }

                // For interface methods, the return type is already substituted in resolved.
                // Store it for codegen to use.
                self.substituted_return_types
                    .insert(expr.id, resolved_return_id);
                resolved_return_id
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
    /// Handles:
    /// - Named types: Point.create(), MyClass.static_method()
    /// - Primitive keywords: i32.default_value(), bool.default_value()
    /// - Module-qualified types: time.Duration.seconds(), math.Vector.zero()
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
            // Module-qualified types: time.Duration.seconds(), module.Type.method()
            // The object is a field access like `time.Duration` where `time` is a module
            // and `Duration` is a type exported from that module.
            ExprKind::FieldAccess(field_access) => {
                // The object of the field access should be a module variable
                let ExprKind::Identifier(module_sym) = &field_access.object.kind else {
                    return None;
                };

                // Get the module type from the variable
                let module_type_id = self.get_variable_type_id(*module_sym)?;

                // Check if this is a module type
                let module_info = self.type_arena().unwrap_module(module_type_id).cloned()?;

                // Look up the type in the module's exports
                let type_name_str = interner.resolve(field_access.field);
                let type_name_id = self.module_name_id(module_info.module_id, type_name_str)?;

                // Find the export and check if it's a Record or Class type
                let export_type_id = module_info
                    .exports
                    .iter()
                    .find(|(n, _)| *n == type_name_id)
                    .map(|&(_, type_id)| type_id)?;

                // Extract TypeDefId from the export type (class only)
                let arena = self.type_arena();
                let type_def_id = arena
                    .unwrap_nominal(export_type_id)
                    .filter(|(_, _, kind)| kind.is_class_or_struct())
                    .map(|(id, _, _)| id)?;

                tracing::trace!(
                    module = %interner.resolve(*module_sym),
                    type_name = %type_name_str,
                    ?type_def_id,
                    "resolved static call target (module-qualified)"
                );
                Some((type_def_id, type_name_str.to_string()))
            }
            _ => None,
        }
    }

    /// Check a static method call: TypeName.method(args) or TypeName.method<T, U>(args)
    fn check_static_method_call(
        &mut self,
        expr: &Expr,
        type_def_id: TypeDefId,
        type_name_str: &str,
        method_call: &MethodCallExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let method_name_str = interner.resolve(method_call.method);
        let method_name_id = self.method_name_id(method_call.method, interner);

        // Look up the static method on this type
        let maybe_method_id = self
            .entity_registry()
            .find_static_method_on_type(type_def_id, method_name_id);
        if let Some(method_id) = maybe_method_id {
            let (method_type_params, signature_id, required_params) = {
                let registry = self.entity_registry();
                let method_def = registry.get_method(method_id);
                (
                    method_def.method_type_params.clone(),
                    method_def.signature_id,
                    method_def.required_params,
                )
            };

            // Get signature components from arena
            // If signature is invalid (unknown type), return INVALID - error already reported
            let sig_result = {
                let arena = self.type_arena();
                arena
                    .unwrap_function(signature_id)
                    .map(|(params, ret, is_closure)| (params.to_vec(), ret, is_closure))
            };
            let Some((param_type_ids, return_type_id, _is_closure)) = sig_result else {
                return Ok(self.type_arena_mut().invalid());
            };

            // Check argument count with defaults support
            let total_params = param_type_ids.len();
            if method_call.args.len() < required_params || method_call.args.len() > total_params {
                self.add_wrong_arg_count_range(
                    required_params,
                    total_params,
                    method_call.args.len(),
                    expr.span,
                );
            }

            // Get type params from the generic class definition
            let generic_info = self.entity_registry().type_generic_info(type_def_id);

            // First pass: type-check arguments to get their types (as TypeId)
            let mut arg_type_ids = Vec::new();
            for arg in &method_call.args {
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
                let inferred: FxHashMap<NameId, ArenaTypeId> = if !method_call.type_args.is_empty()
                {
                    // Resolve explicit type args and map to class type params
                    if method_call.type_args.len() != class_type_params.len() {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: class_type_params.len(),
                                found: method_call.type_args.len(),
                                span: method_call.method_span.into(),
                            },
                            method_call.method_span,
                        );
                    }
                    let mut explicit_map = FxHashMap::default();
                    for (param, type_expr) in
                        class_type_params.iter().zip(method_call.type_args.iter())
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
            for (arg, (&arg_ty_id, &param_ty_id)) in method_call
                .args
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
                    method_name_id,
                    type_def_id,
                    method_id,
                    func_type_id: signature_id,
                    return_type_id: final_return_id,
                },
            );

            // Record substituted return type if generic substitution occurred
            if maybe_inferred.is_some() && final_return_id != return_type_id {
                self.substituted_return_types
                    .insert(expr.id, final_return_id);
            }

            // Record static method monomorphization whenever the call participates
            // in generic static-method analysis. Inference may legitimately produce
            // an empty map for class-independent static methods (e.g. helpers that
            // only use concrete parameter/return types), but codegen still needs a
            // monomorphized callable target for generic class static methods.
            if let Some(ref inferred) = maybe_inferred {
                self.record_static_method_monomorph(
                    expr,
                    type_def_id,
                    method_call.method,
                    &func_type,
                    &GenericContext {
                        class_type_params: &class_type_params,
                        method_type_params: &method_type_params,
                        inferred,
                    },
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

    /// Record a class method monomorphization for generic class method calls.
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
        // Note: We only record monomorphs for concrete types (Class) that have
        // method bodies to compile. Interface types use vtable dispatch and don't need monomorphs.
        tracing::debug!(object_type_id = ?object_type_id, "record_class_method_monomorph called");
        let generic_info = {
            let arena = self.type_arena();
            arena
                .unwrap_nominal(object_type_id)
                .filter(|(_, args, kind)| kind.is_class_or_struct() && !args.is_empty())
                .map(|(id, args, _)| (id, args.clone()))
        };
        let Some((class_type_def_id, type_args_id)) = generic_info else {
            tracing::debug!("returning early - not a generic class");
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
            let generic_info = self.entity_registry().type_generic_info(class_type_def_id);
            let substitutions = if let Some(generic_info) = &generic_info {
                let mut subs = FxHashMap::default();
                for (param, &arg_id) in generic_info.type_params.iter().zip(type_args_id.iter()) {
                    subs.insert(param.name_id, arg_id);
                }

                // Eagerly substitute all field types into the arena so that codegen's
                // read-only lookup_substitute can find them later. Without this,
                // compound field types like [Entry<K> | Empty] substituted to
                // [Entry<i64> | Empty] would never be created in the arena.
                if !subs.is_empty() {
                    let field_types = generic_info.field_types.clone();
                    let mut arena = self.type_arena_mut();
                    for field_type in field_types {
                        arena.substitute(field_type, &subs);
                    }
                }

                subs
            } else {
                FxHashMap::default()
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

            // Class method monomorphs must carry a concrete signature.
            // Leaving TypeParam-based signatures here can produce verifier
            // mismatches later when branch values are concrete (e.g. i32) but
            // block params are typed as generic storage words (i64).
            let substituted_func_type = if substitutions.is_empty() {
                func_type.clone()
            } else {
                let param_type_ids: Vec<ArenaTypeId> =
                    func_type.params_id.iter().copied().collect();
                let return_type_id: ArenaTypeId = func_type.return_type_id;
                let (subst_param_ids, subst_return_id) = {
                    let mut arena = self.type_arena_mut();
                    let params: Vec<ArenaTypeId> = param_type_ids
                        .iter()
                        .map(|&param_id| arena.substitute(param_id, &substitutions))
                        .collect();
                    let ret = arena.substitute(return_type_id, &substitutions);
                    (params, ret)
                };
                FunctionType::from_ids(&subst_param_ids, subst_return_id, func_type.is_closure)
            };

            let instance = ClassMethodMonomorphInstance {
                class_name: class_name_id,
                method_name: method_name_id,
                mangled_name,
                instance_id,
                func_type: substituted_func_type,
                substitutions,
                external_info,
                self_type: object_type_id,
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

    /// Record a static method monomorphization for generic class static method calls.
    fn record_static_method_monomorph(
        &mut self,
        expr: &Expr,
        type_def_id: TypeDefId,
        method_sym: Symbol,
        func_type: &FunctionType,
        generic_ctx: &GenericContext<'_>,
        interner: &Interner,
    ) {
        // Get the type def to extract name and type args
        let class_name_id = self.entity_registry().name_id(type_def_id);

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Use TypeIds directly as keys for class type params
        let class_type_keys: Vec<_> = generic_ctx
            .class_type_params
            .iter()
            .filter_map(|tp| generic_ctx.inferred.get(&tp.name_id).copied())
            .collect();

        // Use TypeIds directly as keys for method type params
        let method_type_keys: Vec<_> = generic_ctx
            .method_type_params
            .iter()
            .filter_map(|tp| generic_ctx.inferred.get(&tp.name_id).copied())
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
                generic_ctx.inferred.iter().map(|(&k, &v)| (k, v)).collect();

            // Eagerly substitute all field types into the arena so that codegen's
            // read-only lookup_substitute can find them later. Without this,
            // compound field types like [Entry<K> | Empty] substituted to
            // [Entry<i64> | Empty] would never be created in the arena.
            {
                let generic_info = self.entity_registry().type_generic_info(type_def_id);
                if let Some(generic_info) = generic_info {
                    let field_types = generic_info.field_types;
                    let mut arena = self.type_arena_mut();
                    for field_type in field_types {
                        arena.substitute(field_type, &inferred_hb);
                    }
                }
            }

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
            let substitutions: FxHashMap<NameId, ArenaTypeId> =
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
