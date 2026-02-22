use super::super::methods::GenericContext;
use super::super::methods::call_args::NamedArgContext;
use super::super::*;
use super::call::resolve_intrinsic_key_from_mappings;
use crate::generic::{TypeParamInfo, merge_type_params};
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::{FxHashMap, FxHashSet};
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
        let generic_info = self.entity_registry().type_generic_info(type_def_id)?;

        // Find the field by name and get substituted type
        let field_idx = generic_info.field_index_by_name(field_name, &self.name_table());
        if let Some(idx) = field_idx {
            let field_type_id = generic_info.field_types[idx];

            // Independent borrows via per-field RefCells - no unsafe needed
            let mut entities = self.entity_registry_mut();
            let mut types = self.type_arena_mut();
            let substituted_id = entities.substitute_type_id_with_args(
                type_def_id,
                type_args_id,
                field_type_id,
                &mut types,
            );
            return Some(substituted_id);
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
                let export_type_id = self
                    .module_name_id(module_id, field_name)
                    .and_then(|name_id| module.export_type(name_id));
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
                .unwrap_class_or_struct(object_type_id)
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
        expr_id: NodeId,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let object_type_id = self.check_expr(&opt_chain.object, interner)?;

        // Handle errors early
        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // The object must be an optional type (union with nil)
        // Check via arena if it's optional and unwrap (handles T | nil and A | B | nil)
        let inner_type_id = if let Some(inner_id) = self.unwrap_optional_non_nil_id(object_type_id)
        {
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
                .unwrap_class_or_struct(inner_type_id)
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
            // But if field type is already optional (contains nil), don't double-wrap
            let result_type_id = if self.is_optional_id(field_type_id) {
                field_type_id
            } else {
                self.ty_optional_id(field_type_id)
            };

            // Store compact codegen-ready info (no synthetic AST or fresh NodeIds)
            self.results.node_map.set_optional_chain(
                expr_id,
                crate::node_map::OptionalChainInfo {
                    object_type: object_type_id,
                    inner_type: inner_type_id,
                    result_type: field_type_id,
                    kind: crate::node_map::OptionalChainKind::FieldAccess {
                        field: opt_chain.field,
                    },
                },
            );

            Ok(result_type_id)
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

    pub(super) fn check_optional_method_call_expr(
        &mut self,
        omc: &OptionalMethodCallExpr,
        expr_id: NodeId,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let object_type_id = self.check_expr(&omc.object, interner)?;

        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Unwrap optional to get inner type
        let inner_type_id = if let Some(inner_id) = self.unwrap_optional_non_nil_id(object_type_id)
        {
            inner_id
        } else {
            object_type_id
        };

        if inner_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Build a minimal MethodCallExpr for type resolution. The object
        // expression is a placeholder — only the method/args/type_args matter.
        let synthetic_mc = MethodCallExpr {
            object: Expr {
                id: expr_id,
                kind: ExprKind::Identifier(interner.lookup("$oc").expect("$oc must be interned")),
                span: omc.method_span,
            },
            method: omc.method,
            type_args: omc.type_args.clone(),
            args: omc.args.clone(),
            method_span: omc.method_span,
        };

        // Resolve the method on the inner (unwrapped) type.
        // Method resolution is stored on expr_id (the OptionalMethodCallExpr node).
        let method_return_type_id =
            self.resolve_optional_method(expr_id, &synthetic_mc, inner_type_id, interner)?;

        // Wrap return type in optional (T -> T?)
        let result_type_id = if self.is_optional_id(method_return_type_id) {
            method_return_type_id
        } else {
            self.ty_optional_id(method_return_type_id)
        };

        // Store compact codegen-ready info (no synthetic AST or fresh NodeIds)
        self.results.node_map.set_optional_chain(
            expr_id,
            crate::node_map::OptionalChainInfo {
                object_type: object_type_id,
                inner_type: inner_type_id,
                result_type: method_return_type_id,
                kind: crate::node_map::OptionalChainKind::MethodCall,
            },
        );

        Ok(result_type_id)
    }

    /// Resolve and type-check a method call on the inner (unwrapped) type of an
    /// optional method call. This mirrors the instance-method path from
    /// `check_method_call_expr` but operates on a pre-resolved object type.
    ///
    /// `resolution_id` is the NodeId where method resolution and coercion info
    /// will be stored (the original OptionalMethodCallExpr's NodeId).
    fn resolve_optional_method(
        &mut self,
        resolution_id: NodeId,
        method_call: &MethodCallExpr,
        inner_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let method_name = interner.resolve(method_call.method);
        let span = method_call.method_span;

        // Try structural type methods
        let structural_opt = self.type_arena().unwrap_structural(inner_type_id).cloned();
        if let Some(structural) = structural_opt {
            for method in &structural.methods {
                let m_name = self.name_table().last_segment_str(method.name);
                if m_name.as_deref() == Some(method_name) {
                    if method_call.args.len() != method.params.len() {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: method.params.len(),
                                found: method_call.args.len(),
                                span: span.into(),
                            },
                            span,
                        );
                        for arg in &method_call.args {
                            self.check_expr(arg.expr(), interner)?;
                        }
                        return Ok(ArenaTypeId::INVALID);
                    }
                    for (arg, &param_type) in method_call.args.iter().zip(method.params.iter()) {
                        let expr = arg.expr();
                        let arg_type = self.check_expr(expr, interner)?;
                        if !self.types_compatible_id(arg_type, param_type, interner) {
                            self.add_type_mismatch_id(param_type, arg_type, expr.span);
                        }
                    }
                    let func_type =
                        FunctionType::from_ids(&method.params, method.return_type, false);
                    let return_type_id = func_type.return_type_id;
                    let func_type_id = func_type.intern(&mut self.type_arena_mut());
                    self.results.node_map.set_method(
                        resolution_id,
                        ResolvedMethod::Implemented {
                            type_def_id: None,
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
        }

        // Try entity registry resolution
        if let Some(resolved) =
            self.resolve_method_via_entity_registry_id(inner_type_id, method_call.method, interner)
        {
            if let Some(elem_type) = self.extract_custom_iterator_element_type_id(inner_type_id) {
                self.results.node_map.set_coercion_kind(
                    resolution_id,
                    crate::node_map::CoercionKind::IteratorWrap { elem_type },
                );
            }

            // Annotate method dispatch kind for codegen routing.
            let dispatch_kind = {
                let arena = self.type_arena();
                if arena.unwrap_array(inner_type_id).is_some() && method_name == "push" {
                    crate::node_map::MethodDispatchKind::ArrayPush
                } else if resolved.is_builtin() {
                    crate::node_map::MethodDispatchKind::Builtin
                } else {
                    crate::node_map::MethodDispatchKind::Standard
                }
            };
            self.results
                .node_map
                .set_method_dispatch_kind(resolution_id, dispatch_kind);

            // Build a synthetic Expr wrapper for process_resolved_instance_method
            // (it reads expr.id to store resolution and expr.span for diagnostics).
            let synthetic_expr = Expr {
                id: resolution_id,
                kind: ExprKind::MethodCall(Box::new(method_call.clone())),
                span,
            };
            return self.process_resolved_instance_method(
                &synthetic_expr,
                method_call,
                inner_type_id,
                resolved,
                interner,
            );
        }

        // Method not found
        let type_name = self.type_display_id(inner_type_id);
        let method_name_str = interner.resolve(method_call.method).to_string();
        if self.check_for_extension_method_visibility_error(
            inner_type_id,
            method_call.method,
            &type_name,
            &method_name_str,
            method_call.method_span,
            interner,
        ) {
            for arg in &method_call.args {
                self.check_expr(arg.expr(), interner)?;
            }
            return Ok(ArenaTypeId::INVALID);
        }

        self.add_error(
            SemanticError::UnknownMethod {
                ty: type_name,
                method: method_name_str,
                span: method_call.method_span.into(),
            },
            method_call.method_span,
        );
        for arg in &method_call.args {
            self.check_expr(arg.expr(), interner)?;
        }
        Ok(ArenaTypeId::INVALID)
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
            if let Some((type_def_id, _, _)) = arena.unwrap_class_or_struct(var_type_id) {
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
                self.check_expr(arg.expr(), interner)?;
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
                self.check_expr(arg.expr(), interner)?;
            }
            return Ok(self.ty_invalid_traced_id("method_on_union"));
        }

        // Handle module method calls (e.g., math.sqrt(16.0))
        if let Some(result) =
            self.check_module_method_call(expr, method_call, interner, object_type_id)?
        {
            return Ok(result);
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
                            self.check_expr(arg.expr(), interner)?;
                        }
                        return Ok(ArenaTypeId::INVALID);
                    }

                    // Check argument types
                    for (arg, &param_type) in method_call.args.iter().zip(method.params.iter()) {
                        let expr = arg.expr();
                        let arg_type = self.check_expr(expr, interner)?;
                        if !self.types_compatible_id(arg_type, param_type, interner) {
                            self.add_type_mismatch_id(param_type, arg_type, expr.span);
                        }
                    }

                    // Create FunctionType for resolution storage
                    let func_type =
                        FunctionType::from_ids(&method.params, method.return_type, false);
                    let return_type_id = func_type.return_type_id;
                    let func_type_id = func_type.intern(&mut self.type_arena_mut());

                    // Store resolution as a structural method call
                    // Use method.name as method_name_id for structural methods
                    self.results.node_map.set_method(
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
            // Annotate custom Iterator<T> receivers so codegen can box/wrap them
            // as RuntimeIterator without re-detecting the type.
            if let Some(elem_type) = self.extract_custom_iterator_element_type_id(object_type_id) {
                self.results.node_map.set_coercion_kind(
                    expr.id,
                    crate::node_map::CoercionKind::IteratorWrap { elem_type },
                );
            }

            // Annotate method dispatch kind so codegen can route without
            // re-detecting the receiver type via arena queries.
            // Note: RuntimeIterator dispatch is NOT annotated here; the
            // Iterator<T> → RuntimeIterator<T> conversion is a codegen concern.
            let dispatch_kind = {
                let arena = self.type_arena();
                if arena.unwrap_array(object_type_id).is_some() && method_name == "push" {
                    crate::node_map::MethodDispatchKind::ArrayPush
                } else if resolved.is_builtin() {
                    crate::node_map::MethodDispatchKind::Builtin
                } else {
                    crate::node_map::MethodDispatchKind::Standard
                }
            };
            self.results
                .node_map
                .set_method_dispatch_kind(expr.id, dispatch_kind);

            return self.process_resolved_instance_method(
                expr,
                method_call,
                object_type_id,
                resolved,
                interner,
            );
        }

        // Method not found — check if it's a file-scoped extension method from another module.
        // This produces a clearer error than a generic "unknown method" message.
        let method_name_str = interner.resolve(method_call.method).to_string();
        if self.check_for_extension_method_visibility_error(
            object_type_id,
            method_call.method,
            &type_name,
            &method_name_str,
            method_call.method_span,
            interner,
        ) {
            for arg in &method_call.args {
                self.check_expr(arg.expr(), interner)?;
            }
            return Ok(ArenaTypeId::INVALID);
        }

        // No method found - report error
        self.add_error(
            SemanticError::UnknownMethod {
                ty: type_name,
                method: method_name_str,
                span: method_call.method_span.into(),
            },
            method_call.method_span,
        );
        // Still check args for more errors
        for arg in &method_call.args {
            self.check_expr(arg.expr(), interner)?;
        }
        Ok(ArenaTypeId::INVALID)
    }

    /// Check if the failed method resolution was due to a file-scoped extension method.
    /// Returns true and emits `ExtensionMethodNotVisible` if the method exists but is
    /// defined in another module via `extend Type { }`. Returns false otherwise.
    fn check_for_extension_method_visibility_error(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: Symbol,
        type_name: &str,
        method_name_str: &str,
        method_span: Span,
        interner: &Interner,
    ) -> bool {
        // Only applies to nominal types with a TypeDefId
        let type_def_id = {
            let arena = self.type_arena();
            arena.unwrap_nominal(object_type_id).map(|(id, _, _)| id)
        };
        let Some(type_def_id) = type_def_id else {
            return false;
        };
        let method_name_id = self.method_name_id(method_name, interner);
        let not_visible = self.find_extension_method_not_visible(type_def_id, method_name_id);
        if !not_visible {
            return false;
        }
        // Use the short type name (last segment only) for clarity.
        // The full module path (from type_name) includes the source file path which is noisy.
        let short_type_name = {
            let name_id = self.entity_registry().name_id(type_def_id);
            self.name_table()
                .last_segment_str(name_id)
                .unwrap_or_else(|| type_name.to_string())
        };
        self.add_error(
            SemanticError::ExtensionMethodNotVisible {
                ty: short_type_name,
                method: method_name_str.to_string(),
                span: method_span.into(),
            },
            method_span,
        );
        true
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
                use vole_frontend::ast::TypeExprKind;
                if let TypeExprKind::Primitive(prim) = &type_expr.kind {
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
                let export_type_id = module_info.export_type(type_name_id)?;

                // Extract TypeDefId from the export type (class only)
                let arena = self.type_arena();
                let type_def_id = arena
                    .unwrap_class_or_struct(export_type_id)
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
            let (method_type_params, signature_id, required_params, method_param_names) = {
                let registry = self.entity_registry();
                let method_def = registry.get_method(method_id);
                (
                    method_def.method_type_params.clone(),
                    method_def.signature_id,
                    method_def.required_params,
                    method_def.param_names.clone(),
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
                let arg_ty_id = self.check_expr(arg.expr(), interner)?;
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

            // Validate named args if present (stores resolved_call_args mapping for codegen).
            // We do this before the second type-check pass so the mapping is available.
            let has_named_args = method_call
                .args
                .iter()
                .any(|a| matches!(a, CallArg::Named { .. }));
            if has_named_args {
                let named_ctx = NamedArgContext {
                    param_names: &method_param_names,
                    is_external: false, // Static methods are never external
                    call_node_id: expr.id,
                };
                // Use check_call_args_named_id which validates and stores the mapping.
                // Type errors from named-arg validation are collected as side effects.
                let _ = self.check_call_args_named_id(
                    &method_call.args,
                    &final_param_ids,
                    required_params,
                    final_return_id,
                    expr.span,
                    named_ctx,
                    interner,
                );
                // Skip the second pass since check_call_args_named_id already did type checking.
            } else {
                // Second pass: check argument types against (potentially substituted) param types
                for (arg, (&arg_ty_id, &param_ty_id)) in method_call
                    .args
                    .iter()
                    .zip(arg_type_ids.iter().zip(final_param_ids.iter()))
                {
                    if !self.types_compatible_id(arg_ty_id, param_ty_id, interner) {
                        self.add_type_mismatch_id(param_ty_id, arg_ty_id, arg.expr().span);
                    }
                }
            }

            // Record resolution for codegen
            // Keep local func_type for record_static_method_monomorph below
            let func_type = FunctionType {
                is_closure: false,
                params_id: final_param_ids.into(),
                return_type_id: final_return_id,
            };
            self.results.node_map.set_method(
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
                self.results
                    .node_map
                    .set_substituted_return_type(expr.id, final_return_id);
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
            self.check_expr(arg.expr(), interner)?;
        }

        Ok(ArenaTypeId::INVALID)
    }

    /// Handle module method calls (e.g., `math.sqrt(16.0)`).
    /// Returns `Some(return_type_id)` if the object is a module, `None` otherwise.
    fn check_module_method_call(
        &mut self,
        expr: &Expr,
        method_call: &MethodCallExpr,
        interner: &Interner,
        object_type_id: ArenaTypeId,
    ) -> Result<Option<ArenaTypeId>, Vec<TypeError>> {
        let module_info = {
            let arena = self.type_arena();
            arena.unwrap_module(object_type_id).map(|m| {
                let method_name_str = interner.resolve(method_call.method);
                let name_id = self.module_name_id(m.module_id, method_name_str);
                let export_type_id = name_id.and_then(|nid| m.export_type(nid));
                (
                    m.module_id,
                    method_name_str.to_string(),
                    name_id,
                    export_type_id,
                )
            })
        };
        let Some((module_id, method_name_str, name_id, export_type_id)) = module_info else {
            return Ok(None);
        };

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
            return Ok(Some(ArenaTypeId::INVALID));
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
            return Ok(Some(ArenaTypeId::INVALID));
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
            return Ok(Some(ArenaTypeId::INVALID));
        };

        // Check if this is a generic function (has TypeParams in signature)
        let has_type_params = {
            let arena = self.type_arena();
            param_ids
                .iter()
                .any(|&p| arena.unwrap_type_param(p).is_some())
                || arena.unwrap_type_param(return_id).is_some()
        };

        // Determine if the function is external and collect param names for named arg support.
        let is_external_fn = self
            .type_arena()
            .module_metadata(module_id)
            .is_some_and(|meta| meta.external_funcs.contains(&name_id));
        let func_param_names = {
            let fid = self.entity_registry().function_by_name(name_id);
            fid.map(|fid| self.entity_registry().get_function(fid).param_names.clone())
                .unwrap_or_default()
        };

        // For generic functions, infer type params and check arguments against concrete types
        let (concrete_param_ids, concrete_return_id) = if has_type_params {
            let generic_info = self
                .entity_registry()
                .function_by_name(name_id)
                .and_then(|fid| {
                    self.entity_registry()
                        .get_function(fid)
                        .generic_info
                        .clone()
                });

            if let Some(generic_def) = generic_info {
                self.specialize_generic_module_call(
                    expr,
                    method_call,
                    module_id,
                    name_id,
                    &generic_def,
                    interner,
                )?
            } else {
                let named_ctx = NamedArgContext {
                    param_names: &func_param_names,
                    is_external: is_external_fn,
                    call_node_id: expr.id,
                };
                self.check_call_args_named_id(
                    &method_call.args,
                    &param_ids,
                    param_ids.len(), // all required (no defaults for generic non-generic path)
                    return_id,
                    expr.span,
                    named_ctx,
                    interner,
                )?;
                (param_ids.to_vec(), return_id)
            }
        } else {
            let required_params_count = self
                .entity_registry()
                .function_by_name(name_id)
                .map(|fid| self.entity_registry().get_function(fid).required_params)
                .unwrap_or(param_ids.len());
            let named_ctx = NamedArgContext {
                param_names: &func_param_names,
                is_external: is_external_fn,
                call_node_id: expr.id,
            };
            self.check_call_args_named_id(
                &method_call.args,
                &param_ids,
                required_params_count,
                return_id,
                expr.span,
                named_ctx,
                interner,
            )?;
            (param_ids.to_vec(), return_id)
        };

        // Build FunctionType for resolution storage
        let func_type = FunctionType::from_ids(&concrete_param_ids, concrete_return_id, false);
        let func_type_id = func_type.intern(&mut self.type_arena_mut());

        let is_external = is_external_fn;

        let external_info = if is_external {
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

        self.results.node_map.set_method(
            expr.id,
            ResolvedMethod::Implemented {
                type_def_id: None,
                method_name_id: name_id,
                trait_name: None,
                func_type_id,
                return_type_id: concrete_return_id,
                is_builtin: false,
                external_info,
                concrete_return_hint: None,
            },
        );

        // Annotate dispatch kind so codegen can route without re-detecting module type.
        self.results.node_map.set_method_dispatch_kind(
            expr.id,
            crate::node_map::MethodDispatchKind::Module(module_id),
        );

        Ok(Some(concrete_return_id))
    }

    /// Specialize a generic module function call: infer type params, substitute,
    /// create monomorph instance, and record the generic call.
    fn specialize_generic_module_call(
        &mut self,
        expr: &Expr,
        method_call: &MethodCallExpr,
        module_id: ModuleId,
        name_id: NameId,
        generic_def: &GenericFuncInfo,
        interner: &Interner,
    ) -> Result<(Vec<ArenaTypeId>, ArenaTypeId), Vec<TypeError>> {
        let method_name_str = interner.resolve(method_call.method);
        let arg_type_ids: Vec<ArenaTypeId> = method_call
            .args
            .iter()
            .map(|arg| self.check_expr(arg.expr(), interner))
            .collect::<Result<Vec<_>, _>>()?;

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

        for (i, (arg, &expected_id)) in method_call
            .args
            .iter()
            .zip(concrete_params.iter())
            .enumerate()
        {
            let arg_ty_id = arg_type_ids[i];
            if !self.types_compatible_id(arg_ty_id, expected_id, interner) {
                self.add_type_mismatch_id(expected_id, arg_ty_id, arg.expr().span);
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
                .unwrap_or_else(|| method_name_str.to_string());
            let mangled_name = {
                let mut table = self.name_table_mut();
                let mut namer = Namer::new(&mut table, interner);
                namer.monomorph_str(module_id, &base_str, id)
            };
            let substitutions: FxHashMap<NameId, ArenaTypeId> = inferred_id.clone();
            let func_type = FunctionType::from_ids(&concrete_params, concrete_ret, false);
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

        self.results.node_map.set_generic(expr.id, key);

        // Resolve intrinsic key for constant folding.
        // If this is a generic external with compiler intrinsic mappings
        // (e.g., math.sqrt maps to "f64_sqrt"), record the concrete key
        // so the optimizer can fold calls with constant arguments.
        {
            let ext_info = self
                .implement_registry()
                .get_generic_external(method_name_str)
                .cloned();
            if let Some(ext_info) = ext_info {
                let sub_types: FxHashSet<ArenaTypeId> = inferred_id.values().copied().collect();
                if let Some(ikey) =
                    resolve_intrinsic_key_from_mappings(&ext_info.type_mappings, &sub_types)
                {
                    self.results.node_map.set_intrinsic_key(expr.id, ikey);
                }
            }
        }

        Ok((concrete_params, concrete_ret))
    }
}
