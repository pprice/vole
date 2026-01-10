// src/sema/analyzer/declarations.rs
//! Declaration signature collection (Pass 1 of semantic analysis).

use super::*;
use crate::frontend::ast::TypeExpr;
use crate::sema::entity_defs::TypeDefKind;

/// Extract the base interface name from a TypeExpr.
/// For `Iterator` returns `Iterator`, for `Iterator<i64>` returns `Iterator`.
fn interface_base_name(type_expr: &TypeExpr) -> Option<Symbol> {
    match type_expr {
        TypeExpr::Named(sym) => Some(*sym),
        TypeExpr::Generic { name, .. } => Some(*name),
        _ => None,
    }
}

/// Format a TypeExpr for error messages.
fn format_type_expr(type_expr: &TypeExpr, interner: &Interner) -> String {
    match type_expr {
        TypeExpr::Named(sym) => interner.resolve(*sym).to_string(),
        TypeExpr::Generic { name, args } => {
            let args_str: Vec<String> =
                args.iter().map(|a| format_type_expr(a, interner)).collect();
            format!("{}<{}>", interner.resolve(*name), args_str.join(", "))
        }
        _ => "unknown".to_string(),
    }
}

impl Analyzer {
    /// Pass 1: Collect signatures for functions, classes, records, interfaces, and implement blocks
    pub(super) fn collect_signatures(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.collect_function_signature(func, interner);
                }
                Decl::Tests(_) => {
                    // Tests don't need signatures in the first pass
                }
                Decl::Let(_) => {
                    // Let declarations are processed before the second pass
                }
                Decl::Class(class) => {
                    self.collect_class_signature(class, interner);
                }
                Decl::Record(record) => {
                    self.collect_record_signature(record, interner);
                }
                Decl::Interface(interface_decl) => {
                    self.collect_interface_def(interface_decl, interner);
                }
                Decl::Implement(impl_block) => {
                    self.collect_implement_block(impl_block, interner);
                }
                Decl::Error(decl) => {
                    self.analyze_error_decl(decl, interner);
                }
                Decl::External(ext_block) => {
                    // Register external functions as top-level functions
                    self.collect_external_block(ext_block, interner);
                }
            }
        }
    }

    fn collect_function_signature(&mut self, func: &FuncDecl, interner: &Interner) {
        let name_id = self
            .name_table
            .intern(self.current_module, &[func.name], interner);
        if func.type_params.is_empty() {
            // Non-generic function: resolve types normally
            let params: Vec<Type> = func
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty, interner))
                .collect();
            let return_type = func
                .return_type
                .as_ref()
                .map(|t| self.resolve_type(t, interner))
                .unwrap_or(Type::Void);

            let signature = FunctionType {
                params,
                return_type: Box::new(return_type),
                is_closure: false,
            };

            self.functions.insert(func.name, signature.clone());

            // Register in EntityRegistry (parallel migration)
            self.entity_registry.register_function(
                name_id,
                name_id, // For top-level functions, name_id == full_name_id
                self.current_module,
                signature,
            );
        } else {
            // Generic function: resolve with type params in scope
            let builtin_mod = self.name_table.builtin_module();
            let mut name_scope = TypeParamScope::new();
            for tp in &func.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
                name_scope.add(TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint: None,
                });
            }

            let type_params: Vec<TypeParamInfo> = func
                .type_params
                .iter()
                .map(|tp| {
                    let tp_name_str = interner.resolve(tp.name);
                    let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
                    let constraint = tp.constraint.as_ref().and_then(|c| {
                        self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                    });
                    TypeParamInfo {
                        name: tp.name,
                        name_id: tp_name_id,
                        constraint,
                    }
                })
                .collect();

            let mut type_param_scope = TypeParamScope::new();
            for info in &type_params {
                type_param_scope.add(info.clone());
            }

            // Resolve param types with type params in scope
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params(
                &self.type_aliases,
                &self.error_types,
                &self.entity_registry,
                interner,
                &mut self.name_table,
                module_id,
                &type_param_scope,
            );
            let param_types: Vec<Type> = func
                .params
                .iter()
                .map(|p| resolve_type(&p.ty, &mut ctx))
                .collect();
            let return_type = func
                .return_type
                .as_ref()
                .map(|t| resolve_type(t, &mut ctx))
                .unwrap_or(Type::Void);

            self.generic_functions.insert(
                func.name,
                GenericFuncDef {
                    type_params,
                    param_types,
                    return_type,
                },
            );
        }
    }

    fn collect_class_signature(&mut self, class: &ClassDecl, interner: &Interner) {
        let name_id = self
            .name_table
            .intern(self.current_module, &[class.name], interner);
        // Register in EntityRegistry (single source of truth)
        let entity_type_id =
            self.entity_registry
                .register_type(name_id, TypeDefKind::Class, self.current_module);

        // Register fields in EntityRegistry
        let builtin_module = self.name_table.builtin_module();
        for (i, field) in class.fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let field_name_id = self
                .name_table
                .intern_raw(builtin_module, &[field_name_str]);
            let full_field_name_id = self.name_table.intern_raw(
                self.current_module,
                &[interner.resolve(class.name), field_name_str],
            );
            let field_ty = self.resolve_type(&field.ty, interner);
            self.entity_registry.register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                field_ty,
                i,
            );
        }

        // Register in type_table for type resolution
        if let Some(class_type) = self
            .entity_registry
            .build_class_type(entity_type_id, &self.name_table)
        {
            self.register_named_type(class.name, Type::Class(class_type), interner);
        }

        // Register and validate implements list
        if !class.implements.is_empty() {
            let mut iface_names = Vec::new();
            for iface_type in &class.implements {
                if let Some(iface_sym) = interface_base_name(iface_type) {
                    // Validate interface exists via EntityRegistry
                    let iface_str = interner.resolve(iface_sym);
                    let iface_exists = self
                        .name_table
                        .name_id_raw(self.current_module, &[iface_str])
                        .and_then(|name_id| self.entity_registry.type_by_name(name_id))
                        .is_some()
                        || self
                            .entity_registry
                            .interface_by_short_name(iface_str, &self.name_table)
                            .is_some();

                    if !iface_exists {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: format_type_expr(iface_type, interner),
                                span: class.span.into(),
                            },
                            class.span,
                        );
                    }
                    iface_names.push(iface_sym);
                } else {
                    self.add_error(
                        SemanticError::UnknownInterface {
                            name: format_type_expr(iface_type, interner),
                            span: class.span.into(),
                        },
                        class.span,
                    );
                }
            }
            self.type_implements.insert(class.name, iface_names);
        }

        // Register methods in EntityRegistry (single source of truth)
        let builtin_module = self.name_table.builtin_module();
        for method in &class.methods {
            let method_name_str = interner.resolve(method.name);
            let method_name_id = self
                .name_table
                .intern_raw(builtin_module, &[method_name_str]);
            let full_method_name_id = self.name_table.intern_raw(
                self.current_module,
                &[interner.resolve(class.name), method_name_str],
            );
            let params: Vec<Type> = method
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty, interner))
                .collect();
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type(t, interner))
                .unwrap_or(Type::Void);
            let signature = FunctionType {
                params,
                return_type: Box::new(return_type),
                is_closure: false,
            };
            self.entity_registry.register_method(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature,
                false, // class methods don't have defaults
            );
        }
    }

    fn collect_record_signature(&mut self, record: &RecordDecl, interner: &Interner) {
        let name_id = self
            .name_table
            .intern(self.current_module, &[record.name], interner);

        // Handle generic records vs non-generic records
        if record.type_params.is_empty() {
            // Non-generic record: Register in EntityRegistry (single source of truth)
            let entity_type_id = self.entity_registry.register_type(
                name_id,
                TypeDefKind::Record,
                self.current_module,
            );

            // Register fields in EntityRegistry
            let builtin_module = self.name_table.builtin_module();
            for (i, field) in record.fields.iter().enumerate() {
                let field_name_str = interner.resolve(field.name);
                let field_name_id = self
                    .name_table
                    .intern_raw(builtin_module, &[field_name_str]);
                let full_field_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), field_name_str],
                );
                let field_ty = self.resolve_type(&field.ty, interner);
                self.entity_registry.register_field(
                    entity_type_id,
                    field_name_id,
                    full_field_name_id,
                    field_ty,
                    i,
                );
            }

            // Register in type_table for type resolution
            if let Some(record_type) = self
                .entity_registry
                .build_record_type(entity_type_id, &self.name_table)
            {
                self.register_named_type(record.name, Type::Record(record_type), interner);
            }

            // Register and validate implements list
            if !record.implements.is_empty() {
                let mut iface_names = Vec::new();
                for iface_type in &record.implements {
                    if let Some(iface_sym) = interface_base_name(iface_type) {
                        // Validate interface exists via EntityRegistry
                        let iface_str = interner.resolve(iface_sym);
                        let iface_exists = self
                            .name_table
                            .name_id_raw(self.current_module, &[iface_str])
                            .and_then(|name_id| self.entity_registry.type_by_name(name_id))
                            .is_some()
                            || self
                                .entity_registry
                                .interface_by_short_name(iface_str, &self.name_table)
                                .is_some();

                        if !iface_exists {
                            self.add_error(
                                SemanticError::UnknownInterface {
                                    name: format_type_expr(iface_type, interner),
                                    span: record.span.into(),
                                },
                                record.span,
                            );
                        }
                        iface_names.push(iface_sym);
                    } else {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: format_type_expr(iface_type, interner),
                                span: record.span.into(),
                            },
                            record.span,
                        );
                    }
                }
                self.type_implements.insert(record.name, iface_names);
            }

            // Register methods in EntityRegistry (single source of truth)
            let builtin_module = self.name_table.builtin_module();
            for method in &record.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self
                    .name_table
                    .intern_raw(builtin_module, &[method_name_str]);
                let full_method_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), method_name_str],
                );
                let params: Vec<Type> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type(&p.ty, interner))
                    .collect();
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type(t, interner))
                    .unwrap_or(Type::Void);
                let signature = FunctionType {
                    params,
                    return_type: Box::new(return_type),
                    is_closure: false,
                };
                self.entity_registry.register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    false,
                );
            }
        } else {
            // Generic record: store with type params as placeholders
            let builtin_mod = self.name_table.builtin_module();
            let mut name_scope = TypeParamScope::new();
            for tp in &record.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
                name_scope.add(TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint: None, // TODO: handle constraints
                });
            }

            let type_params: Vec<TypeParamInfo> = record
                .type_params
                .iter()
                .map(|tp| {
                    let tp_name_str = interner.resolve(tp.name);
                    let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
                    TypeParamInfo {
                        name: tp.name,
                        name_id: tp_name_id,
                        constraint: None,
                    }
                })
                .collect();

            let mut type_param_scope = TypeParamScope::new();
            for info in &type_params {
                type_param_scope.add(info.clone());
            }

            // Resolve field types with type params in scope
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params(
                &self.type_aliases,
                &self.error_types,
                &self.entity_registry,
                interner,
                &mut self.name_table,
                module_id,
                &type_param_scope,
            );

            let field_names: Vec<Symbol> = record.fields.iter().map(|f| f.name).collect();
            let field_types: Vec<Type> = record
                .fields
                .iter()
                .map(|f| resolve_type(&f.ty, &mut ctx))
                .collect();

            self.generic_records.insert(
                record.name,
                GenericRecordDef {
                    name_id,
                    type_params,
                    field_names,
                    field_types,
                },
            );

            // Also register in regular records with TypeParam placeholders
            // This allows struct literal checking to find the record definition
            let fields: Vec<StructField> = record
                .fields
                .iter()
                .enumerate()
                .map(|(i, f)| {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.type_aliases,
                        &self.error_types,
                        &self.entity_registry,
                        interner,
                        &mut self.name_table,
                        module_id,
                        &type_param_scope,
                    );
                    StructField {
                        name: interner.resolve(f.name).to_string(),
                        ty: resolve_type(&f.ty, &mut ctx),
                        slot: i,
                    }
                })
                .collect();
            let record_type = RecordType {
                name_id,
                fields,
                type_args: vec![], // Generic record base has no type args yet
            };
            self.register_named_type(record.name, Type::Record(record_type.clone()), interner);

            // Register and validate implements list (for generic records)
            if !record.implements.is_empty() {
                let mut iface_names = Vec::new();
                for iface_type in &record.implements {
                    if let Some(iface_sym) = interface_base_name(iface_type) {
                        // Validate interface exists via EntityRegistry
                        let iface_str = interner.resolve(iface_sym);
                        let iface_exists = self
                            .name_table
                            .name_id_raw(self.current_module, &[iface_str])
                            .and_then(|name_id| self.entity_registry.type_by_name(name_id))
                            .is_some()
                            || self
                                .entity_registry
                                .interface_by_short_name(iface_str, &self.name_table)
                                .is_some();

                        if !iface_exists {
                            self.add_error(
                                SemanticError::UnknownInterface {
                                    name: format_type_expr(iface_type, interner),
                                    span: record.span.into(),
                                },
                                record.span,
                            );
                        }
                        iface_names.push(iface_sym);
                    } else {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: format_type_expr(iface_type, interner),
                                span: record.span.into(),
                            },
                            record.span,
                        );
                    }
                }
                self.type_implements.insert(record.name, iface_names);
            }

            // Register methods in EntityRegistry (with type params in scope)
            // Note: The signature stored has type params as placeholders
            let builtin_module = self.name_table.builtin_module();
            // Get or create the type in EntityRegistry
            let entity_type_id = self
                .entity_registry
                .type_by_name(name_id)
                .unwrap_or_else(|| {
                    self.entity_registry.register_type(
                        name_id,
                        TypeDefKind::Record,
                        self.current_module,
                    )
                });

            for method in &record.methods {
                // First resolve types, then intern names (to avoid borrow conflicts)
                let params: Vec<Type> = {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.type_aliases,
                        &self.error_types,
                        &self.entity_registry,
                        interner,
                        &mut self.name_table,
                        module_id,
                        &type_param_scope,
                    );
                    ctx.self_type = Some(Type::Record(record_type.clone()));
                    method
                        .params
                        .iter()
                        .map(|p| resolve_type(&p.ty, &mut ctx))
                        .collect()
                };
                let return_type: Type = {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.type_aliases,
                        &self.error_types,
                        &self.entity_registry,
                        interner,
                        &mut self.name_table,
                        module_id,
                        &type_param_scope,
                    );
                    ctx.self_type = Some(Type::Record(record_type.clone()));
                    method
                        .return_type
                        .as_ref()
                        .map(|t| resolve_type(t, &mut ctx))
                        .unwrap_or(Type::Void)
                };

                let method_name_str = interner.resolve(method.name);
                let method_name_id = self
                    .name_table
                    .intern_raw(builtin_module, &[method_name_str]);
                let full_method_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), method_name_str],
                );
                let signature = FunctionType {
                    params,
                    return_type: Box::new(return_type),
                    is_closure: false,
                };
                self.entity_registry.register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    false,
                );
            }
        }
    }

    fn collect_interface_def(&mut self, interface_decl: &InterfaceDecl, interner: &Interner) {
        let builtin_mod = self.name_table.builtin_module();
        let mut name_scope = TypeParamScope::new();
        for tp in &interface_decl.type_params {
            let tp_name_str = interner.resolve(tp.name);
            let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
            name_scope.add(TypeParamInfo {
                name: tp.name,
                name_id: tp_name_id,
                constraint: None,
            });
        }

        let type_params: Vec<TypeParamInfo> = interface_decl
            .type_params
            .iter()
            .map(|tp| {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
                let constraint = tp.constraint.as_ref().and_then(|c| {
                    self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                });
                TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint,
                }
            })
            .collect();

        let mut type_param_scope = TypeParamScope::new();
        for info in &type_params {
            type_param_scope.add(info.clone());
        }

        let module_id = self.current_module;
        let mut type_ctx = TypeResolutionContext::with_type_params(
            &self.type_aliases,
            &self.error_types,
            &self.entity_registry,
            interner,
            &mut self.name_table,
            module_id,
            &type_param_scope,
        );

        // Resolve field types directly from AST (store for later registration)
        let resolved_fields: Vec<(Symbol, Type)> = interface_decl
            .fields
            .iter()
            .map(|f| (f.name, resolve_type(&f.ty, &mut type_ctx)))
            .collect();

        // Collect method names with default external bindings (from `default external` blocks)
        let default_external_methods: HashSet<Symbol> = interface_decl
            .external_blocks
            .iter()
            .filter(|ext| ext.is_default)
            .flat_map(|ext| ext.functions.iter().map(|f| f.vole_name))
            .collect();

        // Collect errors for methods with bodies that aren't marked as default
        let body_without_default_errors: Vec<_> = interface_decl
            .methods
            .iter()
            .filter(|m| {
                m.body.is_some() && !m.is_default && !default_external_methods.contains(&m.name)
            })
            .map(|m| (interner.resolve(m.name).to_string(), m.span))
            .collect();

        // Build interface_methods for Type and collect method data for EntityRegistry registration
        // We resolve types once and reuse the data
        let method_data: Vec<(Symbol, String, Vec<Type>, Type, bool)> = interface_decl
            .methods
            .iter()
            .map(|m| {
                let name = m.name;
                let name_str = interner.resolve(m.name).to_string();
                let params: Vec<Type> = m
                    .params
                    .iter()
                    .map(|p| resolve_type(&p.ty, &mut type_ctx))
                    .collect();
                let return_type = m
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type(t, &mut type_ctx))
                    .unwrap_or(Type::Void);
                let has_default =
                    m.is_default || m.body.is_some() || default_external_methods.contains(&m.name);
                (name, name_str, params, return_type, has_default)
            })
            .collect();

        let interface_methods: Vec<crate::sema::types::InterfaceMethodType> = method_data
            .iter()
            .map(|(name, _, params, return_type, has_default)| {
                crate::sema::types::InterfaceMethodType {
                    name: self.method_name_id(*name, interner),
                    params: params.clone(),
                    return_type: Box::new(return_type.clone()),
                    has_default: *has_default,
                }
            })
            .collect();

        // Emit errors for methods with bodies that aren't marked as default
        for (method_name, span) in body_without_default_errors {
            self.add_error(
                SemanticError::InterfaceMethodBodyWithoutDefault {
                    method: method_name,
                    span: span.into(),
                },
                span,
            );
        }

        // Collect method names for external block validation
        let method_names: HashSet<Symbol> = method_data.iter().map(|(name, ..)| *name).collect();

        let mut external_methods: HashMap<String, ExternalMethodInfo> = HashMap::new();
        for external in &interface_decl.external_blocks {
            for func in &external.functions {
                if !method_names.contains(&func.vole_name) {
                    let ty = interner.resolve(interface_decl.name).to_string();
                    let method = interner.resolve(func.vole_name).to_string();
                    self.add_error(
                        SemanticError::UnknownMethod {
                            ty,
                            method,
                            span: func.span.into(),
                        },
                        func.span,
                    );
                    continue;
                }
                let native_name = func
                    .native_name
                    .clone()
                    .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                let method_name_str = interner.resolve(func.vole_name).to_string();
                external_methods.insert(
                    method_name_str,
                    ExternalMethodInfo {
                        module_path: external.module_path.clone(),
                        native_name,
                    },
                );
            }
        }

        // Use current_module for proper module-qualified NameIds
        let name_str = interner.resolve(interface_decl.name).to_string();
        let name_id = self
            .name_table
            .intern_raw(self.current_module, &[&name_str]);

        // Register in EntityRegistry
        let entity_type_id = self.entity_registry.register_type(
            name_id,
            TypeDefKind::Interface,
            self.current_module,
        );

        // Set type parameters in EntityRegistry (using NameIds only)
        let entity_type_params: Vec<_> = type_params.iter().map(|tp| tp.name_id).collect();
        self.entity_registry
            .set_type_params(entity_type_id, entity_type_params);

        // Register extends relationships and build extends Vec<NameId>
        let extends_name_ids: Vec<NameId> = interface_decl
            .extends
            .iter()
            .map(|&parent_sym| {
                let parent_str = interner.resolve(parent_sym);
                let parent_name_id = self
                    .name_table
                    .intern_raw(self.current_module, &[parent_str]);
                if let Some(parent_type_id) = self.entity_registry.type_by_name(parent_name_id) {
                    self.entity_registry
                        .add_extends(entity_type_id, parent_type_id);
                }
                parent_name_id
            })
            .collect();

        // Register methods in EntityRegistry (with external bindings)
        for (_, method_name_str, params, return_type, has_default) in &method_data {
            let builtin_module = self.name_table.builtin_module();
            let method_name_id = self
                .name_table
                .intern_raw(builtin_module, &[method_name_str]);
            let full_method_name_id = self
                .name_table
                .intern_raw(self.current_module, &[&name_str, method_name_str]);
            let signature = FunctionType {
                params: params.clone(),
                return_type: Box::new(return_type.clone()),
                is_closure: false,
            };
            // Look up external binding for this method
            let external_binding = external_methods.get(method_name_str).cloned();
            self.entity_registry.register_method_with_binding(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature,
                *has_default,
                external_binding,
            );
        }

        // Register fields in EntityRegistry (for interface field requirements)
        for (i, (field_name, field_ty)) in resolved_fields.iter().enumerate() {
            let field_name_str = interner.resolve(*field_name).to_string();
            let builtin_module = self.name_table.builtin_module();
            let field_name_id = self
                .name_table
                .intern_raw(builtin_module, &[&field_name_str]);
            let full_field_name_id = self
                .name_table
                .intern_raw(self.current_module, &[&name_str, &field_name_str]);
            self.entity_registry.register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                field_ty.clone(),
                i,
            );
        }

        self.register_named_type(
            interface_decl.name,
            Type::Interface(crate::sema::types::InterfaceType {
                name_id,
                type_args: Vec::new(),
                methods: interface_methods,
                extends: extends_name_ids,
            }),
            interner,
        );
    }

    fn collect_implement_block(&mut self, impl_block: &ImplementBlock, interner: &Interner) {
        // Extract trait name symbol from trait_type (if present)
        let trait_name = impl_block.trait_type.as_ref().and_then(interface_base_name);

        // Validate trait exists if specified
        if let Some(ref trait_type) = impl_block.trait_type
            && let Some(name) = interface_base_name(trait_type)
        {
            // Validate interface exists via EntityRegistry
            let iface_str = interner.resolve(name);
            let iface_exists = self
                .name_table
                .name_id_raw(self.current_module, &[iface_str])
                .and_then(|name_id| self.entity_registry.type_by_name(name_id))
                .is_some()
                || self
                    .entity_registry
                    .interface_by_short_name(iface_str, &self.name_table)
                    .is_some();

            if !iface_exists {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(trait_type, interner),
                        span: impl_block.span.into(),
                    },
                    impl_block.span,
                );
            }
        }

        let target_type = self.resolve_type(&impl_block.target_type, interner);

        // Validate target type exists
        if matches!(target_type, Type::Error) {
            let type_name = match &impl_block.target_type {
                TypeExpr::Named(sym) => interner.resolve(*sym).to_string(),
                _ => "unknown".to_string(),
            };
            self.add_error(
                SemanticError::UnknownImplementType {
                    name: type_name,
                    span: impl_block.span.into(),
                },
                impl_block.span,
            );
        }

        if let Some(type_id) = TypeId::from_type(&target_type, &self.type_table) {
            for method in &impl_block.methods {
                let func_type = FunctionType {
                    params: method
                        .params
                        .iter()
                        .map(|p| self.resolve_type(&p.ty, interner))
                        .collect(),
                    return_type: Box::new(
                        method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type(t, interner))
                            .unwrap_or(Type::Void),
                    ),
                    is_closure: false,
                };

                let method_id = self.method_name_id(method.name, interner);
                self.implement_registry.register_method(
                    type_id,
                    method_id,
                    MethodImpl {
                        trait_name,
                        func_type,
                        is_builtin: false,
                        external_info: None,
                    },
                );
            }

            // Analyze external block if present
            if let Some(ref external) = impl_block.external {
                self.analyze_external_block(external, &target_type, trait_name, interner);
            }
        }
    }

    /// Register external block functions as top-level functions
    /// This is called for standalone external blocks (not inside implement blocks)
    fn collect_external_block(&mut self, ext_block: &ExternalBlock, interner: &Interner) {
        for func in &ext_block.functions {
            let params: Vec<Type> = func
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty, interner))
                .collect();
            let return_type = func
                .return_type
                .as_ref()
                .map(|t| self.resolve_type(t, interner))
                .unwrap_or(Type::Void);

            let func_type = FunctionType {
                params,
                return_type: Box::new(return_type),
                is_closure: false,
            };

            // Register the function with its Vole name (Symbol)
            self.functions.insert(func.vole_name, func_type.clone());

            // Also register by string name for cross-interner lookups (prelude functions)
            let name_str = interner.resolve(func.vole_name).to_string();
            self.functions_by_name.insert(name_str.clone(), func_type);

            // Store the external info (module path and native name) for codegen
            let native_name = func.native_name.clone().unwrap_or_else(|| name_str.clone());
            self.external_func_info.insert(
                name_str,
                ExternalMethodInfo {
                    module_path: ext_block.module_path.clone(),
                    native_name,
                },
            );
        }
    }
}
