// src/sema/analyzer/declarations.rs
//! Declaration signature collection (Pass 1 of semantic analysis).

use super::*;
use crate::entity_defs::{GenericFuncInfo, GenericTypeInfo, TypeDefKind};
use crate::type_arena::{TypeId as ArenaTypeId, TypeIdVec};
use vole_frontend::ast::{ExprKind, LetInit, TypeExpr};

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
    /// Register a type shell (name and kind only, no fields/methods yet).
    /// This enables forward references - types can reference each other regardless of declaration order.
    fn register_type_shell(
        &mut self,
        name: Symbol,
        kind: TypeDefKind,
        interner: &Interner,
    ) -> TypeDefId {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[name], interner);
        self.entity_registry_mut()
            .register_type(name_id, kind, self.current_module)
    }

    /// Pass 0.5: Register all type shells so forward references work.
    /// Must be called before collect_signatures.
    pub(super) fn register_all_type_shells(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Class(c) => {
                    self.register_type_shell(c.name, TypeDefKind::Class, interner);
                }
                Decl::Record(r) => {
                    self.register_type_shell(r.name, TypeDefKind::Record, interner);
                }
                Decl::Interface(i) => {
                    self.register_type_shell(i.name, TypeDefKind::Interface, interner);
                }
                Decl::Let(l) => {
                    // Handle both new syntax (let T = SomeType) and legacy (let T: type = SomeType)
                    let is_type_alias = match &l.init {
                        LetInit::TypeAlias(_) => true,
                        LetInit::Expr(expr) => {
                            matches!(expr.kind, ExprKind::TypeLiteral(_))
                        }
                    };
                    if is_type_alias {
                        self.register_type_shell(l.name, TypeDefKind::Alias, interner);
                    }
                }
                _ => {}
            }
        }
    }

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
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);
        if func.type_params.is_empty() {
            // Non-generic function: resolve types directly to TypeId
            let params_id: Vec<_> = func
                .params
                .iter()
                .map(|p| self.resolve_type_id(&p.ty, interner))
                .collect();
            let return_type_id = func
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_id(t, interner))
                .unwrap_or_else(|| self.type_arena().void());

            let signature = FunctionType::from_ids(&params_id, return_type_id, false);

            self.functions.insert(func.name, signature.clone());

            // Register in EntityRegistry
            self.entity_registry_mut().register_function(
                name_id,
                name_id, // For top-level functions, name_id == full_name_id
                self.current_module,
                signature,
            );
        } else {
            // Generic function: resolve with type params in scope
            let builtin_mod = self.name_table_mut().builtin_module();
            let mut name_scope = TypeParamScope::new();
            for tp in &func.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                name_scope.add(TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint: None,
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                });
            }

            let type_params: Vec<TypeParamInfo> = func
                .type_params
                .iter()
                .map(|tp| {
                    let tp_name_str = interner.resolve(tp.name);
                    let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                    let constraint = tp.constraint.as_ref().and_then(|c| {
                        self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                    });
                    TypeParamInfo {
                        name: tp.name,
                        name_id: tp_name_id,
                        constraint,
                        type_param_id: None,
                        variance: TypeParamVariance::default(),
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
                &self.db,
                interner,
                module_id,
                &type_param_scope,
            );
            // Resolve directly to TypeId
            let param_type_ids: Vec<ArenaTypeId> = func
                .params
                .iter()
                .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                .collect();
            let return_type_id = func
                .return_type
                .as_ref()
                .map(|t| resolve_type_to_id(t, &mut ctx))
                .unwrap_or_else(|| self.type_arena().void());

            // Create a FunctionType from TypeIds
            let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);

            // Register in EntityRegistry
            let func_id = self.entity_registry_mut().register_function(
                name_id,
                name_id, // For top-level functions, name_id == full_name_id
                self.current_module,
                signature,
            );
            self.entity_registry_mut().set_function_generic_info(
                func_id,
                GenericFuncInfo {
                    type_params,
                    param_types: param_type_ids,
                    return_type: return_type_id,
                },
            );
        }
    }

    fn collect_class_signature(&mut self, class: &ClassDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[class.name], interner);

        // Handle generic classes vs non-generic classes
        if class.type_params.is_empty() {
            // Non-generic class: lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry_mut()
                .type_by_name(name_id)
                .expect("class shell registered in register_all_type_shells");

            // Collect field info for generic_info (needed for struct literal checking)
            // Convert Symbol field names to NameId at registration time
            let builtin_mod = self.name_table_mut().builtin_module();
            let field_names: Vec<NameId> = class
                .fields
                .iter()
                .map(|f| {
                    let name_str = interner.resolve(f.name);
                    self.name_table_mut().intern_raw(builtin_mod, &[name_str])
                })
                .collect();
            // Resolve field types directly to TypeId
            let field_type_ids: Vec<ArenaTypeId> = class
                .fields
                .iter()
                .map(|f| self.resolve_type_id(&f.ty, interner))
                .collect();

            // Set generic_info (with empty type_params for non-generic classes)
            self.entity_registry_mut().set_generic_info(
                entity_type_id,
                GenericTypeInfo {
                    type_params: vec![],
                    field_names: field_names.clone(),
                    field_types: field_type_ids.clone(),
                },
            );

            // Register fields in EntityRegistry
            for (i, field) in class.fields.iter().enumerate() {
                let field_name_str = interner.resolve(field.name);
                let full_field_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), field_name_str],
                );
                self.entity_registry_mut().register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Register and validate implements list
            self.validate_and_register_implements(
                entity_type_id,
                &class.implements,
                class.span,
                interner,
            );

            // Register methods in EntityRegistry (single source of truth)
            // Use class TypeId as Self for resolving method signatures
            let self_type_id = self.type_arena_mut()
                .class(entity_type_id, TypeIdVec::new());
            let builtin_mod = self.name_table_mut().builtin_module();
            for method in &class.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), method_name_str],
                );
                let params_id: Vec<_> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type_id_with_self(&p.ty, interner, Some(self_type_id)))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id_with_self(t, interner, Some(self_type_id)))
                    .unwrap_or_else(|| self.type_arena().void());
                let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                    .intern(&mut self.type_arena_mut());
                self.entity_registry_mut().register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature_id,
                    false, // class methods don't have defaults
                );
            }

            // Register static methods in EntityRegistry
            if let Some(ref statics) = class.statics {
                let builtin_mod = self.name_table_mut().builtin_module();
                let class_name_str = interner.resolve(class.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);
                    let params_id: Vec<_> = method
                        .params
                        .iter()
                        .map(|p| self.resolve_type_id(&p.ty, interner))
                        .collect();
                    let return_type_id = method
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_id(t, interner))
                        .unwrap_or_else(|| self.type_arena().void());
                    let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                        .intern(&mut self.type_arena_mut());
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry_mut().register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        has_default,
                        Vec::new(), // Non-generic class, no method type params
                    );
                }
            }

            // Register external methods in EntityRegistry (non-generic class)
            if let Some(ref external) = class.external {
                let class_name_str = interner.resolve(class.name);
                for func in &external.functions {
                    let method_name_str = interner.resolve(func.vole_name);
                    let method_name_id =
                        self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);
                    let params_id: Vec<_> = func
                        .params
                        .iter()
                        .map(|p| self.resolve_type_id(&p.ty, interner))
                        .collect();
                    let return_type_id = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_id(t, interner))
                        .unwrap_or_else(|| self.type_arena().void());
                    let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                        .intern(&mut self.type_arena_mut());
                    let native_name_str = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| method_name_str.to_string());
                    let builtin_mod = self.name_table_mut().builtin_module();
                    self.entity_registry_mut().register_method_with_binding(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        false, // external methods don't have defaults
                        Some(ExternalMethodInfo {
                            module_path: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&external.module_path]),
                            native_name: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]),
                        }),
                    );
                }
            }
        } else {
            // Generic class: store with type params as placeholders
            let builtin_mod = self.name_table_mut().builtin_module();

            // First pass: create name_scope for constraint resolution (same pattern as functions)
            let mut name_scope = TypeParamScope::new();
            for tp in &class.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                name_scope.add(TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint: None,
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                });
            }

            // Second pass: resolve constraints with name_scope available
            let type_params: Vec<TypeParamInfo> = class
                .type_params
                .iter()
                .map(|tp| {
                    let tp_name_str = interner.resolve(tp.name);
                    let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                    let constraint = tp.constraint.as_ref().and_then(|c| {
                        self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                    });
                    TypeParamInfo {
                        name: tp.name,
                        name_id: tp_name_id,
                        constraint,
                        type_param_id: None,
                        variance: TypeParamVariance::default(),
                    }
                })
                .collect();

            let mut type_param_scope = TypeParamScope::new();
            for info in &type_params {
                type_param_scope.add(info.clone());
            }

            // Convert Symbol field names to NameId at registration time
            // (must be done before creating ctx which borrows name_table)
            let field_names: Vec<NameId> = class
                .fields
                .iter()
                .map(|f| {
                    let name_str = interner.resolve(f.name);
                    self.name_table_mut().intern_raw(builtin_mod, &[name_str])
                })
                .collect();

            // Resolve field types with type params in scope
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params(
                &self.db,
                interner,
                module_id,
                &type_param_scope,
            );

            // Resolve field types directly to TypeId
            let field_type_ids: Vec<ArenaTypeId> = class
                .fields
                .iter()
                .map(|f| resolve_type_to_id(&f.ty, &mut ctx))
                .collect();

            // Lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry_mut()
                .type_by_name(name_id)
                .expect("class shell registered in register_all_type_shells");

            // Set type params on the type definition (needed for method substitutions)
            let type_param_name_ids: Vec<NameId> =
                type_params.iter().map(|tp| tp.name_id).collect();
            self.entity_registry_mut()
                .set_type_params(entity_type_id, type_param_name_ids);

            // Set generic info for type inference during struct literal checking
            self.entity_registry_mut().set_generic_info(
                entity_type_id,
                GenericTypeInfo {
                    type_params,
                    field_names: field_names.clone(),
                    field_types: field_type_ids.clone(),
                },
            );

            // Register fields with placeholder types
            for (i, field) in class.fields.iter().enumerate() {
                let field_name_str = interner.resolve(field.name);
                let full_field_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), field_name_str],
                );
                // Use field_type_ids already computed above
                self.entity_registry_mut().register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Register and validate implements list (for generic classes)
            self.validate_and_register_implements(
                entity_type_id,
                &class.implements,
                class.span,
                interner,
            );

            // Register methods in EntityRegistry with type params in scope
            // Build self_type_id directly from entity_type_id with type param placeholders
            let type_arg_ids: Vec<ArenaTypeId> = type_param_scope
                .params()
                .iter()
                .map(|tp| self.type_arena_mut().type_param(tp.name_id))
                .collect();
            let self_type_id = self.type_arena_mut()
                .class(entity_type_id, type_arg_ids);
            for method in &class.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), method_name_str],
                );

                // Resolve parameter types with type params and self in scope
                let mut ctx = TypeResolutionContext {
                    db: &self.db,
                    interner,
                    module_id,
                    type_params: Some(&type_param_scope),
                    self_type: Some(self_type_id),
                };
                let params_id: Vec<ArenaTypeId> = method
                    .params
                    .iter()
                    .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                    .collect();

                // Resolve return type with type params and self in scope
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type_to_id(t, &mut ctx))
                    .unwrap_or_else(|| self.type_arena().void());

                let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                    .intern(&mut self.type_arena_mut());
                self.entity_registry_mut().register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature_id,
                    false,
                );
            }

            // Register static methods for generic classes
            if let Some(ref statics) = class.statics {
                let class_name_str = interner.resolve(class.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);

                    // Build merged scope: class type params + method type params
                    let mut merged_scope = type_param_scope.clone();
                    for tp in &method.type_params {
                        let tp_name_str = interner.resolve(tp.name);
                        let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                        merged_scope.add(TypeParamInfo {
                            name: tp.name,
                            name_id: tp_name_id,
                            constraint: None,
                            type_param_id: None,
                            variance: TypeParamVariance::default(),
                        });
                    }

                    // Build method type params with resolved constraints
                    let method_type_params: Vec<TypeParamInfo> = method
                        .type_params
                        .iter()
                        .map(|tp| {
                            let tp_name_str = interner.resolve(tp.name);
                            let tp_name_id =
                                self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                            let constraint = tp.constraint.as_ref().and_then(|c| {
                                self.resolve_type_param_constraint(
                                    c,
                                    &merged_scope,
                                    interner,
                                    tp.span,
                                )
                            });
                            TypeParamInfo {
                                name: tp.name,
                                name_id: tp_name_id,
                                constraint,
                                type_param_id: None,
                                variance: TypeParamVariance::default(),
                            }
                        })
                        .collect();

                    // Resolve parameter types with merged type params in scope
                    let params_id: Vec<ArenaTypeId> = method
                        .params
                        .iter()
                        .map(|p| {
                            let mut ctx = TypeResolutionContext::with_type_params(
                                &self.db,
                                interner,
                                module_id,
                                &merged_scope,
                            );
                            resolve_type_to_id(&p.ty, &mut ctx)
                        })
                        .collect();

                    // Resolve return type with merged type params in scope
                    let return_type_id = method
                        .return_type
                        .as_ref()
                        .map(|t| {
                            let mut ctx = TypeResolutionContext::with_type_params(
                                &self.db,
                                interner,
                                module_id,
                                &merged_scope,
                            );
                            resolve_type_to_id(t, &mut ctx)
                        })
                        .unwrap_or_else(|| self.type_arena().void());

                    let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                        .intern(&mut self.type_arena_mut());
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry_mut().register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        has_default,
                        method_type_params,
                    );
                }
            }

            // Register external methods in EntityRegistry (generic class)
            // Type params are in scope for resolving K, V, etc.
            if let Some(ref external) = class.external {
                let class_name_str = interner.resolve(class.name);
                for func in &external.functions {
                    let method_name_str = interner.resolve(func.vole_name);
                    let method_name_id =
                        self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);

                    // Resolve parameter types with type params in scope
                    let params_id: Vec<ArenaTypeId> = func
                        .params
                        .iter()
                        .map(|p| {
                            let mut ctx = TypeResolutionContext::with_type_params(
                                &self.db,
                                interner,
                                module_id,
                                &type_param_scope,
                            );
                            resolve_type_to_id(&p.ty, &mut ctx)
                        })
                        .collect();

                    // Resolve return type with type params in scope
                    let return_type_id = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            let mut ctx = TypeResolutionContext::with_type_params(
                                &self.db,
                                interner,
                                module_id,
                                &type_param_scope,
                            );
                            resolve_type_to_id(t, &mut ctx)
                        })
                        .unwrap_or_else(|| self.type_arena().void());

                    let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                        .intern(&mut self.type_arena_mut());
                    let native_name_str = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| method_name_str.to_string());
                    let builtin_mod = self.name_table_mut().builtin_module();
                    self.entity_registry_mut().register_method_with_binding(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        false, // external methods don't have defaults
                        Some(ExternalMethodInfo {
                            module_path: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&external.module_path]),
                            native_name: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]),
                        }),
                    );
                }
            }
        }
    }

    fn collect_record_signature(&mut self, record: &RecordDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[record.name], interner);

        // Handle generic records vs non-generic records
        if record.type_params.is_empty() {
            // Non-generic record: lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry_mut()
                .type_by_name(name_id)
                .expect("record shell registered in register_all_type_shells");

            // Collect field info for generic_info (needed for struct literal checking)
            // Convert Symbol field names to NameId at registration time
            let builtin_mod = self.name_table_mut().builtin_module();
            let field_names: Vec<NameId> = record
                .fields
                .iter()
                .map(|f| {
                    let name_str = interner.resolve(f.name);
                    self.name_table_mut().intern_raw(builtin_mod, &[name_str])
                })
                .collect();
            // Resolve field types directly to TypeId
            let field_type_ids: Vec<ArenaTypeId> = record
                .fields
                .iter()
                .map(|f| self.resolve_type_id(&f.ty, interner))
                .collect();

            // Set generic_info (with empty type_params for non-generic records)
            self.entity_registry_mut().set_generic_info(
                entity_type_id,
                GenericTypeInfo {
                    type_params: vec![],
                    field_names: field_names.clone(),
                    field_types: field_type_ids.clone(),
                },
            );

            // Register fields in EntityRegistry
            for (i, field) in record.fields.iter().enumerate() {
                let field_name_str = interner.resolve(field.name);
                let full_field_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), field_name_str],
                );
                self.entity_registry_mut().register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Register and validate implements list
            self.validate_and_register_implements(
                entity_type_id,
                &record.implements,
                record.span,
                interner,
            );

            // Register methods in EntityRegistry (single source of truth)
            // Use record TypeId as Self for resolving method signatures
            let self_type_id = self.type_arena_mut()
                .record(entity_type_id, TypeIdVec::new());
            let builtin_mod = self.name_table_mut().builtin_module();
            for method in &record.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), method_name_str],
                );
                let params_id: Vec<_> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type_id_with_self(&p.ty, interner, Some(self_type_id)))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id_with_self(t, interner, Some(self_type_id)))
                    .unwrap_or_else(|| self.type_arena().void());
                let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                    .intern(&mut self.type_arena_mut());
                self.entity_registry_mut().register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature_id,
                    false,
                );
            }

            // Register static methods in EntityRegistry
            if let Some(ref statics) = record.statics {
                let builtin_mod = self.name_table_mut().builtin_module();
                let record_name_str = interner.resolve(record.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[record_name_str, method_name_str]);
                    let params_id: Vec<_> = method
                        .params
                        .iter()
                        .map(|p| self.resolve_type_id(&p.ty, interner))
                        .collect();
                    let return_type_id = method
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_id(t, interner))
                        .unwrap_or_else(|| self.type_arena().void());
                    let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                        .intern(&mut self.type_arena_mut());
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry_mut().register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        has_default,
                        Vec::new(), // Non-generic record, no method type params
                    );
                }
            }
        } else {
            // Generic record: store with type params as placeholders
            let builtin_mod = self.name_table_mut().builtin_module();

            // First pass: create name_scope for constraint resolution (same pattern as functions)
            let mut name_scope = TypeParamScope::new();
            for tp in &record.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                name_scope.add(TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint: None,
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                });
            }

            // Second pass: resolve constraints with name_scope available
            let type_params: Vec<TypeParamInfo> = record
                .type_params
                .iter()
                .map(|tp| {
                    let tp_name_str = interner.resolve(tp.name);
                    let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                    let constraint = tp.constraint.as_ref().and_then(|c| {
                        self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                    });
                    TypeParamInfo {
                        name: tp.name,
                        name_id: tp_name_id,
                        constraint,
                        type_param_id: None,
                        variance: TypeParamVariance::default(),
                    }
                })
                .collect();

            let mut type_param_scope = TypeParamScope::new();
            for info in &type_params {
                type_param_scope.add(info.clone());
            }

            // Convert Symbol field names to NameId at registration time
            // (must be done before creating ctx which borrows name_table)
            let field_names: Vec<NameId> = record
                .fields
                .iter()
                .map(|f| {
                    let name_str = interner.resolve(f.name);
                    self.name_table_mut().intern_raw(builtin_mod, &[name_str])
                })
                .collect();

            // Resolve field types with type params in scope
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params(
                &self.db,
                interner,
                module_id,
                &type_param_scope,
            );

            // Resolve field types directly to TypeId
            let field_type_ids: Vec<ArenaTypeId> = record
                .fields
                .iter()
                .map(|f| resolve_type_to_id(&f.ty, &mut ctx))
                .collect();

            // Extract type param name IDs before moving type_params
            let type_param_name_ids: Vec<NameId> =
                type_params.iter().map(|tp| tp.name_id).collect();

            // Lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry_mut()
                .type_by_name(name_id)
                .expect("record shell registered in register_all_type_shells");

            // Register and validate implements list (for generic records)
            self.validate_and_register_implements(
                entity_type_id,
                &record.implements,
                record.span,
                interner,
            );

            // Register fields in EntityRegistry (needed for self.field access in methods)
            for (i, field) in record.fields.iter().enumerate() {
                let field_name_str = interner.resolve(field.name);
                let full_field_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), field_name_str],
                );
                // Use field_type_ids already computed above
                self.entity_registry_mut().register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Set type params on the type definition
            self.entity_registry_mut()
                .set_type_params(entity_type_id, type_param_name_ids);

            // Set generic info for type inference during struct literal checking
            self.entity_registry_mut().set_generic_info(
                entity_type_id,
                GenericTypeInfo {
                    type_params,
                    field_names,
                    field_types: field_type_ids,
                },
            );

            // Build self_type_id directly from entity_type_id with type param placeholders
            let type_arg_ids: Vec<ArenaTypeId> = type_param_scope
                .params()
                .iter()
                .map(|tp| self.type_arena_mut().type_param(tp.name_id))
                .collect();
            let self_type_id = self.type_arena_mut()
                .record(entity_type_id, type_arg_ids);

            for method in &record.methods {
                // Resolve types directly to TypeId
                let params_id: Vec<ArenaTypeId> = {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.db,
                        interner,
                        module_id,
                        &type_param_scope,
                    );
                    ctx.self_type = Some(self_type_id);
                    method
                        .params
                        .iter()
                        .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                        .collect()
                };
                let return_type_id: ArenaTypeId = {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.db,
                        interner,
                        module_id,
                        &type_param_scope,
                    );
                    ctx.self_type = Some(self_type_id);
                    method
                        .return_type
                        .as_ref()
                        .map(|t| resolve_type_to_id(t, &mut ctx))
                        .unwrap_or_else(|| self.type_arena().void())
                };

                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table_mut().intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), method_name_str],
                );
                let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                    .intern(&mut self.type_arena_mut());
                self.entity_registry_mut().register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature_id,
                    false,
                );
            }

            // Register static methods for generic records
            if let Some(ref statics) = record.statics {
                let record_name_str = interner.resolve(record.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[record_name_str, method_name_str]);

                    // Build merged scope: record type params + method type params
                    let mut merged_scope = type_param_scope.clone();
                    for tp in &method.type_params {
                        let tp_name_str = interner.resolve(tp.name);
                        let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                        merged_scope.add(TypeParamInfo {
                            name: tp.name,
                            name_id: tp_name_id,
                            constraint: None,
                            type_param_id: None,
                            variance: TypeParamVariance::default(),
                        });
                    }

                    // Build method type params with resolved constraints
                    let method_type_params: Vec<TypeParamInfo> = method
                        .type_params
                        .iter()
                        .map(|tp| {
                            let tp_name_str = interner.resolve(tp.name);
                            let tp_name_id =
                                self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                            let constraint = tp.constraint.as_ref().and_then(|c| {
                                self.resolve_type_param_constraint(
                                    c,
                                    &merged_scope,
                                    interner,
                                    tp.span,
                                )
                            });
                            TypeParamInfo {
                                name: tp.name,
                                name_id: tp_name_id,
                                constraint,
                                type_param_id: None,
                                variance: TypeParamVariance::default(),
                            }
                        })
                        .collect();

                    // Resolve parameter types with merged type params in scope
                    let params_id: Vec<ArenaTypeId> = method
                        .params
                        .iter()
                        .map(|p| {
                            let mut ctx = TypeResolutionContext::with_type_params(
                                &self.db,
                                interner,
                                module_id,
                                &merged_scope,
                            );
                            resolve_type_to_id(&p.ty, &mut ctx)
                        })
                        .collect();

                    // Resolve return type with merged type params in scope
                    let return_type_id = method
                        .return_type
                        .as_ref()
                        .map(|t| {
                            let mut ctx = TypeResolutionContext::with_type_params(
                                &self.db,
                                interner,
                                module_id,
                                &merged_scope,
                            );
                            resolve_type_to_id(t, &mut ctx)
                        })
                        .unwrap_or_else(|| self.type_arena().void());

                    let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                        .intern(&mut self.type_arena_mut());
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry_mut().register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        has_default,
                        method_type_params,
                    );
                }
            }
        }
    }

    /// Validate and register interface implementations for a type.
    /// Reports errors for unknown interfaces.
    fn validate_and_register_implements(
        &mut self,
        entity_type_id: TypeDefId,
        implements: &[TypeExpr],
        span: Span,
        interner: &Interner,
    ) {
        for iface_type in implements {
            let Some(iface_sym) = interface_base_name(iface_type) else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(iface_type, interner),
                        span: span.into(),
                    },
                    span,
                );
                continue;
            };

            let iface_str = interner.resolve(iface_sym);
            let Some(interface_type_id) = self
                .resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry())
            else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(iface_type, interner),
                        span: span.into(),
                    },
                    span,
                );
                continue;
            };

            // Extract and resolve type arguments directly to TypeId
            let type_arg_ids: Vec<ArenaTypeId> = match iface_type {
                TypeExpr::Generic { args, .. } => args
                    .iter()
                    .map(|arg| self.resolve_type_id(arg, interner))
                    .collect(),
                _ => Vec::new(),
            };

            // Validate that type args match interface's type params
            let expected_count = {
                let registry = self.entity_registry();
                registry.get_type(interface_type_id).type_params.len()
            };
            let found_count = type_arg_ids.len();
            if expected_count != found_count {
                self.add_error(
                    SemanticError::WrongTypeArgCount {
                        expected: expected_count,
                        found: found_count,
                        span: span.into(),
                    },
                    span,
                );
                continue;
            }
            self.entity_registry_mut().add_implementation(
                entity_type_id,
                interface_type_id,
                type_arg_ids,
            );
        }
    }

    fn collect_interface_def(&mut self, interface_decl: &InterfaceDecl, interner: &Interner) {
        let builtin_mod = self.name_table_mut().builtin_module();
        let mut name_scope = TypeParamScope::new();
        for tp in &interface_decl.type_params {
            let tp_name_str = interner.resolve(tp.name);
            let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
            name_scope.add(TypeParamInfo {
                name: tp.name,
                name_id: tp_name_id,
                constraint: None,
                type_param_id: None,
                variance: TypeParamVariance::default(),
            });
        }

        let type_params: Vec<TypeParamInfo> = interface_decl
            .type_params
            .iter()
            .map(|tp| {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                let constraint = tp.constraint.as_ref().and_then(|c| {
                    self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                });
                TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint,
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                }
            })
            .collect();

        let mut type_param_scope = TypeParamScope::new();
        for info in &type_params {
            type_param_scope.add(info.clone());
        }

        // Use current_module for proper module-qualified NameIds
        let name_str = interner.resolve(interface_decl.name).to_string();
        let name_id = self
            .name_table_mut()
            .intern_raw(self.current_module, &[&name_str]);

        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("interface shell registered in register_all_type_shells");

        let module_id = self.current_module;
        let mut type_ctx = TypeResolutionContext::with_type_params(
            &self.db,
            interner,
            module_id,
            &type_param_scope,
        );

        // Resolve field types directly to TypeId
        let resolved_fields: Vec<(Symbol, ArenaTypeId)> = interface_decl
            .fields
            .iter()
            .map(|f| (f.name, resolve_type_to_id(&f.ty, &mut type_ctx)))
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
        // We resolve types once to TypeId and reuse the data
        // Get void type before the loop to avoid borrowing db while type_ctx is borrowed
        let void_type = self.type_arena().void();
        let method_data: Vec<(Symbol, String, Vec<ArenaTypeId>, ArenaTypeId, bool)> =
            interface_decl
                .methods
                .iter()
                .map(|m| {
                    let name = m.name;
                    let name_str = interner.resolve(m.name).to_string();
                    let params_id: Vec<ArenaTypeId> = m
                        .params
                        .iter()
                        .map(|p| resolve_type_to_id(&p.ty, &mut type_ctx))
                        .collect();
                    let return_type_id = m
                        .return_type
                        .as_ref()
                        .map(|t| resolve_type_to_id(t, &mut type_ctx))
                        .unwrap_or(void_type);
                    let has_default = m.is_default
                        || m.body.is_some()
                        || default_external_methods.contains(&m.name);
                    (name, name_str, params_id, return_type_id, has_default)
                })
                .collect();

        let _interface_methods: Vec<crate::types::InterfaceMethodType> = method_data
            .iter()
            .map(|(name, _, params_id, return_type_id, has_default)| {
                let method_name_id = self.method_name_id(*name, interner);
                crate::types::InterfaceMethodType {
                    name: method_name_id,
                    has_default: *has_default,
                    params_id: params_id.iter().copied().collect(),
                    return_type_id: *return_type_id,
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
                let native_name_str = func
                    .native_name
                    .clone()
                    .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                let method_name_str = interner.resolve(func.vole_name).to_string();
                // Extract name IDs before struct literal to avoid overlapping borrows
                let (module_path, native_name) = {
                    let builtin_mod = self.name_table_mut().builtin_module();
                    let mut name_table = self.name_table_mut();
                    (
                        name_table.intern_raw(builtin_mod, &[&external.module_path]),
                        name_table.intern_raw(builtin_mod, &[&native_name_str]),
                    )
                };
                external_methods.insert(
                    method_name_str,
                    ExternalMethodInfo {
                        module_path,
                        native_name,
                    },
                );
            }
        }

        // Set type parameters in EntityRegistry (using NameIds only)
        let entity_type_params: Vec<_> = type_params.iter().map(|tp| tp.name_id).collect();
        self.entity_registry_mut()
            .set_type_params(entity_type_id, entity_type_params);

        // Register extends relationships
        // Collect parent type IDs first (separate from mutation to avoid borrow conflicts)
        let extends_parents: Vec<(NameId, Option<TypeDefId>)> = interface_decl
            .extends
            .iter()
            .map(|&parent_sym| {
                let parent_str = interner.resolve(parent_sym);
                let parent_name_id = self
                    .name_table_mut()
                    .intern_raw(self.current_module, &[parent_str]);
                let parent_type_id = self.entity_registry().type_by_name(parent_name_id);
                (parent_name_id, parent_type_id)
            })
            .collect();
        let _extends_type_ids: Vec<TypeDefId> = extends_parents
            .into_iter()
            .filter_map(|(_, parent_type_id)| {
                if let Some(parent_type_id) = parent_type_id {
                    self.entity_registry_mut()
                        .add_extends(entity_type_id, parent_type_id);
                    Some(parent_type_id)
                } else {
                    None
                }
            })
            .collect();

        // Register methods in EntityRegistry (with external bindings)
        for (_, method_name_str, params_id, return_type_id, has_default) in &method_data {
            let builtin_mod = self.name_table_mut().builtin_module();
            let method_name_id = self.name_table_mut().intern_raw(builtin_mod, &[method_name_str]);
            let full_method_name_id = self
                .name_table_mut()
                .intern_raw(self.current_module, &[&name_str, method_name_str]);
            let signature_id = FunctionType::from_ids(params_id, *return_type_id, false)
                .intern(&mut self.type_arena_mut());
            // Look up external binding for this method
            let external_binding = external_methods.get(method_name_str).copied();
            self.entity_registry_mut().register_method_with_binding(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature_id,
                *has_default,
                external_binding,
            );
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics_block) = interface_decl.statics {
            // Collect static method names with default external bindings
            let default_static_external_methods: HashSet<Symbol> = statics_block
                .external_blocks
                .iter()
                .filter(|ext| ext.is_default)
                .flat_map(|ext| ext.functions.iter().map(|f| f.vole_name))
                .collect();

            // Build external methods map for static methods
            let mut static_external_methods: HashMap<String, ExternalMethodInfo> = HashMap::new();
            for external in &statics_block.external_blocks {
                for func in &external.functions {
                    let native_name_str = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                    let method_name_str = interner.resolve(func.vole_name).to_string();
                    let builtin_mod = self.name_table_mut().builtin_module();
                    static_external_methods.insert(
                        method_name_str,
                        ExternalMethodInfo {
                            module_path: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&external.module_path]),
                            native_name: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]),
                        },
                    );
                }
            }

            // Register static methods
            for method in &statics_block.methods {
                let method_name_str = interner.resolve(method.name).to_string();
                let builtin_mod = self.name_table_mut().builtin_module();
                let method_name_id = self.name_table_mut().intern_raw(builtin_mod, &[&method_name_str]);
                let full_method_name_id = self
                    .name_table_mut()
                    .intern_raw(self.current_module, &[&name_str, &method_name_str]);

                // Create a fresh type context for each static method
                let mut static_type_ctx = TypeResolutionContext::with_type_params(
                    &self.db,
                    interner,
                    module_id,
                    &type_param_scope,
                );

                let params_id: Vec<ArenaTypeId> = method
                    .params
                    .iter()
                    .map(|p| resolve_type_to_id(&p.ty, &mut static_type_ctx))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type_to_id(t, &mut static_type_ctx))
                    .unwrap_or_else(|| self.type_arena().void());
                let has_default = method.is_default
                    || method.body.is_some()
                    || default_static_external_methods.contains(&method.name);

                let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                    .intern(&mut self.type_arena_mut());

                let external_binding = static_external_methods.get(&method_name_str).copied();
                self.entity_registry_mut().register_static_method_with_binding(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature_id,
                    has_default,
                    external_binding,
                    Vec::new(), // Interface static methods, no method type params
                );
            }
        }

        // Register fields in EntityRegistry (for interface field requirements)
        for (i, (field_name, field_type_id)) in resolved_fields.iter().enumerate() {
            let field_name_str = interner.resolve(*field_name).to_string();
            let builtin_mod = self.name_table_mut().builtin_module();
            let field_name_id = self.name_table_mut().intern_raw(builtin_mod, &[&field_name_str]);
            let full_field_name_id = self
                .name_table_mut()
                .intern_raw(self.current_module, &[&name_str, &field_name_str]);
            self.entity_registry_mut().register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                *field_type_id,
                i,
            );
        }
    }

    fn collect_implement_block(&mut self, impl_block: &ImplementBlock, interner: &Interner) {
        // Extract trait name symbol from trait_type (if present)
        let trait_name = impl_block.trait_type.as_ref().and_then(interface_base_name);

        // Validate trait exists if specified
        if let Some(ref trait_type) = impl_block.trait_type
            && let Some(name) = interface_base_name(trait_type)
        {
            // Validate interface exists via EntityRegistry using resolver
            let iface_str = interner.resolve(name);
            let iface_exists = self
                .resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry())
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

        let target_type_id = self.resolve_type_id(&impl_block.target_type, interner);

        // Validate target type exists
        if target_type_id.is_invalid() {
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

        // Extract impl_type_id with borrow scoped to just this call
        let impl_type_id = {
            let arena = self.type_arena();
            ImplTypeId::from_type_id(target_type_id, &arena, &self.entity_registry())
        };

        if let Some(impl_type_id) = impl_type_id {
            // Get TypeDefId for the target type (for EntityRegistry updates)
            // Use impl_type_id.name_id() which we already have, avoiding name_id_for_type
            let entity_type_id = self
                .type_arena()
                .type_def_id(target_type_id)
                .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

            // Get interface TypeDefId if implementing an interface
            let interface_type_id = trait_name.and_then(|name| {
                let iface_str = interner.resolve(name);
                self.resolver(interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry())
            });

            for method in &impl_block.methods {
                let params_id: Vec<ArenaTypeId> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type_id(&p.ty, interner))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id(t, interner))
                    .unwrap_or_else(|| self.type_arena().void());
                let func_type = FunctionType::from_ids(&params_id, return_type_id, false);

                let method_name_id = self.method_name_id(method.name, interner);
                self.implement_registry_mut().register_method(
                    impl_type_id,
                    method_name_id,
                    MethodImpl {
                        trait_name,
                        func_type: func_type.clone(),
                        is_builtin: false,
                        external_info: None,
                    },
                );

                // Also register in EntityRegistry if we have a type and interface
                if let (Some(entity_type_id), Some(interface_type_id)) =
                    (entity_type_id, interface_type_id)
                {
                    use crate::entity_defs::MethodBinding;
                    self.entity_registry_mut().add_method_binding(
                        entity_type_id,
                        interface_type_id,
                        MethodBinding {
                            method_name: method_name_id,
                            func_type,
                            is_builtin: false,
                            external_info: None,
                        },
                    );
                }
            }

            // Analyze external block if present
            if let Some(ref external) = impl_block.external {
                self.analyze_external_block(external, target_type_id, trait_name, interner);
            }

            // Register static methods from statics block (if present)
            if let Some(ref statics_block) = impl_block.statics {
                // Get entity type id for registering static methods
                // Use impl_type_id.name_id() which we already have
                let entity_type_id = self
                    .type_arena()
                    .type_def_id(target_type_id)
                    .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

                if let Some(entity_type_id) = entity_type_id {
                    let type_name_str = match &impl_block.target_type {
                        TypeExpr::Named(sym) => interner.resolve(*sym).to_string(),
                        TypeExpr::Primitive(prim) => {
                            let name_id = self.name_table().primitives.from_ast(*prim);
                            self.name_table_mut().display(name_id)
                        }
                        _ => "unknown".to_string(),
                    };

                    // Register static methods
                    for method in &statics_block.methods {
                        let method_name_str = interner.resolve(method.name).to_string();
                        let builtin_mod = self.name_table_mut().builtin_module();
                        let method_name_id =
                            self.name_table_mut().intern_raw(builtin_mod, &[&method_name_str]);
                        let full_method_name_id = self
                            .name_table_mut()
                            .intern_raw(self.current_module, &[&type_name_str, &method_name_str]);

                        let params_id: Vec<ArenaTypeId> = method
                            .params
                            .iter()
                            .map(|p| self.resolve_type_id(&p.ty, interner))
                            .collect();
                        let return_type_id = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type_id(t, interner))
                            .unwrap_or_else(|| self.type_arena().void());

                        let signature_id =
                            FunctionType::from_ids(&params_id, return_type_id, false)
                                .intern(&mut self.type_arena_mut());

                        self.entity_registry_mut().register_static_method(
                            entity_type_id,
                            method_name_id,
                            full_method_name_id,
                            signature_id,
                            false,      // implement block methods don't have defaults
                            Vec::new(), // implement block static methods, no method type params
                        );
                    }

                    // Register external static methods
                    for external in &statics_block.external_blocks {
                        for func in &external.functions {
                            let method_name_str = interner.resolve(func.vole_name).to_string();
                            let builtin_mod = self.name_table_mut().builtin_module();
                            let method_name_id =
                                self.name_table_mut().intern_raw(builtin_mod, &[&method_name_str]);
                            let full_method_name_id = self.name_table_mut().intern_raw(
                                self.current_module,
                                &[&type_name_str, &method_name_str],
                            );

                            let params_id: Vec<ArenaTypeId> = func
                                .params
                                .iter()
                                .map(|p| self.resolve_type_id(&p.ty, interner))
                                .collect();
                            let return_type_id = func
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_id(t, interner))
                                .unwrap_or_else(|| self.type_arena().void());

                            let signature_id =
                                FunctionType::from_ids(&params_id, return_type_id, false)
                                    .intern(&mut self.type_arena_mut());

                            let native_name_str = func
                                .native_name
                                .clone()
                                .unwrap_or_else(|| method_name_str.clone());
                            let builtin_mod = self.name_table_mut().builtin_module();

                            self.entity_registry_mut().register_static_method_with_binding(
                                entity_type_id,
                                method_name_id,
                                full_method_name_id,
                                signature_id,
                                false,
                                Some(ExternalMethodInfo {
                                    module_path: self
                                        .name_table_mut()
                                        .intern_raw(builtin_mod, &[&external.module_path]),
                                    native_name: self
                                        .name_table_mut()
                                        .intern_raw(builtin_mod, &[&native_name_str]),
                                }),
                                Vec::new(), // External static methods, no method type params
                            );
                        }
                    }
                }
            }
        }
    }

    /// Register external block functions as top-level functions
    /// This is called for standalone external blocks (not inside implement blocks)
    fn collect_external_block(&mut self, ext_block: &ExternalBlock, interner: &Interner) {
        let builtin_mod = self.name_table_mut().builtin_module();

        for func in &ext_block.functions {
            let name_id = self
                .name_table_mut()
                .intern(self.current_module, &[func.vole_name], interner);

            // For generic external functions, set up type param scope and register with GenericFuncInfo
            if !func.type_params.is_empty() {
                // Build TypeParamInfo list (like regular generic functions)
                let type_params: Vec<TypeParamInfo> = func
                    .type_params
                    .iter()
                    .map(|tp| {
                        let tp_name_str = interner.resolve(tp.name);
                        let tp_name_id = self.name_table_mut().intern_raw(builtin_mod, &[tp_name_str]);
                        TypeParamInfo {
                            name: tp.name,
                            name_id: tp_name_id,
                            constraint: None, // External functions don't have constraints for now
                            type_param_id: None,
                            variance: TypeParamVariance::default(),
                        }
                    })
                    .collect();

                let mut type_param_scope = TypeParamScope::new();
                for info in &type_params {
                    type_param_scope.add(info.clone());
                }

                // Resolve with type params in scope
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.db,
                    interner,
                    module_id,
                    &type_param_scope,
                );
                // Resolve directly to TypeId
                let param_type_ids: Vec<ArenaTypeId> = func
                    .params
                    .iter()
                    .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                    .collect();
                let return_type_id = func
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type_to_id(t, &mut ctx))
                    .unwrap_or_else(|| self.type_arena().void());

                // Create signature from TypeIds
                let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);

                // Register in EntityRegistry (like regular generic functions)
                let func_id = self.entity_registry_mut().register_function(
                    name_id,
                    name_id,
                    self.current_module,
                    signature.clone(),
                );
                self.entity_registry_mut().set_function_generic_info(
                    func_id,
                    GenericFuncInfo {
                        type_params,
                        param_types: param_type_ids,
                        return_type: return_type_id,
                    },
                );

                // NOTE: Don't register in self.functions for generic externals!
                // The call handler checks self.functions first without doing type inference.
                // Generic functions must go through EntityRegistry's generic_info path.

                // Store external info for codegen
                let name_str = interner.resolve(func.vole_name).to_string();
                let native_name_str = func.native_name.clone().unwrap_or_else(|| name_str.clone());
                self.implement_registry_mut().register_external_func(
                    name_str,
                    ExternalMethodInfo {
                        module_path: self
                            .name_table_mut()
                            .intern_raw(builtin_mod, &[&ext_block.module_path]),
                        native_name: self.name_table_mut().intern_raw(builtin_mod, &[&native_name_str]),
                    },
                );
            } else {
                // Non-generic external function
                let params_id: Vec<ArenaTypeId> = func
                    .params
                    .iter()
                    .map(|p| self.resolve_type_id(&p.ty, interner))
                    .collect();
                let return_type_id = func
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id(t, interner))
                    .unwrap_or_else(|| self.type_arena().void());

                let func_type = FunctionType::from_ids(&params_id, return_type_id, false);

                // Register the function with its Vole name (Symbol)
                self.functions.insert(func.vole_name, func_type.clone());

                // Also register by string name for cross-interner lookups (prelude functions)
                let name_str = interner.resolve(func.vole_name).to_string();
                self.functions_by_name
                    .insert(name_str.clone(), func_type.clone());

                // Register in EntityRegistry for consistency
                self.entity_registry_mut().register_function(
                    name_id,
                    name_id,
                    self.current_module,
                    func_type,
                );

                // Store the external info (module path and native name) for codegen
                let native_name_str = func.native_name.clone().unwrap_or_else(|| name_str.clone());
                // Extract name IDs before calling implement_registry_mut to avoid overlapping borrows
                let (module_path, native_name) = {
                    let mut name_table = self.name_table_mut();
                    (
                        name_table.intern_raw(builtin_mod, &[&ext_block.module_path]),
                        name_table.intern_raw(builtin_mod, &[&native_name_str]),
                    )
                };
                self.implement_registry_mut().register_external_func(
                    name_str,
                    ExternalMethodInfo {
                        module_path,
                        native_name,
                    },
                );
            }
        }
    }
}
