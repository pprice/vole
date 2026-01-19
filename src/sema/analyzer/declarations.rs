// src/sema/analyzer/declarations.rs
//! Declaration signature collection (Pass 1 of semantic analysis).

use super::*;
use crate::frontend::ast::{ExprKind, LetInit, TypeExpr};
use crate::sema::entity_defs::{GenericFuncInfo, GenericTypeInfo, TypeDefKind};
use crate::sema::type_arena::{TypeId as ArenaTypeId, TypeIdVec};
use crate::sema::types::{LegacyType, NominalType};

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
            .name_table
            .intern(self.current_module, &[name], interner);
        self.entity_registry
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
            .name_table
            .intern(self.current_module, &[func.name], interner);
        if func.type_params.is_empty() {
            // Non-generic function: resolve types normally
            let params: Vec<LegacyType> = func
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty, interner))
                .collect();
            let return_type = func
                .return_type
                .as_ref()
                .map(|t| self.resolve_type(t, interner))
                .unwrap_or(LegacyType::Void);

            let signature = FunctionType::new_with_arena(
                params,
                return_type,
                false,
                &mut self.type_arena.borrow_mut(),
            );

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
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
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
            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                &self.entity_registry,
                interner,
                &mut self.name_table,
                module_id,
                &type_param_scope,
                &self.type_arena,
            );
            let param_types: Vec<LegacyType> = func
                .params
                .iter()
                .map(|p| resolve_type(&p.ty, &mut ctx))
                .collect();
            let return_type = func
                .return_type
                .as_ref()
                .map(|t| resolve_type(t, &mut ctx))
                .unwrap_or(LegacyType::Void);

            // Create a FunctionType with TypeParam placeholders for the signature
            let signature = FunctionType::new_with_arena(
                param_types.clone(),
                return_type.clone(),
                false,
                &mut self.type_arena.borrow_mut(),
            );

            // Register in EntityRegistry
            let func_id = self.entity_registry.register_function(
                name_id,
                name_id, // For top-level functions, name_id == full_name_id
                self.current_module,
                signature,
            );

            // Set generic info on the function
            // Convert LegacyTypes to ArenaTypeIds for storage
            let param_type_ids: Vec<ArenaTypeId> = param_types
                .iter()
                .map(|t| self.type_arena.borrow_mut().from_type(t))
                .collect();
            let return_type_id = self.type_arena.borrow_mut().from_type(&return_type);
            self.entity_registry.set_function_generic_info(
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
            .name_table
            .intern(self.current_module, &[class.name], interner);

        // Handle generic classes vs non-generic classes
        if class.type_params.is_empty() {
            // Non-generic class: lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry
                .type_by_name(name_id)
                .expect("class shell registered in register_all_type_shells");

            // Collect field info for generic_info (needed for struct literal checking)
            // Convert Symbol field names to NameId at registration time
            let builtin_mod = self.name_table.builtin_module();
            let field_names: Vec<NameId> = class
                .fields
                .iter()
                .map(|f| {
                    let name_str = interner.resolve(f.name);
                    self.name_table.intern_raw(builtin_mod, &[name_str])
                })
                .collect();
            let field_types: Vec<LegacyType> = class
                .fields
                .iter()
                .map(|f| self.resolve_type(&f.ty, interner))
                .collect();
            // Convert to ArenaTypeIds for storage
            let field_type_ids: Vec<ArenaTypeId> = field_types
                .iter()
                .map(|t| self.type_arena.borrow_mut().from_type(t))
                .collect();

            // Set generic_info (with empty type_params for non-generic classes)
            self.entity_registry.set_generic_info(
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
                let full_field_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), field_name_str],
                );
                self.entity_registry.register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Register in type_table for type resolution
            let class_type = self.entity_registry.build_class_type(entity_type_id);
            if let Some(ref ct) = class_type {
                self.register_named_type(
                    class.name,
                    LegacyType::Nominal(NominalType::Class(ct.clone())),
                    interner,
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
            // Use class_type as Self for resolving method signatures
            let self_type_for_methods =
                class_type.map(|c| LegacyType::Nominal(NominalType::Class(c)));
            let builtin_mod = self.name_table.builtin_module();
            for method in &class.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), method_name_str],
                );
                let params: Vec<LegacyType> = method
                    .params
                    .iter()
                    .map(|p| {
                        self.resolve_type_with_self(&p.ty, interner, self_type_for_methods.clone())
                    })
                    .collect();
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        self.resolve_type_with_self(t, interner, self_type_for_methods.clone())
                    })
                    .unwrap_or(LegacyType::Void);
                let signature = FunctionType::new_with_arena(
                    params,
                    return_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                );
                self.entity_registry.register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    false, // class methods don't have defaults
                );
            }

            // Register static methods in EntityRegistry
            if let Some(ref statics) = class.statics {
                let builtin_mod = self.name_table.builtin_module();
                let class_name_str = interner.resolve(class.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);
                    let params: Vec<LegacyType> = method
                        .params
                        .iter()
                        .map(|p| self.resolve_type(&p.ty, interner))
                        .collect();
                    let return_type = method
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type(t, interner))
                        .unwrap_or(LegacyType::Void);
                    let signature = FunctionType::new_with_arena(
                        params,
                        return_type,
                        false,
                        &mut self.type_arena.borrow_mut(),
                    );
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry.register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature,
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
                        self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);
                    let params: Vec<LegacyType> = func
                        .params
                        .iter()
                        .map(|p| self.resolve_type(&p.ty, interner))
                        .collect();
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type(t, interner))
                        .unwrap_or(LegacyType::Void);
                    let signature = FunctionType::new_with_arena(
                        params,
                        return_type.clone(),
                        false,
                        &mut self.type_arena.borrow_mut(),
                    );
                    let native_name = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| method_name_str.to_string());
                    self.entity_registry.register_method_with_binding(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature,
                        false, // external methods don't have defaults
                        Some(ExternalMethodInfo {
                            module_path: external.module_path.clone(),
                            native_name,
                            return_type: Some(Box::new(return_type)),
                        }),
                    );
                }
            }
        } else {
            // Generic class: store with type params as placeholders
            let builtin_mod = self.name_table.builtin_module();

            // First pass: create name_scope for constraint resolution (same pattern as functions)
            let mut name_scope = TypeParamScope::new();
            for tp in &class.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                    let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                    self.name_table.intern_raw(builtin_mod, &[name_str])
                })
                .collect();

            // Resolve field types with type params in scope
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                &self.entity_registry,
                interner,
                &mut self.name_table,
                module_id,
                &type_param_scope,
                &self.type_arena,
            );

            let field_types: Vec<LegacyType> = class
                .fields
                .iter()
                .map(|f| resolve_type(&f.ty, &mut ctx))
                .collect();
            // Convert to ArenaTypeIds for storage
            let field_type_ids: Vec<ArenaTypeId> = field_types
                .iter()
                .map(|t| self.type_arena.borrow_mut().from_type(t))
                .collect();

            // Lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry
                .type_by_name(name_id)
                .expect("class shell registered in register_all_type_shells");

            // Set type params on the type definition (needed for method substitutions)
            let type_param_name_ids: Vec<NameId> =
                type_params.iter().map(|tp| tp.name_id).collect();
            self.entity_registry
                .set_type_params(entity_type_id, type_param_name_ids);

            // Set generic info for type inference during struct literal checking
            self.entity_registry.set_generic_info(
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
                let full_field_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), field_name_str],
                );
                // Use field_type_ids already computed above
                self.entity_registry.register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Build and register class type with TypeParam placeholders
            let class_type = self.entity_registry.build_class_type(entity_type_id);
            if let Some(ref ct) = class_type {
                self.register_named_type(
                    class.name,
                    LegacyType::Nominal(NominalType::Class(ct.clone())),
                    interner,
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
            let self_type_for_methods =
                class_type.map(|c| LegacyType::Nominal(NominalType::Class(c)));
            // Convert to TypeId for use in TypeResolutionContext
            let self_type_id = self_type_for_methods
                .as_ref()
                .map(|t| self.type_arena.borrow_mut().from_type(t));
            for method in &class.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(class.name), method_name_str],
                );

                // Resolve parameter types with type params and self in scope
                let params: Vec<LegacyType> = method
                    .params
                    .iter()
                    .map(|p| {
                        let mut ctx = TypeResolutionContext {
                            entity_registry: &self.entity_registry,
                            interner,
                            name_table: &mut self.name_table,
                            module_id,
                            type_params: Some(&type_param_scope),
                            self_type: self_type_id,
                            type_arena: &self.type_arena,
                        };
                        resolve_type(&p.ty, &mut ctx)
                    })
                    .collect();

                // Resolve return type with type params and self in scope
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        let mut ctx = TypeResolutionContext {
                            entity_registry: &self.entity_registry,
                            interner,
                            name_table: &mut self.name_table,
                            module_id,
                            type_params: Some(&type_param_scope),
                            self_type: self_type_id,
                            type_arena: &self.type_arena,
                        };
                        resolve_type(t, &mut ctx)
                    })
                    .unwrap_or(LegacyType::Void);

                let signature = FunctionType::new_with_arena(
                    params,
                    return_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                );
                self.entity_registry.register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    false,
                );
            }

            // Register static methods for generic classes
            if let Some(ref statics) = class.statics {
                let class_name_str = interner.resolve(class.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);

                    // Build merged scope: class type params + method type params
                    let mut merged_scope = type_param_scope.clone();
                    for tp in &method.type_params {
                        let tp_name_str = interner.resolve(tp.name);
                        let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                                self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                    let params: Vec<LegacyType> = method
                        .params
                        .iter()
                        .map(|p| {
                            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                                &self.entity_registry,
                                interner,
                                &mut self.name_table,
                                module_id,
                                &merged_scope,
                                &self.type_arena,
                            );
                            resolve_type(&p.ty, &mut ctx)
                        })
                        .collect();

                    // Resolve return type with merged type params in scope
                    let return_type = method
                        .return_type
                        .as_ref()
                        .map(|t| {
                            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                                &self.entity_registry,
                                interner,
                                &mut self.name_table,
                                module_id,
                                &merged_scope,
                                &self.type_arena,
                            );
                            resolve_type(t, &mut ctx)
                        })
                        .unwrap_or(LegacyType::Void);

                    let signature = FunctionType::new_with_arena(
                        params,
                        return_type,
                        false,
                        &mut self.type_arena.borrow_mut(),
                    );
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry.register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature,
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
                        self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table
                        .intern_raw(self.current_module, &[class_name_str, method_name_str]);

                    // Resolve parameter types with type params in scope
                    let params: Vec<LegacyType> = func
                        .params
                        .iter()
                        .map(|p| {
                            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                                &self.entity_registry,
                                interner,
                                &mut self.name_table,
                                module_id,
                                &type_param_scope,
                                &self.type_arena,
                            );
                            resolve_type(&p.ty, &mut ctx)
                        })
                        .collect();

                    // Resolve return type with type params in scope
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                                &self.entity_registry,
                                interner,
                                &mut self.name_table,
                                module_id,
                                &type_param_scope,
                                &self.type_arena,
                            );
                            resolve_type(t, &mut ctx)
                        })
                        .unwrap_or(LegacyType::Void);

                    let signature = FunctionType::new_with_arena(
                        params,
                        return_type.clone(),
                        false,
                        &mut self.type_arena.borrow_mut(),
                    );
                    let native_name = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| method_name_str.to_string());
                    self.entity_registry.register_method_with_binding(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature,
                        false, // external methods don't have defaults
                        Some(ExternalMethodInfo {
                            module_path: external.module_path.clone(),
                            native_name,
                            return_type: Some(Box::new(return_type)),
                        }),
                    );
                }
            }
        }
    }

    fn collect_record_signature(&mut self, record: &RecordDecl, interner: &Interner) {
        let name_id = self
            .name_table
            .intern(self.current_module, &[record.name], interner);

        // Handle generic records vs non-generic records
        if record.type_params.is_empty() {
            // Non-generic record: lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry
                .type_by_name(name_id)
                .expect("record shell registered in register_all_type_shells");

            // Collect field info for generic_info (needed for struct literal checking)
            // Convert Symbol field names to NameId at registration time
            let builtin_mod = self.name_table.builtin_module();
            let field_names: Vec<NameId> = record
                .fields
                .iter()
                .map(|f| {
                    let name_str = interner.resolve(f.name);
                    self.name_table.intern_raw(builtin_mod, &[name_str])
                })
                .collect();
            let field_types: Vec<LegacyType> = record
                .fields
                .iter()
                .map(|f| self.resolve_type(&f.ty, interner))
                .collect();
            // Convert to ArenaTypeIds for storage
            let field_type_ids: Vec<ArenaTypeId> = field_types
                .iter()
                .map(|t| self.type_arena.borrow_mut().from_type(t))
                .collect();

            // Set generic_info (with empty type_params for non-generic records)
            self.entity_registry.set_generic_info(
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
                let full_field_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), field_name_str],
                );
                self.entity_registry.register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Register in type_table for type resolution
            let record_type = self.entity_registry.build_record_type(entity_type_id);
            if let Some(ref rt) = record_type {
                self.register_named_type(
                    record.name,
                    LegacyType::Nominal(NominalType::Record(rt.clone())),
                    interner,
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
            // Use record_type as Self for resolving method signatures
            let self_type_for_methods =
                record_type.map(|r| LegacyType::Nominal(NominalType::Record(r)));
            let builtin_mod = self.name_table.builtin_module();
            for method in &record.methods {
                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), method_name_str],
                );
                let params: Vec<LegacyType> = method
                    .params
                    .iter()
                    .map(|p| {
                        self.resolve_type_with_self(&p.ty, interner, self_type_for_methods.clone())
                    })
                    .collect();
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        self.resolve_type_with_self(t, interner, self_type_for_methods.clone())
                    })
                    .unwrap_or(LegacyType::Void);
                let signature = FunctionType::new_with_arena(
                    params,
                    return_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                );
                self.entity_registry.register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    false,
                );
            }

            // Register static methods in EntityRegistry
            if let Some(ref statics) = record.statics {
                let builtin_mod = self.name_table.builtin_module();
                let record_name_str = interner.resolve(record.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table
                        .intern_raw(self.current_module, &[record_name_str, method_name_str]);
                    let params: Vec<LegacyType> = method
                        .params
                        .iter()
                        .map(|p| self.resolve_type(&p.ty, interner))
                        .collect();
                    let return_type = method
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type(t, interner))
                        .unwrap_or(LegacyType::Void);
                    let signature = FunctionType::new_with_arena(
                        params,
                        return_type,
                        false,
                        &mut self.type_arena.borrow_mut(),
                    );
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry.register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature,
                        has_default,
                        Vec::new(), // Non-generic record, no method type params
                    );
                }
            }
        } else {
            // Generic record: store with type params as placeholders
            let builtin_mod = self.name_table.builtin_module();

            // First pass: create name_scope for constraint resolution (same pattern as functions)
            let mut name_scope = TypeParamScope::new();
            for tp in &record.type_params {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                    let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                    self.name_table.intern_raw(builtin_mod, &[name_str])
                })
                .collect();

            // Resolve field types with type params in scope
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                &self.entity_registry,
                interner,
                &mut self.name_table,
                module_id,
                &type_param_scope,
                &self.type_arena,
            );

            let field_types: Vec<LegacyType> = record
                .fields
                .iter()
                .map(|f| resolve_type(&f.ty, &mut ctx))
                .collect();
            // Convert to ArenaTypeIds for storage
            let field_type_ids: Vec<ArenaTypeId> = field_types
                .iter()
                .map(|t| self.type_arena.borrow_mut().from_type(t))
                .collect();

            // Extract type param name IDs before moving type_params
            let type_param_name_ids: Vec<NameId> =
                type_params.iter().map(|tp| tp.name_id).collect();

            // Also register in regular records with TypeParam placeholders
            // This allows struct literal checking to find the record definition
            let _fields: Vec<StructField> = record
                .fields
                .iter()
                .enumerate()
                .map(|(i, f)| {
                    let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                        &self.entity_registry,
                        interner,
                        &mut self.name_table,
                        module_id,
                        &type_param_scope,
                        &self.type_arena,
                    );
                    StructField {
                        name: interner.resolve(f.name).to_string(),
                        ty: resolve_type(&f.ty, &mut ctx),
                        slot: i,
                    }
                })
                .collect();
            // Lookup shell registered in pass 0.5
            let entity_type_id = self
                .entity_registry
                .type_by_name(name_id)
                .expect("record shell registered in register_all_type_shells");

            let record_type = RecordType {
                type_def_id: entity_type_id,
                type_args_id: TypeIdVec::new(),
            };
            self.register_named_type(
                record.name,
                LegacyType::Nominal(NominalType::Record(record_type.clone())),
                interner,
            );

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
                let full_field_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), field_name_str],
                );
                // Use field_type_ids already computed above
                self.entity_registry.register_field(
                    entity_type_id,
                    field_names[i],
                    full_field_name_id,
                    field_type_ids[i],
                    i,
                );
            }

            // Set type params on the type definition
            self.entity_registry
                .set_type_params(entity_type_id, type_param_name_ids);

            // Set generic info for type inference during struct literal checking
            self.entity_registry.set_generic_info(
                entity_type_id,
                GenericTypeInfo {
                    type_params,
                    field_names,
                    field_types: field_type_ids,
                },
            );

            // Convert self type to TypeId once for all method resolutions
            let self_type_legacy = LegacyType::Nominal(NominalType::Record(record_type));
            let self_type_id = self.type_arena.borrow_mut().from_type(&self_type_legacy);

            for method in &record.methods {
                // First resolve types, then intern names (to avoid borrow conflicts)
                let params: Vec<LegacyType> = {
                    let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                        &self.entity_registry,
                        interner,
                        &mut self.name_table,
                        module_id,
                        &type_param_scope,
                        &self.type_arena,
                    );
                    ctx.self_type = Some(self_type_id);
                    method
                        .params
                        .iter()
                        .map(|p| resolve_type(&p.ty, &mut ctx))
                        .collect()
                };
                let return_type: LegacyType = {
                    let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                        &self.entity_registry,
                        interner,
                        &mut self.name_table,
                        module_id,
                        &type_param_scope,
                        &self.type_arena,
                    );
                    ctx.self_type = Some(self_type_id);
                    method
                        .return_type
                        .as_ref()
                        .map(|t| resolve_type(t, &mut ctx))
                        .unwrap_or(LegacyType::Void)
                };

                let method_name_str = interner.resolve(method.name);
                let method_name_id = self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                let full_method_name_id = self.name_table.intern_raw(
                    self.current_module,
                    &[interner.resolve(record.name), method_name_str],
                );
                let signature = FunctionType::new_with_arena(
                    params,
                    return_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                );
                self.entity_registry.register_method(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    false,
                );
            }

            // Register static methods for generic records
            if let Some(ref statics) = record.statics {
                let record_name_str = interner.resolve(record.name);
                for method in &statics.methods {
                    let method_name_str = interner.resolve(method.name);
                    let method_name_id =
                        self.name_table.intern_raw(builtin_mod, &[method_name_str]);
                    let full_method_name_id = self
                        .name_table
                        .intern_raw(self.current_module, &[record_name_str, method_name_str]);

                    // Build merged scope: record type params + method type params
                    let mut merged_scope = type_param_scope.clone();
                    for tp in &method.type_params {
                        let tp_name_str = interner.resolve(tp.name);
                        let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                                self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                    let params: Vec<LegacyType> = method
                        .params
                        .iter()
                        .map(|p| {
                            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                                &self.entity_registry,
                                interner,
                                &mut self.name_table,
                                module_id,
                                &merged_scope,
                                &self.type_arena,
                            );
                            resolve_type(&p.ty, &mut ctx)
                        })
                        .collect();

                    // Resolve return type with merged type params in scope
                    let return_type = method
                        .return_type
                        .as_ref()
                        .map(|t| {
                            let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                                &self.entity_registry,
                                interner,
                                &mut self.name_table,
                                module_id,
                                &merged_scope,
                                &self.type_arena,
                            );
                            resolve_type(t, &mut ctx)
                        })
                        .unwrap_or(LegacyType::Void);

                    let signature = FunctionType::new_with_arena(
                        params,
                        return_type,
                        false,
                        &mut self.type_arena.borrow_mut(),
                    );
                    let has_default = method.is_default || method.body.is_some();
                    self.entity_registry.register_static_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature,
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
                .resolve_type_str_or_interface(iface_str, &self.entity_registry)
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

            // Extract and resolve type arguments for generic interfaces
            let type_args: Vec<LegacyType> = match iface_type {
                TypeExpr::Generic { args, .. } => args
                    .iter()
                    .map(|arg| self.resolve_type(arg, interner))
                    .collect(),
                _ => Vec::new(),
            };

            // Validate that type args match interface's type params
            let interface_def = self.entity_registry.get_type(interface_type_id);
            let expected_count = interface_def.type_params.len();
            let found_count = type_args.len();
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

            // Convert type_args to ArenaTypeIds for storage
            let type_arg_ids: Vec<ArenaTypeId> = type_args
                .iter()
                .map(|t| self.type_arena.borrow_mut().from_type(t))
                .collect();
            self.entity_registry.add_implementation(
                entity_type_id,
                interface_type_id,
                type_arg_ids,
            );
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
                type_param_id: None,
                variance: TypeParamVariance::default(),
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
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                }
            })
            .collect();

        let mut type_param_scope = TypeParamScope::new();
        for info in &type_params {
            type_param_scope.add(info.clone());
        }

        let module_id = self.current_module;
        let mut type_ctx = TypeResolutionContext::with_type_params_and_arena(
            &self.entity_registry,
            interner,
            &mut self.name_table,
            module_id,
            &type_param_scope,
            &self.type_arena,
        );

        // Resolve field types directly from AST (store for later registration)
        let resolved_fields: Vec<(Symbol, LegacyType)> = interface_decl
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
        let method_data: Vec<(Symbol, String, Vec<LegacyType>, LegacyType, bool)> = interface_decl
            .methods
            .iter()
            .map(|m| {
                let name = m.name;
                let name_str = interner.resolve(m.name).to_string();
                let params: Vec<LegacyType> = m
                    .params
                    .iter()
                    .map(|p| resolve_type(&p.ty, &mut type_ctx))
                    .collect();
                let return_type = m
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type(t, &mut type_ctx))
                    .unwrap_or(LegacyType::Void);
                let has_default =
                    m.is_default || m.body.is_some() || default_external_methods.contains(&m.name);
                (name, name_str, params, return_type, has_default)
            })
            .collect();

        let interface_methods: Vec<crate::sema::types::InterfaceMethodType> = method_data
            .iter()
            .map(|(name, _, params, return_type, has_default)| {
                // Get method name_id before borrowing arena
                let method_name_id = self.method_name_id(*name, interner);
                // Intern types into arena
                let mut arena = self.type_arena.borrow_mut();
                let params_id: TypeIdVec = params.iter().map(|p| arena.from_type(p)).collect();
                let return_type_id = arena.from_type(return_type);
                crate::sema::types::InterfaceMethodType {
                    name: method_name_id,
                    params: params.clone().into(),
                    return_type: Box::new(return_type.clone()),
                    has_default: *has_default,
                    params_id: Some(params_id),
                    return_type_id: Some(return_type_id),
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
                        return_type: None, // Type is already defined in interface method declaration
                    },
                );
            }
        }

        // Use current_module for proper module-qualified NameIds
        let name_str = interner.resolve(interface_decl.name).to_string();
        let name_id = self
            .name_table
            .intern_raw(self.current_module, &[&name_str]);

        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry
            .type_by_name(name_id)
            .expect("interface shell registered in register_all_type_shells");

        // Set type parameters in EntityRegistry (using NameIds only)
        let entity_type_params: Vec<_> = type_params.iter().map(|tp| tp.name_id).collect();
        self.entity_registry
            .set_type_params(entity_type_id, entity_type_params);

        // Register extends relationships and build extends Vec<TypeDefId>
        let extends_type_ids: Vec<TypeDefId> = interface_decl
            .extends
            .iter()
            .filter_map(|&parent_sym| {
                let parent_str = interner.resolve(parent_sym);
                let parent_name_id = self
                    .name_table
                    .intern_raw(self.current_module, &[parent_str]);
                if let Some(parent_type_id) = self.entity_registry.type_by_name(parent_name_id) {
                    self.entity_registry
                        .add_extends(entity_type_id, parent_type_id);
                    Some(parent_type_id)
                } else {
                    None
                }
            })
            .collect();

        // Register methods in EntityRegistry (with external bindings)
        for (_, method_name_str, params, return_type, has_default) in &method_data {
            let builtin_mod = self.name_table.builtin_module();
            let method_name_id = self.name_table.intern_raw(builtin_mod, &[method_name_str]);
            let full_method_name_id = self
                .name_table
                .intern_raw(self.current_module, &[&name_str, method_name_str]);
            let signature = FunctionType::new_with_arena(
                params.clone(),
                return_type.clone(),
                false,
                &mut self.type_arena.borrow_mut(),
            );
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
                    let native_name = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                    let method_name_str = interner.resolve(func.vole_name).to_string();
                    static_external_methods.insert(
                        method_name_str,
                        ExternalMethodInfo {
                            module_path: external.module_path.clone(),
                            native_name,
                            return_type: None,
                        },
                    );
                }
            }

            // Register static methods
            for method in &statics_block.methods {
                let method_name_str = interner.resolve(method.name).to_string();
                let builtin_mod = self.name_table.builtin_module();
                let method_name_id = self.name_table.intern_raw(builtin_mod, &[&method_name_str]);
                let full_method_name_id = self
                    .name_table
                    .intern_raw(self.current_module, &[&name_str, &method_name_str]);

                // Create a fresh type context for each static method
                let mut static_type_ctx = TypeResolutionContext::with_type_params_and_arena(
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    &type_param_scope,
                    &self.type_arena,
                );

                let params: Vec<LegacyType> = method
                    .params
                    .iter()
                    .map(|p| resolve_type(&p.ty, &mut static_type_ctx))
                    .collect();
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type(t, &mut static_type_ctx))
                    .unwrap_or(LegacyType::Void);
                let has_default = method.is_default
                    || method.body.is_some()
                    || default_static_external_methods.contains(&method.name);

                let signature = FunctionType::new_with_arena(
                    params,
                    return_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                );

                let external_binding = static_external_methods.get(&method_name_str).cloned();
                self.entity_registry.register_static_method_with_binding(
                    entity_type_id,
                    method_name_id,
                    full_method_name_id,
                    signature,
                    has_default,
                    external_binding,
                    Vec::new(), // Interface static methods, no method type params
                );
            }
        }

        // Register fields in EntityRegistry (for interface field requirements)
        for (i, (field_name, field_ty)) in resolved_fields.iter().enumerate() {
            let field_name_str = interner.resolve(*field_name).to_string();
            let builtin_mod = self.name_table.builtin_module();
            let field_name_id = self.name_table.intern_raw(builtin_mod, &[&field_name_str]);
            let full_field_name_id = self
                .name_table
                .intern_raw(self.current_module, &[&name_str, &field_name_str]);
            // Convert to ArenaTypeId for storage
            let field_type_id = self.type_arena.borrow_mut().from_type(field_ty);
            self.entity_registry.register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                field_type_id,
                i,
            );
        }

        self.register_named_type(
            interface_decl.name,
            LegacyType::Nominal(NominalType::Interface(crate::sema::types::InterfaceType {
                type_def_id: entity_type_id,
                type_args_id: TypeIdVec::new(),
                methods: interface_methods.into(),
                extends: extends_type_ids.into(),
            })),
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
            // Validate interface exists via EntityRegistry using resolver
            let iface_str = interner.resolve(name);
            let iface_exists = self
                .resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry)
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
        if target_type.is_invalid() {
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

        if let Some(impl_type_id) = ImplTypeId::from_type(
            &target_type,
            &self.entity_registry.type_table,
            &self.entity_registry,
        ) {
            // Get TypeDefId for the target type (for EntityRegistry updates)
            // Use impl_type_id.name_id() which we already have, avoiding name_id_for_type
            let entity_type_id = target_type
                .type_def_id()
                .or_else(|| self.entity_registry.type_by_name(impl_type_id.name_id()));

            // Get interface TypeDefId if implementing an interface
            let interface_type_id = trait_name.and_then(|name| {
                let iface_str = interner.resolve(name);
                self.resolver(interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry)
            });

            for method in &impl_block.methods {
                let params: Vec<LegacyType> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type(&p.ty, interner))
                    .collect();
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type(t, interner))
                    .unwrap_or(LegacyType::Void);
                let func_type = FunctionType::new_with_arena(
                    params,
                    return_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                );

                let method_name_id = self.method_name_id(method.name, interner);
                self.implement_registry.register_method(
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
                    use crate::sema::entity_defs::MethodBinding;
                    self.entity_registry.add_method_binding(
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
                self.analyze_external_block(external, &target_type, trait_name, interner);
            }

            // Register static methods from statics block (if present)
            if let Some(ref statics_block) = impl_block.statics {
                // Get entity type id for registering static methods
                // Use impl_type_id.name_id() which we already have
                let entity_type_id = target_type
                    .type_def_id()
                    .or_else(|| self.entity_registry.type_by_name(impl_type_id.name_id()));

                if let Some(entity_type_id) = entity_type_id {
                    let type_name_str = match &impl_block.target_type {
                        TypeExpr::Named(sym) => interner.resolve(*sym).to_string(),
                        TypeExpr::Primitive(prim) => self
                            .name_table
                            .display(self.name_table.primitives.from_ast(*prim)),
                        _ => "unknown".to_string(),
                    };

                    // Register static methods
                    for method in &statics_block.methods {
                        let method_name_str = interner.resolve(method.name).to_string();
                        let builtin_mod = self.name_table.builtin_module();
                        let method_name_id =
                            self.name_table.intern_raw(builtin_mod, &[&method_name_str]);
                        let full_method_name_id = self
                            .name_table
                            .intern_raw(self.current_module, &[&type_name_str, &method_name_str]);

                        let params: Vec<LegacyType> = method
                            .params
                            .iter()
                            .map(|p| self.resolve_type(&p.ty, interner))
                            .collect();
                        let return_type = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type(t, interner))
                            .unwrap_or(LegacyType::Void);

                        let signature = FunctionType::new_with_arena(
                            params,
                            return_type,
                            false,
                            &mut self.type_arena.borrow_mut(),
                        );

                        self.entity_registry.register_static_method(
                            entity_type_id,
                            method_name_id,
                            full_method_name_id,
                            signature,
                            false,      // implement block methods don't have defaults
                            Vec::new(), // implement block static methods, no method type params
                        );
                    }

                    // Register external static methods
                    for external in &statics_block.external_blocks {
                        for func in &external.functions {
                            let method_name_str = interner.resolve(func.vole_name).to_string();
                            let builtin_mod = self.name_table.builtin_module();
                            let method_name_id =
                                self.name_table.intern_raw(builtin_mod, &[&method_name_str]);
                            let full_method_name_id = self.name_table.intern_raw(
                                self.current_module,
                                &[&type_name_str, &method_name_str],
                            );

                            let params: Vec<LegacyType> = func
                                .params
                                .iter()
                                .map(|p| self.resolve_type(&p.ty, interner))
                                .collect();
                            let return_type = func
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type(t, interner))
                                .unwrap_or(LegacyType::Void);

                            let signature = FunctionType::new_with_arena(
                                params,
                                return_type.clone(),
                                false,
                                &mut self.type_arena.borrow_mut(),
                            );

                            let native_name = func
                                .native_name
                                .clone()
                                .unwrap_or_else(|| method_name_str.clone());

                            self.entity_registry.register_static_method_with_binding(
                                entity_type_id,
                                method_name_id,
                                full_method_name_id,
                                signature,
                                false,
                                Some(ExternalMethodInfo {
                                    module_path: external.module_path.clone(),
                                    native_name,
                                    return_type: Some(Box::new(return_type)),
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
        let builtin_mod = self.name_table.builtin_module();

        for func in &ext_block.functions {
            let name_id = self
                .name_table
                .intern(self.current_module, &[func.vole_name], interner);

            // For generic external functions, set up type param scope and register with GenericFuncInfo
            if !func.type_params.is_empty() {
                // Build TypeParamInfo list (like regular generic functions)
                let type_params: Vec<TypeParamInfo> = func
                    .type_params
                    .iter()
                    .map(|tp| {
                        let tp_name_str = interner.resolve(tp.name);
                        let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
                let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    &type_param_scope,
                    &self.type_arena,
                );
                let param_types: Vec<LegacyType> = func
                    .params
                    .iter()
                    .map(|p| resolve_type(&p.ty, &mut ctx))
                    .collect();
                let return_type = func
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type(t, &mut ctx))
                    .unwrap_or(LegacyType::Void);

                // Create signature with TypeParam placeholders
                let signature = FunctionType::new_with_arena(
                    param_types.clone(),
                    return_type.clone(),
                    false,
                    &mut self.type_arena.borrow_mut(),
                );

                // Register in EntityRegistry (like regular generic functions)
                let func_id = self.entity_registry.register_function(
                    name_id,
                    name_id,
                    self.current_module,
                    signature.clone(),
                );

                // Set generic info for call-site type inference
                // Convert LegacyTypes to ArenaTypeIds for storage
                let param_type_ids: Vec<ArenaTypeId> = param_types
                    .iter()
                    .map(|t| self.type_arena.borrow_mut().from_type(t))
                    .collect();
                let return_type_id = self.type_arena.borrow_mut().from_type(&return_type);
                self.entity_registry.set_function_generic_info(
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
                let native_name = func.native_name.clone().unwrap_or_else(|| name_str.clone());
                self.implement_registry.register_external_func(
                    name_str,
                    ExternalMethodInfo {
                        module_path: ext_block.module_path.clone(),
                        native_name,
                        return_type: Some(Box::new(return_type)),
                    },
                );
            } else {
                // Non-generic external function
                let params: Vec<LegacyType> = func
                    .params
                    .iter()
                    .map(|p| self.resolve_type(&p.ty, interner))
                    .collect();
                let return_type = func
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type(t, interner))
                    .unwrap_or(LegacyType::Void);

                let func_type = FunctionType::new_with_arena(
                    params,
                    return_type.clone(),
                    false,
                    &mut self.type_arena.borrow_mut(),
                );

                // Register the function with its Vole name (Symbol)
                self.functions.insert(func.vole_name, func_type.clone());

                // Also register by string name for cross-interner lookups (prelude functions)
                let name_str = interner.resolve(func.vole_name).to_string();
                self.functions_by_name
                    .insert(name_str.clone(), func_type.clone());

                // Register in EntityRegistry for consistency
                self.entity_registry.register_function(
                    name_id,
                    name_id,
                    self.current_module,
                    func_type,
                );

                // Store the external info (module path and native name) for codegen
                let native_name = func.native_name.clone().unwrap_or_else(|| name_str.clone());
                self.implement_registry.register_external_func(
                    name_str,
                    ExternalMethodInfo {
                        module_path: ext_block.module_path.clone(),
                        native_name,
                        return_type: Some(Box::new(return_type)),
                    },
                );
            }
        }
    }
}
