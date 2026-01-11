use std::collections::HashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};
use cranelift_module::Module;

use super::{Compiler, ControlFlowCtx};
use crate::codegen::stmt::compile_block;
use crate::codegen::types::{
    CompileCtx, MethodInfo, TypeMetadata, method_name_id, resolve_type_expr_full, type_to_cranelift,
};
use crate::frontend::{
    ClassDecl, FuncDecl, ImplementBlock, InterfaceMethod, Interner, RecordDecl, StaticsBlock,
    Symbol, TypeExpr,
};
use crate::identity::ModuleId;
use crate::sema::{Type, TypeId};

impl Compiler<'_> {
    /// Compile methods for a class
    pub(super) fn compile_class_methods(
        &mut self,
        class: &ClassDecl,
        program: &crate::frontend::Program,
    ) -> Result<(), String> {
        let metadata = self
            .type_metadata
            .get(&class.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: class {} not registered",
                    self.analyzed.interner.resolve(class.name)
                )
            })?;

        for method in &class.methods {
            self.compile_method(method, class.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();
        // Look up class type_def_id via immutable name_id lookup
        if let Some(class_name_id) = self.analyzed.name_table.name_id(
            self.analyzed.name_table.main_module(),
            &[class.name],
            &self.analyzed.interner,
        ) {
            if let Some(type_def_id) = self.analyzed.entity_registry.type_by_name(class_name_id) {
                for interface_id in
                    self.analyzed.entity_registry.get_implemented_interfaces(type_def_id)
                {
                    let interface_def = self.analyzed.entity_registry.get_type(interface_id);
                    // Look up interface name Symbol
                    if let Some(interface_name_str) = self
                        .analyzed
                        .name_table
                        .last_segment_str(interface_def.name_id)
                    {
                        if let Some(interface_name) =
                            self.analyzed.interner.lookup(&interface_name_str)
                        {
                            if let Some(interface_decl) =
                                self.find_interface_decl(program, interface_name)
                            {
                                for method in &interface_decl.methods {
                                    if method.body.is_some()
                                        && !direct_methods.contains(&method.name)
                                    {
                                        self.compile_default_method(
                                            method,
                                            class.name,
                                            &metadata,
                                        )?;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Compile static methods
        if let Some(ref statics) = class.statics {
            self.compile_static_methods(statics, class.name)?;
        }

        Ok(())
    }

    /// Compile methods for a record
    pub(super) fn compile_record_methods(
        &mut self,
        record: &RecordDecl,
        program: &crate::frontend::Program,
    ) -> Result<(), String> {
        let metadata = self
            .type_metadata
            .get(&record.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: record {} not registered",
                    self.analyzed.interner.resolve(record.name)
                )
            })?;

        for method in &record.methods {
            self.compile_method(method, record.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();
        // Look up record type_def_id via immutable name_id lookup
        if let Some(record_name_id) = self.analyzed.name_table.name_id(
            self.analyzed.name_table.main_module(),
            &[record.name],
            &self.analyzed.interner,
        ) {
            if let Some(type_def_id) = self.analyzed.entity_registry.type_by_name(record_name_id) {
                for interface_id in
                    self.analyzed.entity_registry.get_implemented_interfaces(type_def_id)
                {
                    let interface_def = self.analyzed.entity_registry.get_type(interface_id);
                    // Look up interface name Symbol
                    if let Some(interface_name_str) = self
                        .analyzed
                        .name_table
                        .last_segment_str(interface_def.name_id)
                    {
                        if let Some(interface_name) =
                            self.analyzed.interner.lookup(&interface_name_str)
                        {
                            if let Some(interface_decl) =
                                self.find_interface_decl(program, interface_name)
                            {
                                for method in &interface_decl.methods {
                                    if method.body.is_some()
                                        && !direct_methods.contains(&method.name)
                                    {
                                        self.compile_default_method(
                                            method,
                                            record.name,
                                            &metadata,
                                        )?;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Compile static methods
        if let Some(ref statics) = record.statics {
            self.compile_static_methods(statics, record.name)?;
        }

        Ok(())
    }

    /// Get the type name symbol from a TypeExpr (for implement blocks on records/classes)
    /// Returns None for primitives since they should use the TypeId path which is interner-independent
    fn get_type_name_symbol(&self, ty: &TypeExpr) -> Option<Symbol> {
        match ty {
            TypeExpr::Named(sym) => Some(*sym),
            // Primitives return None so we use the TypeId path instead,
            // which avoids cross-interner issues with module programs
            TypeExpr::Primitive(_) => None,
            _ => None,
        }
    }

    /// Get the type name string from a TypeExpr (works for primitives and named types)
    fn get_type_name_from_expr(&self, ty: &TypeExpr) -> Option<String> {
        match ty {
            TypeExpr::Primitive(p) => Some(Type::from_primitive(*p).name().to_string()),
            TypeExpr::Named(sym) => Some(self.analyzed.interner.resolve(*sym).to_string()),
            _ => None,
        }
    }

    /// Register implement block methods (first pass)
    pub(super) fn register_implement_block(&mut self, impl_block: &ImplementBlock) {
        self.register_implement_block_with_interner(impl_block, &self.analyzed.interner.clone())
    }

    /// Register implement block methods with a specific interner (for module programs)
    pub(super) fn register_implement_block_with_interner(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
    ) {
        let module_id = self.analyzed.name_table.main_module();
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return; // Unsupported type for implement block
        };
        let type_sym = self.get_type_name_symbol(&impl_block.target_type);
        let func_module = if matches!(&impl_block.target_type, TypeExpr::Primitive(_)) {
            self.func_registry.builtin_module()
        } else {
            self.func_registry.main_module()
        };

        // Get the Vole type for the target (used for creating signature)
        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        let self_vole_type = match &impl_block.target_type {
            TypeExpr::Primitive(p) => Type::from_primitive(*p),
            TypeExpr::Named(sym) => self
                .type_metadata
                .get(sym)
                .map(|m| m.vole_type.clone())
                .unwrap_or(Type::Error),
            _ => resolve_type_expr_full(
                &impl_block.target_type,
                &self.analyzed.entity_registry,
                &self.type_metadata,
                interner,
                &self.analyzed.name_table,
                module_id,
            ),
        };

        let type_id = TypeId::from_type(&self_vole_type, &self.analyzed.type_table);

        // Declare methods as functions: TypeName::methodName (implement block convention)
        for method in &impl_block.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| {
                    resolve_type_expr_full(
                        t,
                        &self.analyzed.entity_registry,
                        &self.type_metadata,
                        interner,
                        &self.analyzed.name_table,
                        module_id,
                    )
                })
                .unwrap_or(Type::Void);
            let sig = self.create_implement_method_signature(method, &self_vole_type);
            let func_key = if let Some(type_sym) = type_sym {
                self.func_registry
                    .intern_qualified(func_module, &[type_sym, method.name], interner)
            } else if let Some(type_id) = type_id {
                self.func_registry
                    .intern_with_prefix(type_id.name_id(), method.name, interner)
            } else {
                let method_name_str = interner.resolve(method.name);
                self.func_registry
                    .intern_raw_qualified(func_module, &[type_name.as_str(), method_name_str])
            };
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);
            if let Some(type_id) = type_id {
                let method_id = method_name_id(self.analyzed, interner, method.name)
                    .expect("implement method name_id should be registered");
                self.impl_method_infos.insert(
                    (type_id, method_id),
                    MethodInfo {
                        func_key,
                        return_type,
                    },
                );
            }
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            // Get TypeDefId for this type
            let type_def_id = match &impl_block.target_type {
                TypeExpr::Primitive(p) => {
                    let name_id = self.analyzed.name_table.primitives.from_ast(*p);
                    self.analyzed.entity_registry.type_by_name(name_id)
                }
                TypeExpr::Named(sym) => {
                    let name_id = self.analyzed.name_table.name_id(
                        self.analyzed.name_table.main_module(),
                        &[*sym],
                        interner,
                    );
                    name_id.and_then(|id| self.analyzed.entity_registry.type_by_name(id))
                }
                _ => None,
            };

            for method in &statics.methods {
                // Only register methods with bodies
                if method.body.is_none() {
                    continue;
                }

                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        resolve_type_expr_full(
                            t,
                            &self.analyzed.entity_registry,
                            &self.type_metadata,
                            interner,
                            &self.analyzed.name_table,
                            module_id,
                        )
                    })
                    .unwrap_or(Type::Void);

                // Create signature without self parameter
                let sig = self.create_static_method_signature(method);

                // Function key: TypeName::methodName
                let func_key = self.func_registry.intern_raw_qualified(
                    func_module,
                    &[type_name.as_str(), interner.resolve(method.name)],
                );
                let display_name = self.func_registry.display(func_key);
                let func_id = self.jit.declare_function(&display_name, &sig);
                self.func_registry.set_func_id(func_key, func_id);

                // Register in static_method_infos for codegen lookup
                if let Some(type_def_id) = type_def_id {
                    let method_name_id = method_name_id(self.analyzed, interner, method.name);
                    if let Some(method_name_id) = method_name_id {
                        self.static_method_infos.insert(
                            (type_def_id, method_name_id),
                            MethodInfo {
                                func_key,
                                return_type,
                            },
                        );
                    }
                }
            }
        }
    }

    /// Compile implement block methods (second pass)
    pub(super) fn compile_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
    ) -> Result<(), String> {
        let module_id = self.analyzed.name_table.main_module();
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return Ok(()); // Unsupported type for implement block
        };

        // Get the Vole type for `self` binding
        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        let self_vole_type = match &impl_block.target_type {
            TypeExpr::Primitive(p) => Type::from_primitive(*p),
            TypeExpr::Named(sym) => self
                .type_metadata
                .get(sym)
                .map(|m| m.vole_type.clone())
                .unwrap_or(Type::Error),
            _ => resolve_type_expr_full(
                &impl_block.target_type,
                &self.analyzed.entity_registry,
                &self.type_metadata,
                &self.analyzed.interner,
                &self.analyzed.name_table,
                module_id,
            ),
        };
        let type_sym = self.get_type_name_symbol(&impl_block.target_type);
        let func_module = if matches!(&impl_block.target_type, TypeExpr::Primitive(_)) {
            self.func_registry.builtin_module()
        } else {
            self.func_registry.main_module()
        };

        for method in &impl_block.methods {
            let method_key = TypeId::from_type(&self_vole_type, &self.analyzed.type_table)
                .and_then(|type_id| {
                    let method_id =
                        method_name_id(self.analyzed, &self.analyzed.interner, method.name)?;
                    self.impl_method_infos.get(&(type_id, method_id)).cloned()
                });
            self.compile_implement_method(
                method,
                &type_name,
                type_sym,
                func_module,
                &self_vole_type,
                method_key,
            )?;
        }

        // Compile static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            let interner = self.analyzed.interner.clone();
            self.compile_implement_statics(statics, &type_name, func_module, None, &interner)?;
        }

        Ok(())
    }

    /// Compile ONLY the static methods from an implement block (for module programs)
    pub(super) fn compile_implement_statics_only(
        &mut self,
        impl_block: &ImplementBlock,
        module_path: Option<&str>,
        interner: &Interner,
    ) -> Result<(), String> {
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return Ok(()); // Unsupported type
        };
        let func_module = if matches!(&impl_block.target_type, TypeExpr::Primitive(_)) {
            self.func_registry.builtin_module()
        } else {
            self.func_registry.main_module()
        };

        if let Some(ref statics) = impl_block.statics {
            self.compile_implement_statics(
                statics,
                &type_name,
                func_module,
                module_path,
                interner,
            )?;
        }
        Ok(())
    }

    /// Compile static methods from an implement block's statics section
    fn compile_implement_statics(
        &mut self,
        statics: &StaticsBlock,
        type_name: &str,
        func_module: ModuleId,
        module_path: Option<&str>,
        interner: &Interner,
    ) -> Result<(), String> {
        let module_id = self.analyzed.name_table.main_module();

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Look up the registered function
            let method_name_str = interner.resolve(method.name);
            let func_key = self
                .func_registry
                .intern_raw_qualified(func_module, &[type_name, method_name_str]);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                format!(
                    "Internal error: static method {}::{} not declared",
                    type_name, method_name_str
                )
            })?;

            // Resolve return type for context (needed for proper literal type inference)
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| {
                    resolve_type_expr_full(
                        t,
                        &self.analyzed.entity_registry,
                        &self.type_metadata,
                        interner,
                        &self.analyzed.name_table,
                        module_id,
                    )
                })
                .unwrap_or(Type::Void);

            // Create signature (no self parameter)
            let sig = self.create_static_method_signature(method);
            self.jit.ctx.func.signature = sig;

            // Collect param types
            let param_types: Vec<types::Type> = method
                .params
                .iter()
                .map(|p| {
                    type_to_cranelift(
                        &resolve_type_expr_full(
                            &p.ty,
                            &self.analyzed.entity_registry,
                            &self.type_metadata,
                            interner,
                            &self.analyzed.name_table,
                            module_id,
                        ),
                        self.pointer_type,
                    )
                })
                .collect();
            let param_vole_types: Vec<Type> = method
                .params
                .iter()
                .map(|p| {
                    resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.entity_registry,
                        &self.type_metadata,
                        interner,
                        &self.analyzed.name_table,
                        module_id,
                    )
                })
                .collect();
            let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

            // Get source file pointer before borrowing ctx.func
            let source_file_ptr = self.source_file_ptr();

            // Create function builder
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);

                // Build variables map (no self for static methods)
                let mut variables = HashMap::new();

                // Get entry block params (just user params, no self)
                let params = builder.block_params(entry_block).to_vec();

                // Bind parameters
                for (((name, ty), vole_ty), val) in param_names
                    .iter()
                    .zip(param_types.iter())
                    .zip(param_vole_types.iter())
                    .zip(params.iter())
                {
                    let var = builder.declare_var(*ty);
                    builder.def_var(var, *val);
                    variables.insert(*name, (var, vole_ty.clone()));
                }

                // Compile method body
                let mut cf_ctx = ControlFlowCtx::new();
                let mut ctx = CompileCtx {
                    analyzed: self.analyzed,
                    interner: &self.analyzed.interner,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_registry: &mut self.func_registry,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
                    type_metadata: &self.type_metadata,
                    impl_method_infos: &self.impl_method_infos,
                    static_method_infos: &self.static_method_infos,
                    interface_vtables: &self.interface_vtables,
                    current_function_return_type: Some(return_type.clone()),
                    native_registry: &self.native_registry,
                    current_module: module_path,
                    generic_calls: &self.analyzed.generic_calls,
                    monomorph_cache: &self.analyzed.monomorph_cache,
                };
                let terminated =
                    compile_block(&mut builder, body, &mut variables, &mut cf_ctx, &mut ctx)?;

                // Add implicit return if no explicit return
                if !terminated {
                    builder.ins().return_(&[]);
                }

                builder.seal_all_blocks();
                builder.finalize();
            }

            // Define the function
            self.jit.define_function(func_id)?;
            self.jit.clear();
        }

        Ok(())
    }

    /// Compile a method from an implement block
    fn compile_implement_method(
        &mut self,
        method: &FuncDecl,
        type_name: &str,
        type_sym: Option<Symbol>,
        func_module: ModuleId,
        self_vole_type: &Type,
        method_info: Option<MethodInfo>,
    ) -> Result<(), String> {
        let module_id = self.analyzed.name_table.main_module();
        let func_key = if let Some(info) = method_info {
            info.func_key
        } else if let Some(type_sym) = type_sym {
            self.func_registry.intern_qualified(
                func_module,
                &[type_sym, method.name],
                &self.analyzed.interner,
            )
        } else if let Some(type_id) = TypeId::from_type(self_vole_type, &self.analyzed.type_table) {
            self.func_registry.intern_with_prefix(
                type_id.name_id(),
                method.name,
                &self.analyzed.interner,
            )
        } else {
            let method_name_str = self.analyzed.interner.resolve(method.name);
            self.func_registry
                .intern_raw_qualified(func_module, &[type_name, method_name_str])
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: implement method {} not declared", display)
        })?;

        // Create method signature with correct self type (primitives use their type, not pointer)
        let sig = self.create_implement_method_signature(method, self_vole_type);
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self
        let self_cranelift_type = type_to_cranelift(self_vole_type, self.pointer_type);

        // Clone type for the closure
        let self_type = self_vole_type.clone();

        // Helper to resolve param type, substituting Self with the concrete type
        let resolve_param_type = |ty: &TypeExpr| -> Type {
            if matches!(ty, TypeExpr::SelfType) {
                self_type.clone()
            } else {
                resolve_type_expr_full(
                    ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            }
        };

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| type_to_cranelift(&resolve_param_type(&p.ty), self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_param_type(&p.ty))
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter (using correct type for primitives)
            let self_sym = self
                .analyzed
                .interner
                .lookup("self")
                .ok_or_else(|| "Internal error: 'self' keyword not interned".to_string())?;
            let self_var = builder.declare_var(self_cranelift_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, self_type));

            // Bind remaining parameters
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compute the method's return type for proper union wrapping
            let method_return_type = method.return_type.as_ref().map(|t| {
                resolve_type_expr_full(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            });

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: method_return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
            };
            let terminated = compile_block(
                &mut builder,
                &method.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            if !terminated {
                // Return void if no explicit return
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit
            .module
            .define_function(func_id, &mut self.jit.ctx)
            .map_err(|e| e.to_string())?;
        self.jit.module.clear_context(&mut self.jit.ctx);

        Ok(())
    }

    /// Compile a single method
    fn compile_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> Result<(), String> {
        let type_name_str = self.analyzed.interner.resolve(type_name);
        let method_name_str = self.analyzed.interner.resolve(method.name);
        let module_id = self.analyzed.name_table.main_module();

        let func_key = metadata
            .method_infos
            .get(
                &method_name_id(self.analyzed, &self.analyzed.interner, method.name)
                    .expect("method name_id should be registered"),
            )
            .map(|info| info.func_key)
            .ok_or_else(|| {
                format!(
                    "Internal error: method {} not registered on {}",
                    method_name_str, type_name_str
                )
            })?;
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: method {} not declared", display)
        })?;

        // Create method signature (self + params)
        let sig = self.create_method_signature(method);
        self.jit.ctx.func.signature = sig;

        // Clone metadata for the closure (needs to be before resolve_param_type closure)
        let self_vole_type = metadata.vole_type.clone();

        // Helper to resolve param type, substituting Self with the concrete type
        let resolve_param_type = |ty: &TypeExpr| -> Type {
            if matches!(ty, TypeExpr::SelfType) {
                self_vole_type.clone()
            } else {
                resolve_type_expr_full(
                    ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            }
        };

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| type_to_cranelift(&resolve_param_type(&p.ty), self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_param_type(&p.ty))
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter
            // Note: "self" should already be interned during parsing of method bodies
            let self_sym = self
                .analyzed
                .interner
                .lookup("self")
                .ok_or_else(|| "Internal error: 'self' keyword not interned".to_string())?;
            let self_var = builder.declare_var(self.pointer_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, self_vole_type));

            // Bind remaining parameters
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: None, // Methods don't use raise statements yet
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
            };
            let terminated = compile_block(
                &mut builder,
                &method.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile a default method from an interface, monomorphized for a concrete type
    fn compile_default_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> Result<(), String> {
        let type_name_str = self.analyzed.interner.resolve(type_name);
        let method_name_str = self.analyzed.interner.resolve(method.name);
        let module_id = self.analyzed.name_table.main_module();

        let func_key = metadata
            .method_infos
            .get(
                &method_name_id(self.analyzed, &self.analyzed.interner, method.name)
                    .expect("method name_id should be registered"),
            )
            .map(|info| info.func_key)
            .ok_or_else(|| {
                format!(
                    "Internal error: default method {} not registered on {}",
                    method_name_str, type_name_str
                )
            })?;
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: default method {} not declared", display)
        })?;

        // Create method signature (self + params)
        let sig = self.create_interface_method_signature(method);
        self.jit.ctx.func.signature = sig;

        // Clone metadata for the closure - self has the concrete type!
        let self_vole_type = metadata.vole_type.clone();

        // Helper to resolve param type, substituting Self with the concrete type
        let resolve_param_type = |ty: &TypeExpr| -> Type {
            if matches!(ty, TypeExpr::SelfType) {
                self_vole_type.clone()
            } else {
                resolve_type_expr_full(
                    ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            }
        };

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| type_to_cranelift(&resolve_param_type(&p.ty), self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_param_type(&p.ty))
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter with the concrete type
            let self_sym = self
                .analyzed
                .interner
                .lookup("self")
                .ok_or_else(|| "Internal error: 'self' keyword not interned".to_string())?;
            let self_var = builder.declare_var(self.pointer_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, self_vole_type));

            // Bind remaining parameters
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile method body (must exist for default methods)
            let body = method.body.as_ref().ok_or_else(|| {
                format!(
                    "Internal error: default method {} has no body",
                    method_name_str
                )
            })?;

            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: None, // Default methods don't use raise statements yet
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
            };
            let terminated =
                compile_block(&mut builder, body, &mut variables, &mut cf_ctx, &mut ctx)?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile static methods from a statics block
    fn compile_static_methods(
        &mut self,
        statics: &StaticsBlock,
        type_name: Symbol,
    ) -> Result<(), String> {
        let module_id = self.analyzed.name_table.main_module();
        let func_module = self.func_registry.main_module();

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Look up the registered function
            let func_key = self.func_registry.intern_qualified(
                func_module,
                &[type_name, method.name],
                &self.analyzed.interner,
            );
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                let type_name_str = self.analyzed.interner.resolve(type_name);
                let method_name_str = self.analyzed.interner.resolve(method.name);
                format!(
                    "Internal error: static method {}::{} not declared",
                    type_name_str, method_name_str
                )
            })?;

            // Create signature (no self parameter)
            let sig = self.create_static_method_signature(method);
            self.jit.ctx.func.signature = sig;

            // Collect param types
            let param_types: Vec<types::Type> = method
                .params
                .iter()
                .map(|p| {
                    type_to_cranelift(
                        &resolve_type_expr_full(
                            &p.ty,
                            &self.analyzed.entity_registry,
                            &self.type_metadata,
                            &self.analyzed.interner,
                            &self.analyzed.name_table,
                            module_id,
                        ),
                        self.pointer_type,
                    )
                })
                .collect();
            let param_vole_types: Vec<Type> = method
                .params
                .iter()
                .map(|p| {
                    resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.entity_registry,
                        &self.type_metadata,
                        &self.analyzed.interner,
                        &self.analyzed.name_table,
                        module_id,
                    )
                })
                .collect();
            let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

            // Get source file pointer before borrowing ctx.func
            let source_file_ptr = self.source_file_ptr();

            // Create function builder
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);

                // Build variables map (no self for static methods)
                let mut variables = HashMap::new();

                // Get entry block params (just user params, no self)
                let params = builder.block_params(entry_block).to_vec();

                // Bind parameters
                for (((name, ty), vole_ty), val) in param_names
                    .iter()
                    .zip(param_types.iter())
                    .zip(param_vole_types.iter())
                    .zip(params.iter())
                {
                    let var = builder.declare_var(*ty);
                    builder.def_var(var, *val);
                    variables.insert(*name, (var, vole_ty.clone()));
                }

                // Compile method body
                let mut cf_ctx = ControlFlowCtx::new();
                let mut ctx = CompileCtx {
                    analyzed: self.analyzed,
                    interner: &self.analyzed.interner,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_registry: &mut self.func_registry,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
                    type_metadata: &self.type_metadata,
                    impl_method_infos: &self.impl_method_infos,
                    static_method_infos: &self.static_method_infos,
                    interface_vtables: &self.interface_vtables,
                    current_function_return_type: None,
                    native_registry: &self.native_registry,
                    current_module: None,
                    generic_calls: &self.analyzed.generic_calls,
                    monomorph_cache: &self.analyzed.monomorph_cache,
                };
                let terminated =
                    compile_block(&mut builder, body, &mut variables, &mut cf_ctx, &mut ctx)?;

                // Add implicit return if no explicit return
                if !terminated {
                    builder.ins().return_(&[]);
                }

                builder.seal_all_blocks();
                builder.finalize();
            }

            // Define the function
            self.jit.define_function(func_id)?;
            self.jit.clear();
        }

        Ok(())
    }
}
