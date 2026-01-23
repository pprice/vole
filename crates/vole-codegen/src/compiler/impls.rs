use std::collections::HashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};
use cranelift_module::Module;

use super::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::{Compiler, ControlFlowCtx, SelfParam, TypeResolver};
use crate::stmt::compile_func_body_with_params;
use crate::types::{
    CodegenCtx, FunctionCtx, MethodInfo, TypeMetadata, method_name_id_with_interner,
    resolve_type_expr_to_id, type_id_to_cranelift,
};
use vole_frontend::ast::PrimitiveType as AstPrimitive;
use vole_frontend::{
    ClassDecl, Expr, FuncDecl, ImplementBlock, InterfaceMethod, Interner, RecordDecl, StaticsBlock,
    Symbol, TypeExpr,
};
use vole_identity::ModuleId;
use vole_sema::type_arena::TypeId;

/// Get the canonical name for an AST primitive type
fn primitive_type_name(p: AstPrimitive) -> &'static str {
    match p {
        AstPrimitive::I8 => "i8",
        AstPrimitive::I16 => "i16",
        AstPrimitive::I32 => "i32",
        AstPrimitive::I64 => "i64",
        AstPrimitive::I128 => "i128",
        AstPrimitive::U8 => "u8",
        AstPrimitive::U16 => "u16",
        AstPrimitive::U32 => "u32",
        AstPrimitive::U64 => "u64",
        AstPrimitive::F32 => "f32",
        AstPrimitive::F64 => "f64",
        AstPrimitive::Bool => "bool",
        AstPrimitive::String => "string",
    }
}

impl Compiler<'_> {
    /// Compile methods for a class
    pub(super) fn compile_class_methods(
        &mut self,
        class: &ClassDecl,
        program: &vole_frontend::Program,
    ) -> Result<(), String> {
        // Skip generic classes - they're compiled via monomorphized instances
        if !class.type_params.is_empty() {
            return Ok(());
        }

        let metadata = self
            .state
            .type_metadata
            .get(&class.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: class {} not registered",
                    self.query().resolve_symbol(class.name)
                )
            })?;

        for method in &class.methods {
            self.compile_method(method, class.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();

        // Collect interface names using query (avoids borrow conflicts with compile_default_method)
        let interface_names: Vec<Symbol> = {
            let query = self.query();
            query
                .try_name_id(query.main_module(), &[class.name])
                .and_then(|class_name_id| query.try_type_def_id(class_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            query
                                .last_segment(interface_def.name_id)
                                .and_then(|name_str| query.try_symbol(&name_str))
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        // Compile default methods for each interface
        for interface_name in interface_names {
            if let Some(interface_decl) = self.find_interface_decl(program, interface_name) {
                for method in &interface_decl.methods {
                    if method.body.is_some() && !direct_methods.contains(&method.name) {
                        self.compile_default_method(method, class.name, &metadata)?;
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
        program: &vole_frontend::Program,
    ) -> Result<(), String> {
        // Skip generic records - they're compiled via monomorphized instances
        if !record.type_params.is_empty() {
            return Ok(());
        }

        let metadata = self
            .state
            .type_metadata
            .get(&record.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: record {} not registered",
                    self.query().resolve_symbol(record.name)
                )
            })?;

        for method in &record.methods {
            self.compile_method(method, record.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();

        // Collect interface names using query (avoids borrow conflicts with compile_default_method)
        let interface_names: Vec<Symbol> = {
            let query = self.query();
            query
                .try_name_id(query.main_module(), &[record.name])
                .and_then(|record_name_id| query.try_type_def_id(record_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            query
                                .last_segment(interface_def.name_id)
                                .and_then(|name_str| query.try_symbol(&name_str))
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        // Compile default methods for each interface
        for interface_name in interface_names {
            if let Some(interface_decl) = self.find_interface_decl(program, interface_name) {
                for method in &interface_decl.methods {
                    if method.body.is_some() && !direct_methods.contains(&method.name) {
                        self.compile_default_method(method, record.name, &metadata)?;
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
            TypeExpr::Primitive(p) => Some(primitive_type_name(*p).to_string()),
            TypeExpr::Named(sym) => Some(self.query().resolve_symbol(*sym).to_string()),
            _ => None,
        }
    }

    /// Register implement block methods (first pass)
    pub(super) fn register_implement_block(&mut self, impl_block: &ImplementBlock) {
        self.register_implement_block_with_interner(impl_block, &self.analyzed.interner.clone())
    }

    /// Register ONLY static methods from implement block with a specific interner (for module programs)
    /// This is used when compiling modules where we want to skip instance methods
    /// but still need to register and compile statics like `i32::default_value`.
    pub(super) fn register_implement_statics_only_with_interner(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
    ) {
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return; // Unsupported type for implement block
        };
        let func_module = if matches!(&impl_block.target_type, TypeExpr::Primitive(_)) {
            self.func_registry.builtin_module()
        } else {
            self.func_registry.main_module()
        };

        // Skip if no statics block
        let Some(ref statics) = impl_block.statics else {
            return;
        };

        // Get TypeDefId for this type
        let type_def_id = {
            let name_table = self.analyzed.name_table();
            match &impl_block.target_type {
                TypeExpr::Primitive(p) => {
                    let name_id = name_table.primitives.from_ast(*p);
                    self.query().try_type_def_id(name_id)
                }
                TypeExpr::Named(sym) => {
                    let name_id = name_table.name_id(self.query().main_module(), &[*sym], interner);
                    name_id.and_then(|id| self.query().try_type_def_id(id))
                }
                _ => None,
            }
        };

        for method in &statics.methods {
            // Only register methods with bodies
            if method.body.is_none() {
                continue;
            }

            // Create signature without self parameter
            let sig = self.build_signature(
                &method.params,
                method.return_type.as_ref(),
                SelfParam::None,
                TypeResolver::Query,
            );

            // Function key: TypeName::methodName
            let func_key = self.func_registry.intern_raw_qualified(
                func_module,
                &[type_name.as_str(), interner.resolve(method.name)],
            );
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);

            // Register in static_method_infos for codegen lookup
            if let Some(type_def_id) = type_def_id
                && let Some(method_name_id) =
                    method_name_id_with_interner(self.analyzed, interner, method.name)
            {
                self.state
                    .static_method_infos
                    .insert((type_def_id, method_name_id), MethodInfo { func_key });
            }
        }
    }

    /// Import ONLY static methods from implement block with a specific interner (for module reuse)
    /// This is used when importing pre-compiled modules - it uses Linkage::Import instead of Export.
    pub(super) fn import_implement_statics_only_with_interner(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
    ) {
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return; // Unsupported type for implement block
        };
        let func_module = if matches!(&impl_block.target_type, TypeExpr::Primitive(_)) {
            self.func_registry.builtin_module()
        } else {
            self.func_registry.main_module()
        };

        // Skip if no statics block
        let Some(ref statics) = impl_block.statics else {
            return;
        };

        // Get TypeDefId for this type
        let type_def_id = {
            let name_table = self.analyzed.name_table();
            match &impl_block.target_type {
                TypeExpr::Primitive(p) => {
                    let name_id = name_table.primitives.from_ast(*p);
                    self.query().try_type_def_id(name_id)
                }
                TypeExpr::Named(sym) => {
                    let name_id = name_table.name_id(self.query().main_module(), &[*sym], interner);
                    name_id.and_then(|id| self.query().try_type_def_id(id))
                }
                _ => None,
            }
        };

        for method in &statics.methods {
            // Only import methods with bodies (skip external declarations)
            if method.body.is_none() {
                continue;
            }

            // Create signature without self parameter
            let sig = self.build_signature(
                &method.params,
                method.return_type.as_ref(),
                SelfParam::None,
                TypeResolver::Query,
            );

            // Function key: TypeName::methodName
            let func_key = self.func_registry.intern_raw_qualified(
                func_module,
                &[type_name.as_str(), interner.resolve(method.name)],
            );
            let display_name = self.func_registry.display(func_key);
            // Use import_function (Linkage::Import) instead of declare_function
            let func_id = self.jit.import_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);

            // Register in static_method_infos for codegen lookup
            if let Some(type_def_id) = type_def_id
                && let Some(method_name_id) =
                    method_name_id_with_interner(self.analyzed, interner, method.name)
            {
                self.state
                    .static_method_infos
                    .insert((type_def_id, method_name_id), MethodInfo { func_key });
            }
        }
    }

    /// Register implement block methods with a specific interner (for module programs)
    pub(super) fn register_implement_block_with_interner(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
    ) {
        let module_id = self.query().main_module();
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

        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        // Get type_id directly from metadata to avoid to_type() conversion
        let (self_type_id, impl_type_id) = match &impl_block.target_type {
            TypeExpr::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                let type_id = self.analyzed.type_arena().primitive(prim_type);
                let impl_id = self.impl_type_id_from_type_id(type_id);
                (type_id, impl_id)
            }
            TypeExpr::Named(sym) => {
                let metadata = self.state.type_metadata.get(sym).unwrap_or_else(|| {
                    panic!(
                        "INTERNAL ERROR: implement block target type not in type_metadata\n\
                         sym: {:?}",
                        sym
                    )
                });
                // Use TypeId directly
                let impl_id = self.impl_type_id_from_type_id(metadata.vole_type);
                (metadata.vole_type, impl_id)
            }
            _ => {
                let name_table = self.analyzed.name_table();
                let type_id = resolve_type_expr_to_id(
                    &impl_block.target_type,
                    self.analyzed.entity_registry(),
                    &self.state.type_metadata,
                    interner,
                    &name_table,
                    module_id,
                    self.analyzed.type_arena_ref(),
                );
                drop(name_table);
                let impl_id = self.impl_type_id_from_type_id(type_id);
                (type_id, impl_id)
            }
        };

        // Declare methods as functions: TypeName::methodName (implement block convention)
        for method in &impl_block.methods {
            let sig = self.build_signature(
                &method.params,
                method.return_type.as_ref(),
                SelfParam::TypedId(self_type_id),
                TypeResolver::Query,
            );
            let func_key = if let Some(type_sym) = type_sym {
                self.func_registry
                    .intern_qualified(func_module, &[type_sym, method.name], interner)
            } else if let Some(impl_id) = impl_type_id {
                self.func_registry
                    .intern_with_prefix(impl_id.name_id(), method.name, interner)
            } else {
                let method_name_str = interner.resolve(method.name);
                self.func_registry
                    .intern_raw_qualified(func_module, &[type_name.as_str(), method_name_str])
            };
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);
            if let Some(impl_id) = impl_type_id {
                let method_id = method_name_id_with_interner(self.analyzed, interner, method.name)
                    .expect("implement method name_id should be registered");
                self.state
                    .impl_method_infos
                    .insert((impl_id, method_id), MethodInfo { func_key });
            }
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            // Get TypeDefId for this type
            let type_def_id = {
                let name_table = self.analyzed.name_table();
                match &impl_block.target_type {
                    TypeExpr::Primitive(p) => {
                        let name_id = name_table.primitives.from_ast(*p);
                        self.query().try_type_def_id(name_id)
                    }
                    TypeExpr::Named(sym) => {
                        let name_id =
                            name_table.name_id(self.query().main_module(), &[*sym], interner);
                        name_id.and_then(|id| self.query().try_type_def_id(id))
                    }
                    _ => None,
                }
            };

            for method in &statics.methods {
                // Only register methods with bodies
                if method.body.is_none() {
                    continue;
                }

                // Create signature without self parameter
                let sig = self.build_signature(
                    &method.params,
                    method.return_type.as_ref(),
                    SelfParam::None,
                    TypeResolver::Query,
                );

                // Function key: TypeName::methodName
                let func_key = self.func_registry.intern_raw_qualified(
                    func_module,
                    &[type_name.as_str(), interner.resolve(method.name)],
                );
                let display_name = self.func_registry.display(func_key);
                let func_id = self.jit.declare_function(&display_name, &sig);
                self.func_registry.set_func_id(func_key, func_id);

                // Register in static_method_infos for codegen lookup
                if let Some(type_def_id) = type_def_id
                    && let Some(method_name_id) =
                        method_name_id_with_interner(self.analyzed, interner, method.name)
                {
                    self.state
                        .static_method_infos
                        .insert((type_def_id, method_name_id), MethodInfo { func_key });
                }
            }
        }
    }

    /// Compile implement block methods (second pass)
    pub(super) fn compile_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
    ) -> Result<(), String> {
        let module_id = self.query().main_module();
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return Ok(()); // Unsupported type for implement block
        };

        // Get the TypeId for `self` binding
        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        let self_type_id = match &impl_block.target_type {
            TypeExpr::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                self.analyzed.type_arena().primitive(prim_type)
            }
            TypeExpr::Named(sym) => self
                .state
                .type_metadata
                .get(sym)
                .map(|m| m.vole_type)
                .unwrap_or_else(|| {
                    panic!(
                        "INTERNAL ERROR: implement block self type not in type_metadata\n\
                         sym: {:?}",
                        sym
                    )
                }),
            _ => {
                let name_table = self.analyzed.name_table();
                resolve_type_expr_to_id(
                    &impl_block.target_type,
                    self.analyzed.entity_registry(),
                    &self.state.type_metadata,
                    &self.analyzed.interner,
                    &name_table,
                    module_id,
                    self.analyzed.type_arena_ref(),
                )
            }
        };
        let type_sym = self.get_type_name_symbol(&impl_block.target_type);
        let func_module = if matches!(&impl_block.target_type, TypeExpr::Primitive(_)) {
            self.func_registry.builtin_module()
        } else {
            self.func_registry.main_module()
        };

        // Get impl_type_id for method lookup
        let impl_type_id = self.impl_type_id_from_type_id(self_type_id);

        for method in &impl_block.methods {
            let method_key = impl_type_id.and_then(|type_id| {
                let method_id = self.method_name_id(method.name);
                self.state
                    .impl_method_infos
                    .get(&(type_id, method_id))
                    .copied()
            });
            self.compile_implement_method(
                method,
                &type_name,
                type_sym,
                func_module,
                self_type_id,
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

    /// Compile static methods from an implement block's statics section (TypeId-native)
    fn compile_implement_statics(
        &mut self,
        statics: &StaticsBlock,
        type_name: &str,
        func_module: ModuleId,
        module_path: Option<&str>,
        interner: &Interner,
    ) -> Result<(), String> {
        let module_id = self.query().main_module();

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

            // Resolve return type as TypeId for context (needed for proper literal type inference)
            let return_type_id = {
                let name_table = self.analyzed.name_table();
                method.return_type.as_ref().map(|t| {
                    resolve_type_expr_to_id(
                        t,
                        self.analyzed.entity_registry(),
                        &self.state.type_metadata,
                        interner,
                        &name_table,
                        module_id,
                        self.analyzed.type_arena_ref(),
                    )
                })
            };

            // Create signature (no self parameter)
            let sig = self.build_signature(
                &method.params,
                method.return_type.as_ref(),
                SelfParam::None,
                TypeResolver::Query,
            );
            self.jit.ctx.func.signature = sig;

            // Collect param types as TypeId (resolve once, use for both Cranelift type and variables)
            let param_type_ids: Vec<TypeId> = {
                let name_table = self.analyzed.name_table();
                method
                    .params
                    .iter()
                    .map(|p| {
                        resolve_type_expr_to_id(
                            &p.ty,
                            self.analyzed.entity_registry(),
                            &self.state.type_metadata,
                            interner,
                            &name_table,
                            module_id,
                            self.analyzed.type_arena_ref(),
                        )
                    })
                    .collect()
            };
            let param_cranelift_types: Vec<types::Type> = {
                let arena = self.analyzed.type_arena();
                param_type_ids
                    .iter()
                    .map(|&id| type_id_to_cranelift(id, &arena, self.pointer_type))
                    .collect()
            };
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

                // Bind parameters (using TypeId directly)
                for (((name, ty), type_id), val) in param_names
                    .iter()
                    .zip(param_cranelift_types.iter())
                    .zip(param_type_ids.iter())
                    .zip(params.iter())
                {
                    let var = builder.declare_var(*ty);
                    builder.def_var(var, *val);
                    variables.insert(*name, (var, *type_id));
                }

                // Compile method body
                let mut cf_ctx = ControlFlowCtx::default();

                // Create split contexts - use module context if compiling module code
                let function_ctx = if let Some(path) = module_path {
                    let name_table = self.analyzed.name_table();
                    if let Some(mod_id) = name_table.module_id_if_known(path) {
                        FunctionCtx::module(return_type_id, mod_id)
                    } else {
                        FunctionCtx::main(return_type_id)
                    }
                } else {
                    FunctionCtx::main(return_type_id)
                };
                let env = compile_env!(self, source_file_ptr);
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let (terminated, expr_value) = compile_func_body_with_params(
                    &mut builder,
                    body,
                    &mut variables,
                    &mut cf_ctx,
                    &mut codegen_ctx,
                    &function_ctx,
                    &env,
                    None,
                    None,
                )?;

                // Add implicit return if no explicit return
                if let Some(value) = expr_value {
                    builder.ins().return_(&[value.value]);
                } else if !terminated {
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

    /// Compile a method from an implement block (TypeId-native version)
    fn compile_implement_method(
        &mut self,
        method: &FuncDecl,
        type_name: &str,
        type_sym: Option<Symbol>,
        func_module: ModuleId,
        self_type_id: TypeId,
        method_info: Option<MethodInfo>,
    ) -> Result<(), String> {
        let module_id = self.query().main_module();
        let func_key = if let Some(info) = method_info {
            info.func_key
        } else if let Some(type_sym) = type_sym {
            self.intern_func(func_module, &[type_sym, method.name])
        } else if let Some(impl_id) = self.impl_type_id_from_type_id(self_type_id) {
            self.intern_func_prefixed(impl_id.name_id(), method.name)
        } else {
            let method_name_str = self.resolve_symbol(method.name);
            self.func_registry
                .intern_raw_qualified(func_module, &[type_name, &method_name_str])
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: implement method {} not declared", display)
        })?;

        // Create method signature with correct self type (primitives use their type, not pointer)
        let sig = self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::TypedId(self_type_id),
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self (using TypeId)
        let self_cranelift_type =
            type_id_to_cranelift(self_type_id, &self.analyzed.type_arena(), self.pointer_type);

        // Build params: Vec<(Symbol, TypeId, Type)>
        // First collect type IDs (which may access arena internally)
        let param_info: Vec<(Symbol, TypeId)> = {
            let name_table = self.analyzed.name_table();
            method
                .params
                .iter()
                .map(|p| {
                    let type_id = if matches!(&p.ty, TypeExpr::SelfType) {
                        self_type_id
                    } else {
                        resolve_type_expr_to_id(
                            &p.ty,
                            self.analyzed.entity_registry(),
                            &self.state.type_metadata,
                            &self.analyzed.interner,
                            &name_table,
                            module_id,
                            self.analyzed.type_arena_ref(),
                        )
                    };
                    (p.name, type_id)
                })
                .collect()
        };
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
            param_info
                .into_iter()
                .map(|(name, type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, &arena_ref, self.pointer_type);
                    (name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Compute the method's return type as TypeId for proper union wrapping
        let method_return_type_id = {
            let name_table = self.analyzed.name_table();
            method.return_type.as_ref().map(|t| {
                resolve_type_expr_to_id(
                    t,
                    self.analyzed.entity_registry(),
                    &self.state.type_metadata,
                    &self.analyzed.interner,
                    &name_table,
                    module_id,
                    self.analyzed.type_arena_ref(),
                )
            })
        };

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let function_ctx = FunctionCtx::main(method_return_type_id);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let self_binding = (self_sym, self_type_id, self_cranelift_type);
            let config = FunctionCompileConfig::method(
                &method.body,
                params,
                self_binding,
                method_return_type_id,
            );
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &function_ctx,
                &env,
                config,
            )?;
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
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = self.query().resolve_symbol(method.name).to_string();
        let module_id = self.query().main_module();

        let method_name_id = self.method_name_id(method.name);
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            format!(
                "Internal error: method {} not registered on {}",
                method_name_str, type_name_str
            )
        })?;
        let func_key = method_info.func_key;
        // Look up return type from sema (removes redundant storage in MethodInfo)
        let return_type_id_from_sema = self
            .query()
            .method_return_type_by_id(metadata.type_def_id, method_name_id)
            .unwrap_or(TypeId::VOID);
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: method {} not declared", display)
        })?;

        // Create method signature (self + params) - use sema return type for inferred types
        let sig = self.build_signature_with_return_type_id(
            &method.params,
            Some(return_type_id_from_sema),
            SelfParam::Pointer,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Use TypeId directly for self binding
        let self_type_id = metadata.vole_type;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // First collect type IDs (which may access arena internally)
        let param_info: Vec<(Symbol, TypeId)> = {
            let query = self.query();
            let registry = query.registry();
            let interner = query.interner();
            let name_table = self.analyzed.name_table();
            let type_metadata = &self.state.type_metadata;
            let arena = self.analyzed.type_arena_ref();
            method
                .params
                .iter()
                .map(|p| {
                    let type_id = if matches!(&p.ty, TypeExpr::SelfType) {
                        self_type_id
                    } else {
                        resolve_type_expr_to_id(
                            &p.ty,
                            registry,
                            type_metadata,
                            interner,
                            &name_table,
                            module_id,
                            arena,
                        )
                    };
                    (p.name, type_id)
                })
                .collect()
        };
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
            param_info
                .into_iter()
                .map(|(name, type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, &arena_ref, self.pointer_type);
                    (name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();
        let method_return_type_id = Some(return_type_id_from_sema);

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let function_ctx = FunctionCtx::main(method_return_type_id);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
            let self_binding = (self_sym, self_type_id, self.pointer_type);
            let config = FunctionCompileConfig::method(
                &method.body,
                params,
                self_binding,
                method_return_type_id,
            );
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &function_ctx,
                &env,
                config,
            )?;
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
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = self.query().resolve_symbol(method.name).to_string();
        let module_id = self.query().main_module();

        let method_name_id = self.method_name_id(method.name);
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            format!(
                "Internal error: default method {} not registered on {}",
                method_name_str, type_name_str
            )
        })?;
        let func_key = method_info.func_key;
        // For default methods, the return type is explicit in the interface declaration
        // We can't look it up on the implementing type since it's inherited
        let return_type_id_from_sema = method
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_to_id(t))
            .unwrap_or(TypeId::VOID);
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: default method {} not declared", display)
        })?;

        // Create method signature (self + params) - use sema return type for inferred types
        let sig = self.build_signature_with_return_type_id(
            &method.params,
            Some(return_type_id_from_sema),
            SelfParam::Pointer,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Use TypeId directly for self binding
        let self_type_id = metadata.vole_type;

        // Collect param type IDs first, then convert to cranelift types
        let param_type_ids: Vec<TypeId> = {
            let query = self.query();
            let registry = query.registry();
            let interner = query.interner();
            let name_table = self.analyzed.name_table();
            let type_metadata = &self.state.type_metadata;
            let arena = self.analyzed.type_arena_ref();
            method
                .params
                .iter()
                .map(|p| {
                    if matches!(&p.ty, TypeExpr::SelfType) {
                        self_type_id
                    } else {
                        resolve_type_expr_to_id(
                            &p.ty,
                            registry,
                            type_metadata,
                            interner,
                            &name_table,
                            module_id,
                            arena,
                        )
                    }
                })
                .collect()
        };
        let param_types: Vec<types::Type> = {
            let arena_ref = self.analyzed.type_arena();
            param_type_ids
                .iter()
                .map(|&ty_id| type_id_to_cranelift(ty_id, &arena_ref, self.pointer_type))
                .collect()
        };
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Use the return type from sema (handles inferred types)
        let method_return_type_id = Some(return_type_id_from_sema);

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

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
            let self_var = builder.declare_var(self.pointer_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, metadata.vole_type));

            // Bind remaining parameters (TypeId-native)
            for (((name, ty), type_id), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_type_ids.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, *type_id));
            }

            // Compile method body (must exist for default methods)
            let body = method.body.as_ref().ok_or_else(|| {
                format!(
                    "Internal error: default method {} has no body",
                    method_name_str
                )
            })?;

            // Create split contexts
            let function_ctx = FunctionCtx::main(method_return_type_id);
            let env = compile_env!(self, source_file_ptr);
            let mut cf_ctx = ControlFlowCtx::default();
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
            let (terminated, expr_value) = compile_func_body_with_params(
                &mut builder,
                body,
                &mut variables,
                &mut cf_ctx,
                &mut codegen_ctx,
                &function_ctx,
                &env,
                None,
                None,
            )?;

            // Add implicit return if no explicit return
            if let Some(value) = expr_value {
                builder.ins().return_(&[value.value]);
            } else if !terminated {
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
        let module_id = self.query().main_module();
        let func_module = self.func_registry.main_module();

        // Get the TypeDefId for looking up method info
        let type_name_id = self.query().name_id(module_id, &[type_name]);
        let type_def_id = self.query().try_type_def_id(type_name_id);

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Look up the registered function
            let func_key = self.intern_func(func_module, &[type_name, method.name]);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                let type_name_str = self.query().resolve_symbol(type_name);
                let method_name_str = self.query().resolve_symbol(method.name);
                format!(
                    "Internal error: static method {}::{} not declared",
                    type_name_str, method_name_str
                )
            })?;

            // Get the return type from sema directly (removes redundant storage)
            let method_name_id = self.method_name_id(method.name);
            let return_type_id = type_def_id
                .and_then(|type_def_id| {
                    self.query()
                        .static_method_return_type_by_id(type_def_id, method_name_id)
                })
                .unwrap_or(TypeId::VOID);

            // Create signature using the (possibly inferred) return type
            let sig = self.build_signature_with_return_type_id(
                &method.params,
                Some(return_type_id),
                SelfParam::None,
                TypeResolver::Query,
            );
            self.jit.ctx.func.signature = sig;

            // Collect param type IDs first, then convert to cranelift types (TypeId-native)
            let param_type_ids: Vec<TypeId> = {
                let query = self.query();
                let type_metadata = &self.state.type_metadata;
                let arena = self.analyzed.type_arena_ref();
                let name_table = self.analyzed.name_table();
                method
                    .params
                    .iter()
                    .map(|p| {
                        resolve_type_expr_to_id(
                            &p.ty,
                            query.registry(),
                            type_metadata,
                            query.interner(),
                            &name_table,
                            module_id,
                            arena,
                        )
                    })
                    .collect()
            };
            let param_types: Vec<types::Type> = {
                let arena_ref = self.analyzed.type_arena();
                param_type_ids
                    .iter()
                    .map(|&ty_id| type_id_to_cranelift(ty_id, &arena_ref, self.pointer_type))
                    .collect()
            };
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

                // Bind parameters (TypeId-native)
                for (((name, ty), type_id), val) in param_names
                    .iter()
                    .zip(param_types.iter())
                    .zip(param_type_ids.iter())
                    .zip(params.iter())
                {
                    let var = builder.declare_var(*ty);
                    builder.def_var(var, *val);
                    variables.insert(*name, (var, *type_id));
                }

                // Create split contexts
                let function_ctx = FunctionCtx::main(None);
                let env = compile_env!(self, source_file_ptr);

                // Compile method body
                let mut cf_ctx = ControlFlowCtx::default();
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
                let (terminated, expr_value) = compile_func_body_with_params(
                    &mut builder,
                    body,
                    &mut variables,
                    &mut cf_ctx,
                    &mut codegen_ctx,
                    &function_ctx,
                    &env,
                    None,
                    None,
                )?;

                // Add implicit return if no explicit return
                if let Some(value) = expr_value {
                    builder.ins().return_(&[value.value]);
                } else if !terminated {
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

    /// Compile methods for a module class (uses module interner)
    pub(super) fn compile_module_class_methods(
        &mut self,
        class: &ClassDecl,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &HashMap<Symbol, Expr>,
    ) -> Result<(), String> {
        let type_name_str = module_interner.resolve(class.name);
        // Look up the actual module_id from the module_path (not main_module!)
        let module_id = self
            .analyzed
            .name_table()
            .module_id_if_known(module_path)
            .unwrap_or_else(|| self.query().main_module());
        let func_module_id = self.func_registry.main_module();

        // Find the type metadata by looking for the type name string
        let metadata = self
            .state
            .type_metadata
            .values()
            .find(|meta| {
                let arena = self.analyzed.type_arena();
                if let Some((type_def_id, _)) = arena.unwrap_class(meta.vole_type) {
                    let name_id = self.query().get_type(type_def_id).name_id;
                    self.analyzed
                        .name_table()
                        .last_segment_str(name_id)
                        .is_some_and(|name| name == type_name_str)
                } else {
                    false
                }
            })
            .cloned();

        let Some(metadata) = metadata else {
            tracing::warn!(type_name = %type_name_str, "Could not find metadata for module class");
            return Ok(());
        };

        // Compile instance methods
        for method in &class.methods {
            let method_name_str = module_interner.resolve(method.name);
            let func_key = self
                .func_registry
                .intern_raw_qualified(func_module_id, &[type_name_str, method_name_str]);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                format!(
                    "Internal error: method {}::{} not declared",
                    type_name_str, method_name_str
                )
            })?;

            // Create method signature with self parameter (use module interner)
            let sig = self.build_signature(
                &method.params,
                method.return_type.as_ref(),
                SelfParam::Pointer,
                TypeResolver::Interner(module_interner),
            );
            self.jit.ctx.func.signature = sig;

            // Resolve param type IDs (TypeId-native)
            let param_type_ids: Vec<TypeId> = {
                let type_metadata = &self.state.type_metadata;
                let arena = self.analyzed.type_arena_ref();
                let name_table = self.analyzed.name_table();
                method
                    .params
                    .iter()
                    .map(|p| {
                        resolve_type_expr_to_id(
                            &p.ty,
                            self.analyzed.entity_registry(),
                            type_metadata,
                            module_interner,
                            &name_table,
                            module_id,
                            arena,
                        )
                    })
                    .collect()
            };
            let param_types: Vec<types::Type> = {
                let arena_ref = self.analyzed.type_arena();
                param_type_ids
                    .iter()
                    .map(|&ty_id| type_id_to_cranelift(ty_id, &arena_ref, self.pointer_type))
                    .collect()
            };
            let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

            // Get source file pointer and self symbol (use module interner for method body)
            let source_file_ptr = self.source_file_ptr();
            let self_sym = module_interner
                .lookup("self")
                .expect("'self' should be interned in module");
            // Resolve return type (TypeId-native)
            let return_type_id = {
                let name_table = self.analyzed.name_table();
                method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        resolve_type_expr_to_id(
                            t,
                            self.analyzed.entity_registry(),
                            &self.state.type_metadata,
                            module_interner,
                            &name_table,
                            module_id,
                            self.analyzed.type_arena_ref(),
                        )
                    })
                    .unwrap_or(TypeId::VOID)
            };

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
                let self_var = builder.declare_var(self.pointer_type);
                builder.def_var(self_var, params[0]);
                variables.insert(self_sym, (self_var, metadata.vole_type));

                // Bind remaining parameters (TypeId-native)
                for (((name, ty), type_id), val) in param_names
                    .iter()
                    .zip(param_types.iter())
                    .zip(param_type_ids.iter())
                    .zip(params[1..].iter())
                {
                    let var = builder.declare_var(*ty);
                    builder.def_var(var, *val);
                    variables.insert(*name, (var, *type_id));
                }

                // Create split contexts (use module interner)
                let function_ctx = FunctionCtx::module(Some(return_type_id), module_id);
                let env = compile_env!(
                    self,
                    module_interner,
                    module_global_inits,
                    source_file_ptr,
                    module_id
                );

                // Compile method body
                let mut cf_ctx = ControlFlowCtx::default();
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
                let (terminated, expr_value) = compile_func_body_with_params(
                    &mut builder,
                    &method.body,
                    &mut variables,
                    &mut cf_ctx,
                    &mut codegen_ctx,
                    &function_ctx,
                    &env,
                    None,
                    None,
                )?;

                if let Some(value) = expr_value {
                    builder.ins().return_(&[value.value]);
                } else if !terminated {
                    builder.ins().return_(&[]);
                }

                builder.seal_all_blocks();
                builder.finalize();
            }

            // Define the function
            self.jit.define_function(func_id)?;
            self.jit.clear();
        }

        // Compile static methods
        if let Some(ref statics) = class.statics {
            for method in &statics.methods {
                let body = match &method.body {
                    Some(body) => body,
                    None => continue,
                };

                let method_name_str = module_interner.resolve(method.name);
                let func_key = self
                    .func_registry
                    .intern_raw_qualified(func_module_id, &[type_name_str, method_name_str]);
                let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                    format!(
                        "Internal error: static method {}::{} not declared",
                        type_name_str, method_name_str
                    )
                })?;

                // Resolve return type (TypeId-native)
                let return_type_id = {
                    let name_table = self.analyzed.name_table();
                    method
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_to_id(
                                t,
                                self.analyzed.entity_registry(),
                                &self.state.type_metadata,
                                module_interner,
                                &name_table,
                                module_id,
                                self.analyzed.type_arena_ref(),
                            )
                        })
                        .unwrap_or(TypeId::VOID)
                };

                // Create signature (no self parameter) - use module interner
                let sig = self.build_signature(
                    &method.params,
                    method.return_type.as_ref(),
                    SelfParam::None,
                    TypeResolver::Interner(module_interner),
                );
                self.jit.ctx.func.signature = sig;

                // Resolve param type IDs (TypeId-native)
                let param_type_ids: Vec<TypeId> = {
                    let type_metadata = &self.state.type_metadata;
                    let arena = self.analyzed.type_arena_ref();
                    let name_table = self.analyzed.name_table();
                    method
                        .params
                        .iter()
                        .map(|p| {
                            resolve_type_expr_to_id(
                                &p.ty,
                                self.analyzed.entity_registry(),
                                type_metadata,
                                module_interner,
                                &name_table,
                                module_id,
                                arena,
                            )
                        })
                        .collect()
                };
                let param_types: Vec<types::Type> = {
                    let arena_ref = self.analyzed.type_arena();
                    param_type_ids
                        .iter()
                        .map(|&ty_id| type_id_to_cranelift(ty_id, &arena_ref, self.pointer_type))
                        .collect()
                };
                let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

                // Get source file pointer
                let source_file_ptr = self.source_file_ptr();

                // Create function builder
                let mut builder_ctx = FunctionBuilderContext::new();
                {
                    let mut builder =
                        FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

                    let entry_block = builder.create_block();
                    builder.append_block_params_for_function_params(entry_block);
                    builder.switch_to_block(entry_block);

                    // Build variables map (no self for static methods)
                    let mut variables = HashMap::new();

                    // Get entry block params (just user params, no self)
                    let params = builder.block_params(entry_block).to_vec();

                    // Bind parameters (TypeId-native)
                    for (((name, ty), type_id), val) in param_names
                        .iter()
                        .zip(param_types.iter())
                        .zip(param_type_ids.iter())
                        .zip(params.iter())
                    {
                        let var = builder.declare_var(*ty);
                        builder.def_var(var, *val);
                        variables.insert(*name, (var, *type_id));
                    }

                    // Create split contexts (use module interner)
                    let function_ctx = FunctionCtx::module(Some(return_type_id), module_id);
                    let env = compile_env!(
                        self,
                        module_interner,
                        module_global_inits,
                        source_file_ptr,
                        module_id
                    );

                    // Compile method body
                    let mut cf_ctx = ControlFlowCtx::default();
                    let mut codegen_ctx =
                        CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
                    let (terminated, expr_value) = compile_func_body_with_params(
                        &mut builder,
                        body,
                        &mut variables,
                        &mut cf_ctx,
                        &mut codegen_ctx,
                        &function_ctx,
                        &env,
                        None,
                        None,
                    )?;

                    if let Some(value) = expr_value {
                        builder.ins().return_(&[value.value]);
                    } else if !terminated {
                        builder.ins().return_(&[]);
                    }

                    builder.seal_all_blocks();
                    builder.finalize();
                }

                // Define the function
                self.jit.define_function(func_id)?;
                self.jit.clear();
            }
        }

        Ok(())
    }
}
