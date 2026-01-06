use std::collections::HashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};
use cranelift_module::Module;

use super::{Compiler, ControlFlowCtx};
use crate::codegen::stmt::compile_block;
use crate::codegen::types::{CompileCtx, TypeMetadata, resolve_type_expr_full, type_to_cranelift};
use crate::frontend::{
    ClassDecl, FuncDecl, ImplementBlock, InterfaceMethod, RecordDecl, Symbol, TypeExpr,
};
use crate::sema::Type;

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
        if let Some(interfaces) = self.analyzed.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            self.compile_default_method(method, class.name, &metadata)?;
                        }
                    }
                }
            }
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
        if let Some(interfaces) = self.analyzed.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            self.compile_default_method(method, record.name, &metadata)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Get the type name symbol from a TypeExpr (for implement blocks on records/classes)
    fn get_type_name_symbol(&self, ty: &TypeExpr) -> Option<Symbol> {
        match ty {
            TypeExpr::Named(sym) => Some(*sym),
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
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return; // Unsupported type for implement block
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
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
            ),
        };

        // For named types (records/classes), add method return types to metadata
        if let Some(type_sym) = self.get_type_name_symbol(&impl_block.target_type)
            && let Some(metadata) = self.type_metadata.get_mut(&type_sym)
        {
            for method in &impl_block.methods {
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        resolve_type_expr_full(
                            t,
                            &self.analyzed.type_aliases,
                            &self.analyzed.interface_registry,
                            &self.analyzed.interner,
                        )
                    })
                    .unwrap_or(Type::Void);
                metadata
                    .method_return_types
                    .insert(method.name, return_type);
            }
        }

        // Declare methods as functions: TypeName::methodName (implement block convention)
        for method in &impl_block.methods {
            let method_name_str = self.analyzed.interner.resolve(method.name);
            let full_name = format!("{}::{}", type_name, method_name_str);
            let sig = self.create_implement_method_signature(method, &self_vole_type);
            self.jit.declare_function(&full_name, &sig);
        }
    }

    /// Compile implement block methods (second pass)
    pub(super) fn compile_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
    ) -> Result<(), String> {
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
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
            ),
        };

        for method in &impl_block.methods {
            self.compile_implement_method(method, &type_name, &self_vole_type)?;
        }
        Ok(())
    }

    /// Compile a method from an implement block
    fn compile_implement_method(
        &mut self,
        method: &FuncDecl,
        type_name: &str,
        self_vole_type: &Type,
    ) -> Result<(), String> {
        let method_name_str = self.analyzed.interner.resolve(method.name);
        let full_name = format!("{}::{}", type_name, method_name_str);

        let func_id = *self
            .jit
            .func_ids
            .get(&full_name)
            .ok_or_else(|| format!("Internal error: method {} not declared", full_name))?;

        // Create method signature with correct self type (primitives use their type, not pointer)
        let sig = self.create_implement_method_signature(method, self_vole_type);
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self
        let self_cranelift_type = type_to_cranelift(self_vole_type, self.pointer_type);

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Clone type for the closure
        let self_type = self_vole_type.clone();

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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            });

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
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
        let full_name = format!("{}_{}", type_name_str, method_name_str);

        let func_id = *self
            .jit
            .func_ids
            .get(&full_name)
            .ok_or_else(|| format!("Internal error: method {} not declared", full_name))?;

        // Create method signature (self + params)
        let sig = self.create_method_signature(method);
        self.jit.ctx.func.signature = sig;

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Clone metadata for the closure
        let self_vole_type = metadata.vole_type.clone();

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
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
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
        let full_name = format!("{}_{}", type_name_str, method_name_str);

        let func_id =
            *self.jit.func_ids.get(&full_name).ok_or_else(|| {
                format!("Internal error: default method {} not declared", full_name)
            })?;

        // Create method signature (self + params)
        let sig = self.create_interface_method_signature(method);
        self.jit.ctx.func.signature = sig;

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Clone metadata for the closure - self has the concrete type!
        let self_vole_type = metadata.vole_type.clone();

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
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
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
}
