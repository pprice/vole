//! Class/struct method declaration, registration, and compilation.
//!
//! This module handles the "what-to-compile" logic for type methods:
//! - Type method orchestration (`compile_type_methods`)
//! - Individual method compilation (`compile_method`, `compile_default_method`)
//! - Static method compilation (`compile_static_methods`)
//! - Module type method compilation (`compile_module_type_methods` and helpers)
//! - Shared helpers (`register_method_func`, `get_type_name_from_expr`)

use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::impls::{ModuleCompileInfo, TypeDeclInfo, TypeMethodsData};
use super::{Compiler, DeclareMode, SelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, TypeMetadata, method_name_id_with_interner, type_id_to_cranelift};
use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use vole_frontend::ast::{ClassDecl, InterfaceMethod, StaticsBlock, StructDecl};
use vole_frontend::{Expr, FuncDecl, Interner, Symbol, TypeExpr, TypeExprKind};
use vole_identity::{MethodId, ModuleId};
use vole_sema::type_arena::TypeId;

use super::impls::primitive_type_name;

impl Compiler<'_> {
    /// Register a method in the JIT function registry if not already registered.
    ///
    /// Returns the function key for downstream use (method_func_keys, compilation).
    /// If the method is already registered (e.g. from overlapping implement blocks),
    /// returns the existing key without re-declaring.
    pub(super) fn register_method_func(
        &mut self,
        method_id: MethodId,
        sig: &cranelift::prelude::Signature,
        mode: DeclareMode,
    ) -> crate::function_registry::FunctionKey {
        let full_name_id = self.query().method_full_name(method_id);
        let func_key = self.func_registry.intern_name_id(full_name_id);
        if self.func_registry.func_id(func_key).is_none() {
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = match mode {
                DeclareMode::Declare => self.jit.declare_function(&display_name, sig),
                DeclareMode::Import => self.jit.import_function(&display_name, sig),
            };
            self.func_registry.set_func_id(func_key, jit_func_id);
        }
        func_key
    }

    /// Get the type name string from a TypeExpr (works for primitives, named types,
    /// and generic specializations like `Tagged<i64>`)
    pub(super) fn get_type_name_from_expr(&self, ty: &TypeExpr) -> Option<String> {
        match &ty.kind {
            TypeExprKind::Primitive(p) => Some(primitive_type_name(*p).to_string()),
            TypeExprKind::Handle => Some("handle".to_string()),
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                Some(self.query().resolve_symbol(*sym).to_string())
            }
            // `extend [T] with Iterable<T>` has an Array target type.
            TypeExprKind::Array(_) => Some("array".to_string()),
            _ => None,
        }
    }

    /// Get the type name string from a TypeExpr using a specific interner
    /// (for module-specific symbols)
    pub(super) fn get_type_name_from_expr_with_interner(
        &self,
        ty: &TypeExpr,
        interner: &Interner,
    ) -> Option<String> {
        match &ty.kind {
            TypeExprKind::Primitive(p) => Some(primitive_type_name(*p).to_string()),
            TypeExprKind::Handle => Some("handle".to_string()),
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                Some(interner.resolve(*sym).to_string())
            }
            // `extend [T] with Iterable<T>` has an Array target type.
            TypeExprKind::Array(_) => Some("array".to_string()),
            _ => None,
        }
    }

    /// Compile methods for a class
    pub(super) fn compile_class_methods(
        &mut self,
        class: &ClassDecl,
        program: &vole_frontend::Program,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        self.compile_class_methods_in_module(class, program, module_id)
    }

    /// Compile instance methods for a struct type.
    pub(super) fn compile_struct_methods(
        &mut self,
        struct_decl: &StructDecl,
        program: &vole_frontend::Program,
    ) -> CodegenResult<()> {
        // Skip generic structs - they're compiled via monomorphized instances
        if struct_decl.has_type_params() {
            return Ok(());
        }
        let module_id = self.program_module();
        self.compile_type_methods(TypeMethodsData::from_decl(struct_decl), program, module_id)
    }

    /// Compile methods for a class using a specific module for type lookups.
    pub(super) fn compile_class_methods_in_module(
        &mut self,
        class: &ClassDecl,
        program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Skip generic classes - they're compiled via monomorphized instances
        if class.has_type_params() {
            return Ok(());
        }
        self.compile_type_methods(TypeMethodsData::from_decl(class), program, module_id)
    }

    /// Core implementation for compiling methods of a class or struct
    fn compile_type_methods(
        &mut self,
        data: TypeMethodsData<'_>,
        _program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Look up TypeDefId from name (needed as key for type_metadata)
        let query = self.query();
        let type_def_id = query
            .try_name_id(module_id, &[data.name])
            .and_then(|name_id| query.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::not_found(
                    "type",
                    format!(
                        "{} {}",
                        data.type_kind,
                        self.query().resolve_symbol(data.name)
                    ),
                )
            })?;

        let metadata = self
            .state
            .type_metadata
            .get(&type_def_id)
            .cloned()
            .ok_or_else(|| {
                CodegenError::not_found(
                    "type_metadata",
                    format!(
                        "{} {}",
                        data.type_kind,
                        self.query().resolve_symbol(data.name)
                    ),
                )
            })?;

        for method in data.methods {
            self.compile_method(method, data.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces.
        // Direct method names (for skipping explicitly implemented methods, cross-interner safe).
        let direct_method_name_strs: std::collections::HashSet<String> = data
            .methods
            .iter()
            .map(|m| self.resolve_symbol(m.name))
            .collect();

        // Collect interface name strings using query (avoids borrow conflicts with compile calls).
        let interface_name_strs: Vec<String> = {
            let query = self.query();
            query
                .try_name_id(module_id, &[data.name])
                .and_then(|type_name_id| query.try_type_def_id(type_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            query.last_segment(interface_def.name_id)
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        // Collect (InterfaceMethod, is_from_module) pairs before any mutable operations.
        // We clone the method data so we can release the borrow on self.analyzed.
        struct DefaultMethodInfo {
            method: InterfaceMethod,
            /// True if from a module program (needs module interner for compilation).
            from_module: bool,
            /// The interner key (module path) if from_module is true.
            module_path: Option<String>,
        }
        let mut default_methods_to_compile: Vec<DefaultMethodInfo> = Vec::new();
        for interface_name_str in &interface_name_strs {
            // Search main program first
            let found_in_main = self.analyzed.program.declarations.iter().find_map(|decl| {
                if let vole_frontend::Decl::Interface(iface) = decl {
                    let name_str = self.analyzed.interner.resolve(iface.name);
                    if name_str == interface_name_str {
                        return Some(iface.methods.clone());
                    }
                }
                None
            });
            if let Some(methods) = found_in_main {
                for method in methods {
                    let method_name_str = self.analyzed.interner.resolve(method.name).to_string();
                    if method.body.is_some() && !direct_method_name_strs.contains(&method_name_str)
                    {
                        default_methods_to_compile.push(DefaultMethodInfo {
                            method,
                            from_module: false,
                            module_path: None,
                        });
                    }
                }
                continue; // Found in main, no need to search modules
            }

            // Search module programs
            let module_paths: Vec<String> = self.analyzed.module_programs.keys().cloned().collect();
            for module_path in module_paths {
                let found = {
                    let (prog, interner) = &self.analyzed.module_programs[&module_path];
                    prog.declarations.iter().find_map(|decl| {
                        if let vole_frontend::Decl::Interface(iface) = decl {
                            let name_str = interner.resolve(iface.name);
                            if name_str == interface_name_str {
                                return Some((iface.methods.clone(), interner.clone()));
                            }
                        }
                        None
                    })
                };
                if let Some((methods, mod_interner)) = found {
                    for method in methods {
                        let method_name_str = mod_interner.resolve(method.name).to_string();
                        if method.body.is_some()
                            && !direct_method_name_strs.contains(&method_name_str)
                        {
                            default_methods_to_compile.push(DefaultMethodInfo {
                                method,
                                from_module: true,
                                module_path: Some(module_path.clone()),
                            });
                        }
                    }
                    break; // Found in this module, no need to search further
                }
            }
        }

        for info in default_methods_to_compile {
            if info.from_module {
                let module_path = info.module_path.as_deref().unwrap_or("");
                let module_id = self.query().module_id_or_main(module_path);
                let module_interner = self.analyzed.module_programs[module_path].1.clone();
                self.compile_default_method_with_interner(
                    &info.method,
                    data.name,
                    &metadata,
                    &module_interner,
                    Some(module_id),
                )?;
            } else {
                self.compile_default_method(&info.method, data.name, &metadata)?;
            }
        }

        // Compile static methods
        if let Some(statics) = data.statics {
            self.compile_static_methods(statics, data.name, module_id)?;
        }

        Ok(())
    }

    /// Compile a single method
    fn compile_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> CodegenResult<()> {
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = self.query().resolve_symbol(method.name).to_string();

        let method_name_id = self.method_name_id(method.name)?;
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        // Look up MethodId from entity_registry for pre-computed signature
        let semantic_method_id = self
            .query()
            .find_method(metadata.type_def_id, method_name_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "class instance method not registered in entity_registry",
                    format!(
                        "{}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    ),
                )
            })?;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Use TypeId directly for self binding
        let self_type_id = metadata.vole_type;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, method_return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
            (params.to_vec(), Some(ret))
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Skip explicit `self` params — they are handled via the separate self_binding.
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.arena();
            method
                .params
                .iter()
                .filter(|p| p.name != self_sym)
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, arena_ref, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );
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
                &env,
                config,
                None,
                None,
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile a default method from an interface, monomorphized for a concrete type
    fn compile_default_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> CodegenResult<()> {
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = self.query().resolve_symbol(method.name).to_string();

        let method_name_id = self.method_name_id(method.name)?;
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "default method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        // Look up MethodId - interface default methods are now registered on implementing types
        let semantic_method_id = self
            .query()
            .find_method(metadata.type_def_id, method_name_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "interface default method not registered on implementing type",
                    format!(
                        "{}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    ),
                )
            })?;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("default method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
            (params.to_vec(), ret)
        };

        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = method
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Compile method body (must exist for default methods)
        let body = method.body.as_ref().ok_or_else(|| {
            CodegenError::internal_with_context("default method has no body", &*method_name_str)
        })?;

        // Get source file pointer and self binding (use metadata.vole_type for self type)
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();
        let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let config =
                FunctionCompileConfig::method(body, params, self_binding, Some(return_type_id));
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile a default method from a module interface, using the module interner.
    ///
    /// This is needed when the default method body uses symbols from a module interner
    /// (e.g., stdlib `Comparable.lt` uses stdlib symbols for `self` and `compare`).
    fn compile_default_method_with_interner(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        metadata: &TypeMetadata,
        interner: &Interner,
        module_id: Option<ModuleId>,
    ) -> CodegenResult<()> {
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = interner.resolve(method.name).to_string();

        // Look up method NameId using the module interner (cross-interner safe)
        let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name)
            .ok_or_else(|| CodegenError::not_found("method name_id", &method_name_str))?;

        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "default method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        let semantic_method_id = self
            .query()
            .find_method(metadata.type_def_id, method_name_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "interface default method not registered on implementing type",
                    format!(
                        "{}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    ),
                )
            })?;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("default method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
            (params.to_vec(), ret)
        };

        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = method
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Compile method body (must exist for default methods)
        let body = method.body.as_ref().ok_or_else(|| {
            CodegenError::internal_with_context("default method has no body", &*method_name_str)
        })?;

        // Use the module interner's "self" symbol so the body's identifier references
        // for `self` (which use the module interner) bind correctly.
        let source_file_ptr = self.source_file_ptr();
        let self_sym = interner
            .lookup("self")
            .ok_or_else(|| CodegenError::internal("'self' not interned in module interner"))?;
        let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

        // Create function builder and compile using the module interner
        let no_global_inits = FxHashMap::default();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, interner, &no_global_inits, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let config =
                FunctionCompileConfig::method(body, params, self_binding, Some(return_type_id));
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                module_id,
                None,
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile static methods from a statics block
    fn compile_static_methods(
        &mut self,
        statics: &StaticsBlock,
        type_name: Symbol,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Get the TypeDefId for looking up method info
        let type_name_id = self.query().name_id(module_id, &[type_name]);
        let type_def_id = self.query().try_type_def_id(type_name_id).ok_or_else(|| {
            let type_name_str = self.resolve_symbol(type_name);
            CodegenError::internal_with_context(
                "static method type not registered in entity_registry",
                format!("{} (type_name_id={:?})", type_name_str, type_name_id),
            )
        })?;

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Look up MethodId from entity_registry for pre-computed signature
            let method_name_id = self.method_name_id(method.name)?;
            let semantic_method_id = self
                .query()
                .find_static_method(type_def_id, method_name_id)
                .ok_or_else(|| {
                    let type_name_str = self.resolve_symbol(type_name);
                    let method_name_str = self.resolve_symbol(method.name);
                    CodegenError::internal_with_context(
                        "static method not registered in entity_registry",
                        format!(
                            "{}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_name_str, method_name_str, type_def_id, method_name_id
                        ),
                    )
                })?;

            // Function key from EntityRegistry full_name_id
            let method_def = self.analyzed.query().get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!(
                        "{}::{}",
                        self.query().resolve_symbol(type_name),
                        self.query().resolve_symbol(method.name),
                    ),
                )
            })?;

            // Create signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema (pre-resolved signature)
            let (param_type_ids, return_type_id) = {
                let arena = self.arena();
                let (params, ret, _) =
                    arena
                        .unwrap_function(method_def.signature_id)
                        .ok_or_else(|| {
                            CodegenError::internal(
                                "static method signature: expected function type",
                            )
                        })?;
                (params.to_vec(), ret)
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(self, source_file_ptr);
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(body, params, Some(return_type_id));
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    None,
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile methods for a class using a specific module for type lookups.
    /// This is the unified implementation for compile_module_class_methods and
    /// compile_module_struct_methods.
    fn compile_module_type_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        // Generic types are compiled via monomorphized instances.
        if type_decl.has_type_params() {
            return Ok(());
        }

        let type_name_str = module_interner.resolve(type_decl.name());
        let type_kind = type_decl.type_kind();
        let is_class = type_decl.is_class();

        // Look up the actual module_id from the module_path (not main_module!)
        let module_id = self
            .analyzed
            .name_table()
            .module_id_if_known(module_path)
            .unwrap_or_else(|| self.program_module());

        // Find the type metadata by looking for the type name string
        let metadata = self
            .state
            .type_metadata
            .values()
            .find(|meta| {
                let arena = self.arena();
                // Use unwrap_class for classes, unwrap_struct for structs
                let type_def_id = if is_class {
                    arena.unwrap_class(meta.vole_type).map(|(id, _)| id)
                } else {
                    arena.unwrap_struct(meta.vole_type).map(|(id, _)| id)
                };
                type_def_id.is_some_and(|id| {
                    let name_id = self.query().get_type(id).name_id;
                    self.analyzed
                        .name_table()
                        .last_segment_str(name_id)
                        .is_some_and(|name| name == type_name_str)
                })
            })
            .cloned();

        let Some(metadata) = metadata else {
            tracing::warn!(type_name = %type_name_str, type_kind, "Could not find metadata for module type");
            return Ok(());
        };

        let module_info = ModuleCompileInfo {
            interner: module_interner,
            module_id,
            global_inits: module_global_inits,
        };

        // Compile instance methods
        self.compile_module_type_instance_methods(
            type_decl,
            &metadata,
            &module_info,
            type_name_str,
        )?;

        // Compile static methods
        if let Some(statics) = type_decl.statics() {
            self.compile_module_type_static_methods(
                statics,
                &metadata,
                &module_info,
                type_name_str,
                type_kind,
            )?;
        }

        Ok(())
    }

    /// Compile instance methods for a module type.
    /// Helper for compile_module_type_methods to keep functions under ~80 lines.
    fn compile_module_type_instance_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        metadata: &TypeMetadata,
        module_info: &ModuleCompileInfo<'_>,
        type_name_str: &str,
    ) -> CodegenResult<()> {
        let type_kind = type_decl.type_kind();

        for method in type_decl.methods() {
            let method_name_str = module_info.interner.resolve(method.name);

            // Look up MethodId from sema to get pre-computed signature
            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_info.interner, method.name)
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "module method name not found in name_table",
                            format!("{}::{}::{}", type_kind, type_name_str, method_name_str),
                        )
                    })?;

            let semantic_method_id = self
                .query()
                .find_method(metadata.type_def_id, method_name_id)
                .ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "module method not registered in entity_registry",
                        format!(
                            "{}::{}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_kind,
                            type_name_str,
                            method_name_str,
                            metadata.type_def_id,
                            method_name_id
                        ),
                    )
                })?;

            let method_def = self.query().get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found("method", format!("{}::{}", type_name_str, method_name_str))
            })?;

            // Create method signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.query().get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let arena = self.arena();
                let (params, ret, _) =
                    arena
                        .unwrap_function(method_def.signature_id)
                        .ok_or_else(|| {
                            CodegenError::internal("method signature: expected function type")
                        })?;
                (params.to_vec(), Some(ret))
            };

            let self_sym = module_info
                .interner
                .lookup("self")
                .ok_or_else(|| CodegenError::internal("method compilation: 'self' not interned"))?;
            // Skip explicit `self` params — they are handled via the separate self_binding.
            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .filter(|p| p.name != self_sym)
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();
            let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(
                    self,
                    module_info.interner,
                    module_info.global_inits,
                    source_file_ptr
                );
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::method(
                    &method.body,
                    params,
                    self_binding,
                    return_type_id,
                );
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    Some(module_info.module_id),
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile static methods for a module type.
    /// Helper for compile_module_type_methods to keep functions under ~80 lines.
    fn compile_module_type_static_methods(
        &mut self,
        statics: &StaticsBlock,
        metadata: &TypeMetadata,
        module_info: &ModuleCompileInfo<'_>,
        type_name_str: &str,
        type_kind: &str,
    ) -> CodegenResult<()> {
        for method in &statics.methods {
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            let method_name_str = module_info.interner.resolve(method.name);

            // Look up MethodId from sema to get pre-computed signature
            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_info.interner, method.name)
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "module static method name not found in name_table",
                            format!("{}::{}::{}", type_kind, type_name_str, method_name_str),
                        )
                    })?;

            let semantic_method_id = self
                .query()
                .find_static_method(metadata.type_def_id, method_name_id)
                .ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "module static method not registered in entity_registry",
                        format!(
                            "{}::{}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_kind,
                            type_name_str,
                            method_name_str,
                            metadata.type_def_id,
                            method_name_id
                        ),
                    )
                })?;

            let method_def = self.query().get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!("{}::{}", type_name_str, method_name_str),
                )
            })?;

            // Create signature using pre-resolved MethodId (no self parameter for static)
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.query().get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let arena = self.arena();
                let (params, ret, _) =
                    arena
                        .unwrap_function(method_def.signature_id)
                        .ok_or_else(|| {
                            CodegenError::internal(
                                "static method signature: expected function type",
                            )
                        })?;
                (params.to_vec(), Some(ret))
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(
                    self,
                    module_info.interner,
                    module_info.global_inits,
                    source_file_ptr
                );
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(body, params, return_type_id);
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    Some(module_info.module_id),
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile methods for a module class (uses module interner)
    pub(super) fn compile_module_class_methods(
        &mut self,
        class: &ClassDecl,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        self.compile_module_type_methods(class, module_interner, module_path, module_global_inits)
    }

    /// Compile methods for a module struct (uses module interner)
    pub(super) fn compile_module_struct_methods(
        &mut self,
        struct_decl: &StructDecl,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        self.compile_module_type_methods(
            struct_decl,
            module_interner,
            module_path,
            module_global_inits,
        )
    }
}
