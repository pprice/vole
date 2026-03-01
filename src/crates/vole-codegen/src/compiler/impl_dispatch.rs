//! Class/struct method declaration, registration, and compilation.
//!
//! This module handles the "what-to-compile" logic for type methods:
//! - Type method orchestration (`compile_type_methods`)
//! - Individual method compilation (`compile_method`, `compile_default_method`)
//! - Static method compilation (`compile_static_methods`)
//! - Module type method compilation (`compile_module_type_methods` and helpers)
//! - Shared helpers (`register_method_func`, `get_type_name_from_expr`)

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::impls::ModuleCompileInfo;
use super::impls::TypeMethodsData;
use super::{Compiler, DeclareMode, SelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, TypeMetadata, type_id_to_cranelift};
use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use vole_frontend::ast::InterfaceMethod;
use vole_frontend::{Interner, Symbol, TypeExpr, TypeExprKind};
use vole_identity::{MethodId, ModuleId, TypeId};

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
        let full_name_id = self.analyzed.method_full_name(method_id);
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
                Some(self.analyzed.resolve_symbol(*sym).to_string())
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

    /// Compile methods for a class by name.
    pub(super) fn compile_class_methods(
        &mut self,
        name: Symbol,
        program: &vole_frontend::Program,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        self.compile_class_methods_in_module(name, program, module_id)
    }

    /// Compile instance methods for a struct type by name.
    pub(super) fn compile_struct_methods(
        &mut self,
        name: Symbol,
        has_type_params: bool,
        program: &vole_frontend::Program,
    ) -> CodegenResult<()> {
        // Skip generic structs - they're compiled via monomorphized instances
        if has_type_params {
            return Ok(());
        }
        let module_id = self.program_module();
        let type_def_id = self
            .analyzed
            .try_name_id(module_id, &[name])
            .and_then(|name_id| self.analyzed.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::not_found("type", format!("struct {}", self.resolve_symbol(name)))
            })?;
        let type_def = self.analyzed.get_type(type_def_id);
        let data = TypeMethodsData::from_vir(type_def, name);
        self.compile_type_methods(data, program, module_id)
    }

    /// Compile methods for a class using a specific module for type lookups.
    pub(super) fn compile_class_methods_in_module(
        &mut self,
        name: Symbol,
        program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Look up VirTypeDef to check if generic
        let type_def_id = self
            .analyzed
            .try_name_id(module_id, &[name])
            .and_then(|name_id| self.analyzed.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::not_found("type", format!("class {}", self.resolve_symbol(name)))
            })?;
        let type_def = self.analyzed.get_type(type_def_id);
        // Skip generic classes - they're compiled via monomorphized instances
        if type_def.has_type_params() {
            return Ok(());
        }
        let data = TypeMethodsData::from_vir(type_def, name);
        self.compile_type_methods(data, program, module_id)
    }

    /// Core implementation for compiling methods of a class or struct
    fn compile_type_methods(
        &mut self,
        data: TypeMethodsData<'_>,
        _program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Look up TypeDefId from name (needed as key for type_metadata)
        let query = self.analyzed;
        let type_def_id = query
            .try_name_id(module_id, &[data.name])
            .and_then(|name_id| query.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::not_found(
                    "type",
                    format!(
                        "{} {}",
                        data.type_kind,
                        self.analyzed.resolve_symbol(data.name)
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
                        self.analyzed.resolve_symbol(data.name)
                    ),
                )
            })?;

        // Compile instance methods from VIR method IDs.
        // VirTypeDef.methods includes ALL methods on the type (direct class-body,
        // inherited defaults, implement-block), but only direct class-body methods
        // should be compiled here.  Other methods are compiled by their own paths:
        // - Inherited defaults (has_default=true) → default method compilation below
        // - Implement-block methods (no VIR keyed by this MethodId) → implement block path
        for &method_id in data.method_ids {
            let method_def = self.analyzed.get_method(method_id);
            // Skip inherited default methods
            if method_def.has_default {
                continue;
            }
            // Skip methods without VIR (implement-block methods with duplicate MethodIds)
            if self.analyzed.get_vir_method(method_id).is_none() {
                continue;
            }
            self.compile_method_by_id(method_id, data.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces.
        // Direct method names (for skipping explicitly implemented methods, cross-interner safe).
        // Only include methods that we compiled above (non-default with VIR) plus
        // methods from implement blocks (non-default without VIR but explicitly defined).
        // This prevents the default path from re-compiling methods the class explicitly provides.
        let direct_method_name_strs: std::collections::HashSet<String> = data
            .method_ids
            .iter()
            .filter_map(|&mid| {
                let md = self.analyzed.get_method(mid);
                // Inherited defaults should NOT count as "explicitly implemented"
                if md.has_default {
                    return None;
                }
                self.analyzed.last_segment(md.name_id)
            })
            .collect();

        // Collect interface name strings using query (avoids borrow conflicts with compile calls).
        let interface_name_strs: Vec<String> = {
            let query = self.analyzed;
            query
                .try_name_id(module_id, &[data.name])
                .and_then(|type_name_id| query.try_type_def_id(type_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            query.last_segment(query.entity_type_name_id(interface_id))
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
            let found_in_main = self
                .analyzed
                .program()
                .declarations
                .iter()
                .find_map(|decl| {
                    if let vole_frontend::Decl::Interface(iface) = decl {
                        let name_str = self.analyzed.interner().resolve(iface.name);
                        if name_str == interface_name_str {
                            return Some(iface.methods.clone());
                        }
                    }
                    None
                });
            if let Some(methods) = found_in_main {
                for method in methods {
                    let method_name_str = self.analyzed.interner().resolve(method.name).to_string();
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
            let module_paths: Vec<String> =
                self.analyzed.module_programs().keys().cloned().collect();
            for module_path in module_paths {
                let found = {
                    let (prog, interner) = &self.analyzed.module_programs()[&module_path];
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
                let module_id = self.analyzed.module_id_or_main(module_path);
                let module_interner = self.analyzed.module_programs()[module_path].1.clone();
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

        // Compile static methods from VIR metadata
        if !data.static_method_ids.is_empty() {
            self.compile_static_methods_by_id(data.static_method_ids, data.name, module_id)?;
        }

        Ok(())
    }

    /// Compile a single method by MethodId (VIR-based).
    ///
    /// Uses VirMethodDef param_names to build parameter bindings instead of
    /// reading AST FuncDecl params.
    fn compile_method_by_id(
        &mut self,
        method_id: MethodId,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> CodegenResult<()> {
        let method_def = self.analyzed.get_method(method_id);
        let method_name_id = method_def.name_id;
        let type_name_str = self.analyzed.resolve_symbol(type_name).to_string();
        let method_name_str = self
            .analyzed
            .last_segment(method_name_id)
            .unwrap_or_default();

        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Use TypeId directly for self binding
        let self_type_id = metadata.vole_type;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.analyzed.get_method(method_id);
        let param_names = method_def.param_names.clone();
        let (param_type_ids, method_return_type_id) = {
            let (params, ret, _) = self
                .vir_query_unwrap_function(method_def.signature_id)
                .ok_or_else(|| {
                    CodegenError::internal("method signature: expected function type")
                })?;
            (params, Some(ret))
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Build params from VirMethodDef param_names (already excludes `self`)
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.arena();
            let interner = self.analyzed.interner();
            param_names
                .iter()
                .zip(param_type_ids.iter())
                .map(|(param_name, &type_id)| {
                    let sym = interner.lookup(param_name).unwrap_or_else(|| {
                        panic!(
                            "compile_method_by_id: param '{}' not interned for {}::{}",
                            param_name, type_name_str, method_name_str
                        )
                    });
                    let cranelift_type =
                        type_id_to_cranelift(type_id, arena_ref, self.pointer_type);
                    (sym, type_id, cranelift_type)
                })
                .collect()
        };

        // Check if a VIR function was lowered for this method
        let vir_func = self.analyzed.get_vir_method(method_id);

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
            let config = FunctionCompileConfig::method(params, self_binding, method_return_type_id);
            let vir = vir_func.expect("VIR must be available for type method");
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir.body,
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
        let type_name_str = self.analyzed.resolve_symbol(type_name).to_string();
        let method_name_str = self.analyzed.resolve_symbol(method.name).to_string();

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
            .analyzed
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
        let method_def = self.analyzed.get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let (params, ret, _) = self
                .vir_query_unwrap_function(method_def.signature_id)
                .ok_or_else(|| {
                    CodegenError::internal("method signature: expected function type")
                })?;
            (params, ret)
        };

        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = method
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Validate method body exists for default methods
        let _body = method.body.as_ref().ok_or_else(|| {
            CodegenError::internal_with_context("default method has no body", &*method_name_str)
        })?;

        // Get source file pointer and self binding (use metadata.vole_type for self type)
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();
        let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

        // Check if a VIR function was lowered for this method
        let vir_func = self.analyzed.get_vir_method(semantic_method_id);

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

            let config = FunctionCompileConfig::method(params, self_binding, Some(return_type_id));
            let vir = vir_func.expect("VIR must be available for default method");
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir.body,
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
        let type_name_str = self.analyzed.resolve_symbol(type_name).to_string();
        let method_name_str = interner.resolve(method.name).to_string();

        // Look up method NameId using the module interner (cross-interner safe)
        let method_name_id =
            crate::types::method_name_id_with_interner(self.analyzed, interner, method.name)
                .ok_or_else(|| CodegenError::not_found("method name_id", &method_name_str))?;

        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "default method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        let semantic_method_id = self
            .analyzed
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
        let method_def = self.analyzed.get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let (params, ret, _) = self
                .vir_query_unwrap_function(method_def.signature_id)
                .ok_or_else(|| {
                    CodegenError::internal("method signature: expected function type")
                })?;
            (params, ret)
        };

        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = method
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Validate method body exists for default methods
        let _body = method.body.as_ref().ok_or_else(|| {
            CodegenError::internal_with_context("default method has no body", &*method_name_str)
        })?;

        // Use the module interner's "self" symbol so the body's identifier references
        // for `self` (which use the module interner) bind correctly.
        let source_file_ptr = self.source_file_ptr();
        let self_sym = interner
            .lookup("self")
            .ok_or_else(|| CodegenError::internal("'self' not interned in module interner"))?;
        let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

        // Check if a VIR function was lowered for this method
        let vir_func = self.analyzed.get_vir_method(semantic_method_id);

        // Create function builder and compile using the module interner
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, interner, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let config = FunctionCompileConfig::method(params, self_binding, Some(return_type_id));
            let vir = vir_func.expect("VIR must be available for module default method");
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir.body,
                module_id,
                None,
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile static methods by MethodId from VIR metadata.
    fn compile_static_methods_by_id(
        &mut self,
        static_method_ids: &[MethodId],
        type_name: Symbol,
        _module_id: ModuleId,
    ) -> CodegenResult<()> {
        for &method_id in static_method_ids {
            let method_def = self.analyzed.get_method(method_id);

            // Only compile methods with bodies (skip external-only)
            if method_def.external_binding.is_some() {
                continue;
            }

            let method_name_id = method_def.name_id;
            let method_name_str = self
                .analyzed
                .last_segment(method_name_id)
                .unwrap_or_default();

            // Function key from EntityRegistry full_name_id
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!(
                        "{}::{}",
                        self.analyzed.resolve_symbol(type_name),
                        method_name_str,
                    ),
                )
            })?;

            // Create signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema (pre-resolved signature)
            let method_def = self.analyzed.get_method(method_id);
            let param_names = method_def.param_names.clone();
            let (param_type_ids, return_type_id) = {
                let (params, ret, _) = self
                    .vir_query_unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("static method signature: expected function type")
                    })?;
                (params, ret)
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = param_names
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((name, &type_id), &cranelift_type)| {
                    let sym = self.analyzed.interner().lookup(name).unwrap_or_else(|| {
                        panic!(
                            "compile_static_methods_by_id: param '{}' not interned for ::{}",
                            name, method_name_str
                        )
                    });
                    (sym, type_id, cranelift_type)
                })
                .collect();

            // Check if a VIR function was lowered for this method
            let vir_func = self.analyzed.get_vir_method(method_id);

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

                let config = FunctionCompileConfig::top_level(params, Some(return_type_id));
                let vir = vir_func.expect("VIR must be available for static method");
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir.body,
                    None,
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile methods for a module type using VIR metadata.
    /// This is the unified implementation for compile_module_class_methods and
    /// compile_module_struct_methods.
    fn compile_module_type_methods(
        &mut self,
        type_name_str: &str,
        module_interner: &Interner,
        module_path: &str,
    ) -> CodegenResult<()> {
        // Look up the actual module_id from the module_path (not main_module!)
        let module_id = self
            .analyzed
            .name_table()
            .module_id_if_known(module_path)
            .unwrap_or_else(|| self.program_module());

        // Resolve VirTypeDef by name
        let Some(type_def_id) = self
            .analyzed
            .resolve_type_def_by_str(module_id, type_name_str)
        else {
            tracing::warn!(type_name = %type_name_str, "Could not find TypeDefId for module type methods");
            return Ok(());
        };

        let type_def = self.analyzed.get_type(type_def_id);

        // Generic types are compiled via monomorphized instances.
        if type_def.has_type_params() {
            return Ok(());
        }

        let is_class = type_def.is_class();

        // Find the type metadata by looking for the type name string
        let metadata = self
            .state
            .type_metadata
            .values()
            .find(|meta| {
                // Use unwrap_class for classes, unwrap_struct for structs
                let found_def_id = if is_class {
                    self.vir_query_unwrap_class(meta.vole_type)
                        .map(|(id, _)| id)
                } else {
                    self.vir_query_unwrap_struct(meta.vole_type)
                        .map(|(id, _)| id)
                };
                found_def_id.is_some_and(|id| {
                    let name_id = self.analyzed.entity_type_name_id(id);
                    self.analyzed
                        .name_table()
                        .last_segment_str(name_id)
                        .is_some_and(|name| name == type_name_str)
                })
            })
            .cloned();

        let Some(metadata) = metadata else {
            tracing::warn!(type_name = %type_name_str, "Could not find metadata for module type");
            return Ok(());
        };

        let module_info = ModuleCompileInfo {
            interner: module_interner,
            module_id,
        };

        // Compile instance methods from VIR metadata
        let method_ids: Vec<MethodId> = type_def.methods.clone();
        self.compile_module_type_instance_methods(
            &method_ids,
            &metadata,
            &module_info,
            type_name_str,
        )?;

        // Compile static methods from VIR metadata
        let static_method_ids: Vec<MethodId> = type_def.static_methods.clone();
        if !static_method_ids.is_empty() {
            self.compile_module_type_static_methods(
                &static_method_ids,
                &metadata,
                &module_info,
                type_name_str,
            )?;
        }

        Ok(())
    }

    /// Compile instance methods for a module type using VIR metadata.
    fn compile_module_type_instance_methods(
        &mut self,
        method_ids: &[MethodId],
        metadata: &TypeMetadata,
        module_info: &ModuleCompileInfo<'_>,
        type_name_str: &str,
    ) -> CodegenResult<()> {
        for &method_id in method_ids {
            let method_def = self.analyzed.get_method(method_id);
            // Skip inherited default methods — they are compiled via the
            // implement block / default method path, not the direct method path.
            if method_def.has_default {
                continue;
            }
            let method_name_id = method_def.name_id;
            let method_name_str = self
                .analyzed
                .last_segment(method_name_id)
                .unwrap_or_default();
            let param_names = method_def.param_names.clone();

            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found("method", format!("{}::{}", type_name_str, method_name_str))
            })?;

            // Skip methods already compiled by an earlier pass (e.g. implement blocks).
            // VirTypeDef.methods includes implement-block methods, but those are compiled
            // by compile_module_implement_block which runs first.
            if self.defined_functions.contains(&func_id) {
                continue;
            }

            // Create method signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(method_id, SelfParam::Pointer);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.analyzed.get_method(method_id);
            let (param_type_ids, return_type_id) = {
                let (params, ret, _) = self
                    .vir_query_unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
                (params, Some(ret))
            };

            let self_sym = module_info
                .interner
                .lookup("self")
                .ok_or_else(|| CodegenError::internal("method compilation: 'self' not interned"))?;
            // Build params from VirMethodDef param_names (already excludes self)
            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = param_names
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((name, &type_id), &cranelift_type)| {
                    let sym = module_info.interner.lookup(name).unwrap_or_else(|| {
                        panic!(
                            "compile_module_type_instance_methods: param '{}' not interned for {}::{}",
                            name, type_name_str, method_name_str
                        )
                    });
                    (sym, type_id, cranelift_type)
                })
                .collect();
            let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

            // Check if a VIR function was lowered for this method
            let vir_func = self.analyzed.get_vir_method(method_id);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(self, module_info.interner, source_file_ptr);
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::method(params, self_binding, return_type_id);
                let vir = vir_func.expect("VIR must be available for module method");
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir.body,
                    Some(module_info.module_id),
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile static methods for a module type using VIR metadata.
    fn compile_module_type_static_methods(
        &mut self,
        static_method_ids: &[MethodId],
        _metadata: &TypeMetadata,
        module_info: &ModuleCompileInfo<'_>,
        type_name_str: &str,
    ) -> CodegenResult<()> {
        for &method_id in static_method_ids {
            let method_def = self.analyzed.get_method(method_id);

            // Skip external-only statics
            if method_def.external_binding.is_some() {
                continue;
            }

            let method_name_str = self
                .analyzed
                .last_segment(method_def.name_id)
                .unwrap_or_default();
            let param_names = method_def.param_names.clone();

            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!("{}::{}", type_name_str, method_name_str),
                )
            })?;

            // Create signature using pre-resolved MethodId (no self parameter for static)
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.analyzed.get_method(method_id);
            let (param_type_ids, return_type_id) = {
                let (params, ret, _) = self
                    .vir_query_unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("static method signature: expected function type")
                    })?;
                (params, Some(ret))
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = param_names
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((name, &type_id), &cranelift_type)| {
                    let sym = module_info.interner.lookup(name).unwrap_or_else(|| {
                        panic!(
                            "compile_module_type_static_methods: param '{}' not interned for {}::{}",
                            name, type_name_str, method_name_str
                        )
                    });
                    (sym, type_id, cranelift_type)
                })
                .collect();

            // Check if a VIR function was lowered for this method
            let vir_func = self.analyzed.get_vir_method(method_id);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(self, module_info.interner, source_file_ptr);
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(params, return_type_id);
                let vir = vir_func.expect("VIR must be available for module static method");
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir.body,
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
        name: Symbol,
        module_interner: &Interner,
        module_path: &str,
    ) -> CodegenResult<()> {
        let type_name_str = module_interner.resolve(name);
        self.compile_module_type_methods(type_name_str, module_interner, module_path)
    }

    /// Compile methods for a module struct (uses module interner)
    pub(super) fn compile_module_struct_methods(
        &mut self,
        name: Symbol,
        has_methods: bool,
        module_interner: &Interner,
        module_path: &str,
    ) -> CodegenResult<()> {
        if !has_methods {
            return Ok(());
        }
        let type_name_str = module_interner.resolve(name);
        self.compile_module_type_methods(type_name_str, module_interner, module_path)
    }
}
