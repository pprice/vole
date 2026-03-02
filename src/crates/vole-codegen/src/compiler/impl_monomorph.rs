//! Implement block registration and compilation.
//!
//! This module handles the "how-to-instantiate" logic for implement blocks:
//! - Implement block registration (first pass): `register_implement_block*`
//! - Implement block compilation (second pass): `compile_implement_block*`
//! - Module implement block compilation: `compile_module_implement_block`
//! - Individual implement method compilation: `compile_implement_method`, `compile_module_implement_method`
//! - Implement statics compilation: `compile_implement_statics`
//! - Interface interner resolution: `find_interface_method_interner`
//! - Array iterable default methods: `compile_array_iterable_default_methods`, `import_array_iterable_default_methods`

use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::{Compiler, DeclareMode, SelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::vir_conversions::vir_type_to_cranelift;
use crate::types::{CodegenCtx, MethodInfo};
use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use vole_frontend::{Interner, Symbol};
use vole_identity::{MethodId, ModuleId, NameId, TypeDefId, TypeId, VirTypeId};
use vole_vir::VirImplementBlockEntry;

impl Compiler<'_> {
    /// Register implement block methods (first pass).
    ///
    /// Takes pre-resolved VIR metadata instead of walking AST `ImplementBlock`.
    pub(super) fn register_implement_block(
        &mut self,
        entry: &VirImplementBlockEntry,
    ) -> CodegenResult<()> {
        self.register_implement_block_inner(entry, None)
    }

    /// Import all methods (instance + static) from a module implement block.
    /// Uses Linkage::Import for pre-compiled modules in shared cache.
    ///
    /// Takes pre-resolved VIR metadata instead of walking AST `ImplementBlock`.
    pub(super) fn import_module_implement_block(
        &mut self,
        entry: &VirImplementBlockEntry,
    ) -> CodegenResult<()> {
        let type_def_id = entry.type_def_id;
        let self_type_id = entry.self_type_id;
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);

        // Import explicitly declared instance methods
        for &method_id in &entry.instance_methods {
            let method_def = self.analyzed.get_method(method_id);
            let sig = self.build_signature_for_method(method_id, SelfParam::TypedId(self_type_id));
            let func_key = self.register_method_func(method_id, &sig, DeclareMode::Import);
            self.state
                .method_func_keys
                .insert((type_name_id, method_def.name_id), func_key);
        }

        // Import interface default methods (concrete ones, not abstract/generic).
        // These were compiled as part of the module and must be imported when using the module cache.
        let direct_method_name_ids: std::collections::HashSet<NameId> = entry
            .instance_methods
            .iter()
            .map(|&mid| self.analyzed.get_method(mid).name_id)
            .collect();

        let iface_default_methods =
            self.collect_iface_default_methods(type_def_id, &direct_method_name_ids);

        for (semantic_method_id, method_name_id, interface_tdef_id) in iface_default_methods {
            // Build TypeParam substitution map for this interface implementation.
            let type_param_subs = self
                .analyzed
                .interface_impl_type_param_subs(type_def_id, interface_tdef_id);
            // Skip abstract/generic default methods (not compiled in the module).
            if !type_param_subs.is_empty() {
                let has_abstract = type_param_subs
                    .values()
                    .any(|&v| self.vir_query_unwrap_type_param(v).is_some());
                if has_abstract {
                    continue;
                }
            }
            let sig = {
                let method_def = self.analyzed.get_method(semantic_method_id);
                let subst_params: Vec<TypeId> = method_def
                    .param_types
                    .iter()
                    .map(|&vir_ty| {
                        if vir_ty == VirTypeId::UNKNOWN {
                            self_type_id
                        } else {
                            let tid = self.cv_type_id_from_vir(vir_ty);
                            self.vir_query_lookup_substitute(tid, &type_param_subs)
                                .unwrap_or(tid)
                        }
                    })
                    .collect();
                let subst_ret = if method_def.return_type == VirTypeId::UNKNOWN {
                    self_type_id
                } else {
                    let tid = self.cv_type_id_from_vir(method_def.return_type);
                    self.vir_query_lookup_substitute(tid, &type_param_subs)
                        .unwrap_or(tid)
                };
                self.build_signature_from_type_ids(
                    &subst_params,
                    Some(subst_ret),
                    SelfParam::TypedId(self_type_id),
                )
            };
            let func_key = self.register_method_func(semantic_method_id, &sig, DeclareMode::Import);
            self.state
                .method_func_keys
                .insert((type_name_id, method_name_id), func_key);
        }

        // Import static methods
        for &method_id in &entry.static_methods {
            let method_def = self.analyzed.get_method(method_id);
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            let func_key = self.register_method_func(method_id, &sig, DeclareMode::Import);
            self.state
                .method_func_keys
                .insert((type_name_id, method_def.name_id), func_key);
        }

        Ok(())
    }

    /// Register implement block methods with pre-resolved VIR metadata.
    ///
    /// `interner_override` is `Some` for module implement blocks (where symbols
    /// come from the module's interner rather than the main program interner).
    fn register_implement_block_inner(
        &mut self,
        entry: &VirImplementBlockEntry,
        _interner_override: Option<&Rc<Interner>>,
    ) -> CodegenResult<()> {
        let type_def_id = entry.type_def_id;
        let self_type_id = entry.self_type_id;
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);

        // Declare instance methods as functions
        for &method_id in &entry.instance_methods {
            let method_def = self.analyzed.get_method(method_id);
            let sig = self.build_signature_for_method(method_id, SelfParam::TypedId(self_type_id));
            let func_key = self.register_method_func(method_id, &sig, DeclareMode::Declare);
            self.state
                .method_func_keys
                .insert((type_name_id, method_def.name_id), func_key);
        }

        // Register interface default methods (if this is an implement block with a trait).
        // The explicit methods have been registered above.
        // Default methods (not overridden) also need to be registered so that
        // codegen can find them via method_func_keys at call sites.
        let direct_method_name_ids: std::collections::HashSet<NameId> = entry
            .instance_methods
            .iter()
            .map(|&mid| self.analyzed.get_method(mid).name_id)
            .collect();

        let iface_default_methods =
            self.collect_iface_default_methods(type_def_id, &direct_method_name_ids);

        // Register each default method in the JIT function registry and method_func_keys.
        // Build signatures with Placeholder(SelfType) substituted by self_type_id, and
        // TypeParam(T) substituted with the concrete interface type arg (e.g., i64 for
        // Iterable<i64>), so that the JIT function declaration signature matches what
        // the compiler will emit.
        for (semantic_method_id, method_name_id, interface_tdef_id) in iface_default_methods {
            // Build TypeParam substitution map for this interface's implementation.
            let type_param_subs = self
                .analyzed
                .interface_impl_type_param_subs(type_def_id, interface_tdef_id);
            // Skip registration if any substitution value is still a TypeParam (abstract).
            // Generic interface implementations (e.g., `extend [T] with Iterable<T>`) are
            // handled via monomorphization at the call site, not registered here.
            if !type_param_subs.is_empty() {
                let has_abstract = type_param_subs
                    .values()
                    .any(|&v| self.vir_query_unwrap_type_param(v).is_some());
                if has_abstract {
                    continue;
                }
            }
            let sig = {
                let method_def = self.analyzed.get_method(semantic_method_id);
                let subst_params: Vec<TypeId> = method_def
                    .param_types
                    .iter()
                    .map(|&vir_ty| {
                        if vir_ty == VirTypeId::UNKNOWN {
                            self_type_id
                        } else {
                            let tid = self.cv_type_id_from_vir(vir_ty);
                            self.vir_query_lookup_substitute(tid, &type_param_subs)
                                .unwrap_or(tid)
                        }
                    })
                    .collect();
                let subst_ret = if method_def.return_type == VirTypeId::UNKNOWN {
                    self_type_id
                } else {
                    let tid = self.cv_type_id_from_vir(method_def.return_type);
                    self.vir_query_lookup_substitute(tid, &type_param_subs)
                        .unwrap_or(tid)
                };
                self.build_signature_from_type_ids(
                    &subst_params,
                    Some(subst_ret),
                    SelfParam::TypedId(self_type_id),
                )
            };
            let func_key =
                self.register_method_func(semantic_method_id, &sig, DeclareMode::Declare);
            self.state
                .method_func_keys
                .insert((type_name_id, method_name_id), func_key);
        }

        // Register static methods (VirImplementBlockEntry only includes methods with bodies)
        for &method_id in &entry.static_methods {
            let method_def = self.analyzed.get_method(method_id);
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            let func_key = self.register_method_func(method_id, &sig, DeclareMode::Declare);
            self.state
                .method_func_keys
                .insert((type_name_id, method_def.name_id), func_key);
        }

        Ok(())
    }

    /// Compile implement block methods (second pass).
    ///
    /// Takes pre-resolved VIR metadata instead of walking AST `ImplementBlock`.
    pub(super) fn compile_implement_block(
        &mut self,
        entry: &VirImplementBlockEntry,
    ) -> CodegenResult<()> {
        self.compile_implement_block_inner(entry, None)
    }

    /// Inner implementation for compiling implement block methods.
    ///
    /// `override_module_id` is used for test-scoped implement blocks that need
    /// to resolve types under a virtual module.
    fn compile_implement_block_inner(
        &mut self,
        entry: &VirImplementBlockEntry,
        override_module_id: Option<ModuleId>,
    ) -> CodegenResult<()> {
        let type_def_id = entry.type_def_id;
        let self_type_id = entry.self_type_id;
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);

        // Compile instance methods
        for &method_id in &entry.instance_methods {
            let method_def = self.analyzed.get_method(method_id);
            let method_key = self
                .state
                .method_func_keys
                .get(&(type_name_id, method_def.name_id))
                .map(|&func_key| MethodInfo { func_key });
            self.compile_implement_method_by_id(method_id, self_type_id, method_key, None)?;
        }

        // Compile interface default methods (if this is a trait implement block).
        // These are default methods from the interface that are NOT explicitly implemented.
        // They've been registered in pass 1; now compile their bodies.
        self.compile_iface_default_methods(entry, override_module_id)?;

        // Compile static methods
        self.compile_implement_statics_by_ids(&entry.static_methods, type_def_id, None)?;

        Ok(())
    }

    /// Compile implement block methods from a module.
    /// Handles both instance methods and statics.
    ///
    /// Takes pre-resolved VIR metadata instead of walking AST `ImplementBlock`.
    pub(super) fn compile_module_implement_block(
        &mut self,
        entry: &VirImplementBlockEntry,
        interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_def_id = entry.type_def_id;
        let self_type_id = entry.self_type_id;
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);

        // Compile instance methods using module interner for name resolution
        for &method_id in &entry.instance_methods {
            let method_def = self.analyzed.get_method(method_id);
            let method_key = self
                .state
                .method_func_keys
                .get(&(type_name_id, method_def.name_id))
                .map(|&func_key| MethodInfo { func_key });
            self.compile_module_implement_method_by_id(
                method_id,
                self_type_id,
                method_key,
                interner,
                module_id,
            )?;
        }

        // Compile interface default methods (if this is a trait implement block).
        self.compile_iface_default_methods(entry, None)?;

        // Compile static methods
        self.compile_implement_statics_by_ids(&entry.static_methods, type_def_id, Some(module_id))?;

        Ok(())
    }

    /// Compile a single method from a module implement block, using a module interner.
    ///
    /// Takes a pre-resolved `MethodId` instead of walking an AST `FuncDecl`.
    fn compile_module_implement_method_by_id(
        &mut self,
        method_id: MethodId,
        self_type_id: TypeId,
        method_info: Option<MethodInfo>,
        interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let func_key = if let Some(info) = method_info {
            info.func_key
        } else {
            let method_def = self.analyzed.get_method(method_id);
            self.func_registry.intern_name_id(method_def.full_name_id)
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        let sig = self.build_signature_for_method(method_id, SelfParam::TypedId(self_type_id));
        self.jit.ctx.func.signature = sig;

        let self_cranelift_type = self.vir_query_type_to_cranelift(self_type_id);

        let source_file_ptr = self.source_file_ptr();
        // Use module interner to look up "self"
        let self_sym = interner.lookup("self").ok_or_else(|| {
            CodegenError::internal("'self' keyword not interned in module interner")
        })?;

        // Build params from VirMethodDef.param_names (excluding self).
        let params = self.build_method_params_from_vir(method_id, interner)?;

        let method_return_type_id = {
            let method_def = self.analyzed.get_method(method_id);
            Some(self.cv_type_id_from_vir(method_def.return_type))
        };

        // Get the VIR function (must be available — implement block methods are always lowered)
        let vir_func = self.analyzed.get_vir_method(method_id).unwrap_or_else(|| {
            panic!("VIR must be available for module implement method (MethodId={method_id:?})")
        });

        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            // Use module interner for compilation
            let env = compile_env!(self, interner, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let self_binding = (self_sym, self_type_id, self_cranelift_type);
            let config = FunctionCompileConfig::method(params, self_binding, method_return_type_id);
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir_func.body,
                Some(module_id),
                None,
            )?;
        }

        self.finalize_function(func_id)?;
        Ok(())
    }

    /// Compile static methods from pre-resolved MethodIds.
    ///
    /// Takes a slice of `MethodId`s (from `VirImplementBlockEntry.static_methods`)
    /// instead of walking an AST `StaticsBlock`.
    fn compile_implement_statics_by_ids(
        &mut self,
        static_method_ids: &[MethodId],
        type_def_id: TypeDefId,
        module_id: Option<ModuleId>,
    ) -> CodegenResult<()> {
        for &method_id in static_method_ids {
            // Look up the registered function via its full NameId
            let func_key = self
                .func_registry
                .intern_name_id(self.analyzed.method_full_name(method_id));
            let jit_func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!("{:?}::{:?}", type_def_id, method_id),
                )
            })?;

            // Use VIR method definition for param/return types
            let method_def = self.analyzed.get_method(method_id);
            let param_vir_types = method_def.param_types.clone();
            let return_vir_type = method_def.return_type;
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            let return_type_id = {
                let tid = self.cv_type_id_from_vir(return_vir_type);
                Some(tid).filter(|r| !r.is_void())
            };
            self.jit.ctx.func.signature = sig;

            // Build param info from VirMethodDef.param_names
            let interner = self.interner_for_module(module_id);
            let table = self.vir_type_table();
            let method_def = self.analyzed.get_method(method_id);
            let params: Vec<_> = method_def
                .param_names
                .iter()
                .zip(param_vir_types.iter())
                .map(|(name_str, &vir_ty)| {
                    let sym = interner.lookup(name_str).unwrap_or_else(|| {
                        self.analyzed
                            .interner()
                            .lookup(name_str)
                            .unwrap_or_else(|| panic!("param name '{}' not interned", name_str))
                    });
                    let cranelift_type = vir_type_to_cranelift(vir_ty, table, self.pointer_type);
                    let type_id = self.cv_type_id_from_vir(vir_ty);
                    (sym, type_id, cranelift_type)
                })
                .collect();

            // Get source file pointer
            let source_file_ptr = self.source_file_ptr();

            // Create function builder and compile
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                // Use module interner when compiling module statics
                let env = if module_id.is_some() {
                    compile_env!(self, &interner, source_file_ptr)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(params, return_type_id);

                // VIR path — all implement block statics are lowered
                let vir_func = self
                    .analyzed
                    .get_vir_method(method_id)
                    .expect("implement block static method should have VIR");
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
                    module_id,
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(jit_func_id)?;
        }

        Ok(())
    }

    /// Compile a method from an implement block by MethodId.
    ///
    /// Takes a pre-resolved `MethodId` instead of walking an AST `FuncDecl`.
    /// `interner_override` is for module methods; pass `None` for main program.
    fn compile_implement_method_by_id(
        &mut self,
        method_id: MethodId,
        self_type_id: TypeId,
        method_info: Option<MethodInfo>,
        interner_override: Option<&Interner>,
    ) -> CodegenResult<()> {
        let func_key = if let Some(info) = method_info {
            info.func_key
        } else {
            let method_def = self.analyzed.get_method(method_id);
            self.func_registry.intern_name_id(method_def.full_name_id)
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        let sig = self.build_signature_for_method(method_id, SelfParam::TypedId(self_type_id));
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self (using TypeId)
        let self_cranelift_type = self.vir_query_type_to_cranelift(self_type_id);

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Build params from VirMethodDef.param_names (excluding self)
        let interner = interner_override.unwrap_or(self.analyzed.interner());
        let params = self.build_method_params_from_vir(method_id, interner)?;

        // Get the method's return type from VIR method definition
        let method_return_type_id = {
            let method_def = self.analyzed.get_method(method_id);
            Some(self.cv_type_id_from_vir(method_def.return_type))
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

            let self_binding = (self_sym, self_type_id, self_cranelift_type);
            let config = FunctionCompileConfig::method(params, self_binding, method_return_type_id);

            // VIR path — all implement block methods are lowered
            let vir_func = self
                .analyzed
                .get_vir_method(method_id)
                .expect("implement block method should have VIR");
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir_func.body,
                None,
                None,
            )?;
        }

        // Define the function (skip if already defined by an overlapping implement block)
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Find the interner and module_id for an interface's default method.
    ///
    /// Searches main program and all module programs for the interface by name,
    /// then finds the method by name. Returns the interner that owns the method's
    /// symbols and the module_id (if from a module).
    ///
    /// Returns None if the interface or method is not found.
    fn find_interface_method_interner(
        &self,
        interface_name_str: &str,
        method_name_str: &str,
    ) -> Option<(Rc<Interner>, Option<ModuleId>)> {
        // Find the interface TypeDefId by short name
        let iface_tdef_id = self.analyzed.type_by_short_name(interface_name_str)?;

        // Verify it's an interface
        if !self.analyzed.is_interface_type(iface_tdef_id) {
            return None;
        }

        // Find the method by name string
        let method_name_id = self.analyzed.try_method_name_id_by_str(method_name_str)?;
        let method_id = self.analyzed.find_method(iface_tdef_id, method_name_id)?;
        let method_def = self.analyzed.get_method(method_id);

        // Only return if the method has a default body
        if !method_def.has_default {
            return None;
        }

        // Determine the module for this interface
        let iface_type_def = self.analyzed.get_type(iface_tdef_id);
        let iface_module_id = iface_type_def.module;
        let program_module = self.program_module();

        if iface_module_id == program_module {
            // Interface is in the main program
            Some((self.analyzed.interner_rc(), None))
        } else {
            // Interface is in a module — get its interner
            let module_path = self.analyzed.name_table().module_path(iface_module_id);
            let interner = self
                .analyzed
                .vir_program()
                .module_interner_rc(module_path)?;
            Some((interner, Some(iface_module_id)))
        }
    }

    /// Build `(Symbol, TypeId, cranelift::Type)` param triples from VirMethodDef.
    ///
    /// Uses `VirMethodDef.param_names` to look up Symbols in the given interner.
    /// Excludes the `self` parameter (handled separately via self_binding).
    fn build_method_params_from_vir(
        &self,
        method_id: MethodId,
        interner: &Interner,
    ) -> CodegenResult<Vec<(Symbol, TypeId, types::Type)>> {
        let method_def = self.analyzed.get_method(method_id);
        let table = self.vir_type_table();
        let params = method_def
            .param_names
            .iter()
            .zip(method_def.param_types.iter())
            .map(|(name_str, &vir_ty)| {
                let sym = interner
                    .lookup(name_str)
                    .or_else(|| self.analyzed.interner().lookup(name_str))
                    .unwrap_or_else(|| {
                        panic!(
                            "param name '{}' not interned for method {:?}",
                            name_str, method_id
                        )
                    });
                let cranelift_type = vir_type_to_cranelift(vir_ty, table, self.pointer_type);
                let type_id = self.cv_type_id_from_vir(vir_ty);
                (sym, type_id, cranelift_type)
            })
            .collect();
        Ok(params)
    }

    /// Get the appropriate interner for a module, falling back to the program interner.
    fn interner_for_module(&self, module_id: Option<ModuleId>) -> Rc<Interner> {
        if let Some(mod_id) = module_id {
            let module_path = self.analyzed.name_table().module_path(mod_id);
            if let Some(interner) = self.analyzed.vir_program().module_interner_rc(module_path) {
                return interner;
            }
        }
        self.analyzed.interner_rc()
    }

    /// Collect interface default methods that are NOT explicitly implemented.
    ///
    /// Returns `(impl_method_id, method_name_id, interface_tdef_id)` triples.
    fn collect_iface_default_methods(
        &self,
        type_def_id: TypeDefId,
        direct_method_name_ids: &std::collections::HashSet<NameId>,
    ) -> Vec<(MethodId, NameId, TypeDefId)> {
        let query = self.analyzed;
        let mut results = Vec::new();
        for interface_tdef_id in query.implemented_interfaces(type_def_id) {
            for iface_method_id in query.type_methods(interface_tdef_id) {
                let method_def = query.get_method(iface_method_id);
                if !method_def.has_default {
                    continue;
                }
                // Skip external default methods - they are provided by the runtime,
                // not compiled from Vole source.
                if method_def.external_binding.is_some() {
                    continue;
                }
                // Skip explicitly implemented methods
                if direct_method_name_ids.contains(&method_def.name_id) {
                    continue;
                }
                // Find the method as registered on the implementing type
                if let Some(impl_method_id) = query.find_method(type_def_id, method_def.name_id) {
                    results.push((impl_method_id, method_def.name_id, interface_tdef_id));
                }
            }
        }
        results
    }

    /// Compile interface default method bodies for an implement block.
    ///
    /// These are default methods from interfaces that are NOT explicitly implemented.
    /// They were registered in pass 1; this function compiles their bodies.
    fn compile_iface_default_methods(
        &mut self,
        entry: &VirImplementBlockEntry,
        _override_module_id: Option<ModuleId>,
    ) -> CodegenResult<()> {
        let type_def_id = entry.type_def_id;
        let self_type_id = entry.self_type_id;
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);

        // Collect direct method NameIds to skip explicitly implemented ones
        let direct_method_name_ids: std::collections::HashSet<NameId> = entry
            .instance_methods
            .iter()
            .map(|&mid| self.analyzed.get_method(mid).name_id)
            .collect();

        // Collect (interface_name_str, default_method_id, method_name_id, interface_tdef_id)
        let iface_default_method_ids: Vec<(String, MethodId, NameId, TypeDefId)> = {
            let query = self.analyzed;
            let mut results = Vec::new();
            for interface_tdef_id in query.implemented_interfaces(type_def_id) {
                let iface_name_str = query
                    .last_segment(query.entity_type_name_id(interface_tdef_id))
                    .unwrap_or_default();
                for iface_method_id in query.type_methods(interface_tdef_id) {
                    let method_def = query.get_method(iface_method_id);
                    if !method_def.has_default {
                        continue;
                    }
                    if method_def.external_binding.is_some() {
                        continue;
                    }
                    if direct_method_name_ids.contains(&method_def.name_id) {
                        continue;
                    }
                    if let Some(impl_method_id) = query.find_method(type_def_id, method_def.name_id)
                    {
                        results.push((
                            iface_name_str.clone(),
                            impl_method_id,
                            method_def.name_id,
                            interface_tdef_id,
                        ));
                    }
                }
            }
            results
        };

        for (iface_name_str, semantic_method_id, method_name_id, interface_tdef_id) in
            iface_default_method_ids
        {
            // Look up function key (registered in pass 1)
            let func_key = match self
                .state
                .method_func_keys
                .get(&(type_name_id, method_name_id))
            {
                Some(&k) => k,
                None => continue,
            };
            let func_id = match self.func_registry.func_id(func_key) {
                Some(id) => id,
                None => continue,
            };

            // Skip if the function was imported from cache (Import linkage).
            if !self.jit.is_local_func_id(func_id) {
                continue;
            }

            // Get method_name_str for searching the interface decl
            let method_name_str = self
                .analyzed
                .name_table()
                .last_segment_str(method_name_id)
                .unwrap_or_default();

            // Find the interface's interner and module_id
            let iface_info = self.find_interface_method_interner(&iface_name_str, &method_name_str);
            let Some((iface_interner, iface_module_id)) = iface_info else {
                continue;
            };

            // Build type-parameter substitution map for this interface implementation.
            let type_param_subs = self
                .analyzed
                .interface_impl_type_param_subs(type_def_id, interface_tdef_id);

            // Skip compilation if any substitution value is still a TypeParam (abstract/generic).
            if !type_param_subs.is_empty() {
                let has_abstract = type_param_subs
                    .values()
                    .any(|&v| self.vir_query_unwrap_type_param(v).is_some());
                if has_abstract {
                    continue;
                }
            }

            // Get signature data from VIR method definition, substituting:
            //   1. VirTypeId::UNKNOWN (Self placeholder) -> self_type_id
            //   2. TypeParam(T) -> concrete element type (via type_param_subs)
            let method_def = self.analyzed.get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let subst_params: Vec<TypeId> = method_def
                    .param_types
                    .iter()
                    .map(|&vir_ty| {
                        if vir_ty == VirTypeId::UNKNOWN {
                            self_type_id
                        } else {
                            let tid = self.cv_type_id_from_vir(vir_ty);
                            self.vir_query_lookup_substitute(tid, &type_param_subs)
                                .unwrap_or(tid)
                        }
                    })
                    .collect();
                let subst_ret = if method_def.return_type == VirTypeId::UNKNOWN {
                    self_type_id
                } else {
                    let tid = self.cv_type_id_from_vir(method_def.return_type);
                    self.vir_query_lookup_substitute(tid, &type_param_subs)
                        .unwrap_or(tid)
                };
                (subst_params, subst_ret)
            };

            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(return_type_id),
                SelfParam::TypedId(self_type_id),
            );
            self.jit.ctx.func.signature = sig;

            // Build params from VirMethodDef.param_names using the interface's interner
            let method_def = self.analyzed.get_method(semantic_method_id);
            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method_def
                .param_names
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((name_str, &type_id), &cranelift_type)| {
                    let sym = iface_interner
                        .lookup(name_str)
                        .or_else(|| self.analyzed.interner().lookup(name_str))
                        .unwrap_or_else(|| {
                            panic!(
                                "param name '{}' not interned for default method {:?}",
                                name_str, semantic_method_id
                            )
                        });
                    (sym, type_id, cranelift_type)
                })
                .collect();

            let self_sym = iface_interner
                .lookup("self")
                .unwrap_or_else(|| self.self_symbol());

            let source_file_ptr = self.source_file_ptr();
            let self_cranelift_type = self.vir_query_type_to_cranelift(self_type_id);
            let self_binding = (self_sym, self_type_id, self_cranelift_type);

            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(self, &iface_interner, source_file_ptr);
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );
                let mut config =
                    FunctionCompileConfig::method(params, self_binding, Some(return_type_id));
                if self
                    .analyzed
                    .name_table()
                    .well_known
                    .is_iterable_type_def(interface_tdef_id)
                {
                    config = config.with_iterable_default_body();
                }
                let subs = if type_param_subs.is_empty() {
                    None
                } else {
                    Some(&type_param_subs)
                };
                let vir_func = self
                    .analyzed
                    .get_vir_method(semantic_method_id)
                    .expect("implement block default method should have VIR");
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
                    iface_module_id,
                    subs,
                )?;
            }
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Declare and compile array Iterable default methods for each concrete element type.
    ///
    /// Called after `declare_module_types_and_functions` so all types are registered.
    ///
    /// For each concrete RuntimeIterator element type (e.g. i64, string) found in the arena,
    /// and for each non-external Iterable default method registered on the array TypeDef,
    /// this function:
    ///   1. Builds a concrete substitution `{T_name_id -> elem_type}`
    ///   2. Declares a JIT function with a mangled name (e.g. "__array_iterable_4_count")
    ///   3. Registers the func_key in `state.array_iterable_func_keys[(method_name_id, elem_type)]`
    ///   4. Compiles the Iterable default method body with the concrete substitution
    pub(super) fn compile_array_iterable_default_methods(&mut self) -> CodegenResult<()> {
        // Get array TypeDefId and Iterable TypeDefId
        let array_tdef_id = {
            let array_name_id = match self.analyzed.array_type_name_id() {
                Some(id) => id,
                None => return Ok(()), // array not registered, nothing to do
            };
            match self.analyzed.try_type_def_id(array_name_id) {
                Some(id) => id,
                None => return Ok(()),
            }
        };

        // Find Iterable TypeDefId (the interface array implements)
        let iterable_tdef_id = {
            let interfaces = self.analyzed.implemented_interfaces(array_tdef_id);
            if interfaces.is_empty() {
                return Ok(());
            }
            interfaces[0] // array implements exactly one interface: Iterable<T>
        };

        // Find T's NameId from the abstract substitution map {T_name_id -> TypeParam(T)}
        let t_name_id: NameId = {
            let subs = self
                .analyzed
                .interface_impl_type_param_subs(array_tdef_id, iterable_tdef_id);
            if subs.is_empty() {
                return Ok(());
            }
            // For `extend [T] with Iterable<T>`, T's value is TypeParam(T_name_id)
            // Get the first (only) T's NameId — the key in the subs map IS T's NameId
            match subs.into_keys().next() {
                Some(name_id) => name_id,
                None => return Ok(()),
            }
        };

        // Get the interface name string for find_interface_method_interner
        let iface_name_str: String = {
            let iface_name_id = self.analyzed.entity_type_name_id(iterable_tdef_id);
            self.analyzed
                .name_table()
                .last_segment_str(iface_name_id)
                .unwrap_or("Iterable".to_string())
        };

        // Collect non-external Iterable default methods registered on the array type
        // We skip external methods (provided by runtime, not compiled from Vole source)
        let default_methods: Vec<(MethodId, NameId, String)> = {
            let query = self.analyzed;
            let mut results = Vec::new();
            for iface_method_id in query.type_methods(iterable_tdef_id) {
                let method_def = query.get_method(iface_method_id);
                if !method_def.has_default {
                    continue;
                }
                if method_def.external_binding.is_some() {
                    continue; // External methods are already handled by runtime
                }
                let method_name_str = query
                    .last_segment(method_def.name_id)
                    .unwrap_or_default()
                    .to_string();
                // Find this method as registered on the array implementing type
                if let Some(array_method_id) = query.find_method(array_tdef_id, method_def.name_id)
                {
                    results.push((array_method_id, method_def.name_id, method_name_str));
                }
            }
            results
        };

        if default_methods.is_empty() {
            return Ok(());
        }

        // Get all concrete element types for which we need to compile array Iterable methods
        let elem_types: Vec<TypeId> = self.vir_query_all_concrete_runtime_iterator_elem_types();

        for elem_type in elem_types {
            // Get the concrete array TypeId for this element type
            let self_type_id = match self.vir_query_lookup_array(elem_type) {
                Some(tid) => tid,
                None => continue, // No array of this elem type in arena, skip
            };

            // Skip element types whose iterable methods were already imported from
            // the module cache. Check the first default method as a sentinel — all
            // methods for an element type are imported/compiled as a batch.
            if let Some((_, first_name_id, _)) = default_methods.first()
                && self
                    .state
                    .array_iterable_func_keys
                    .contains_key(&(*first_name_id, self_type_id))
            {
                continue;
            }

            // Build concrete substitution: T_name_id -> elem_type
            let mut concrete_subs = FxHashMap::default();
            concrete_subs.insert(t_name_id, elem_type);

            for (semantic_method_id, method_name_id, method_name_str) in &default_methods {
                // Build a unique mangled name: "__array_iterable_{elem_type_idx}_{method_name}"
                // elem_type.index() is a stable u32 index that uniquely identifies the type.
                let mangled_name =
                    format!("__array_iterable_{}_{}", elem_type.index(), method_name_str);

                // Build the concrete signature (substituting Self -> self_type_id, T -> elem_type)
                // If any return type substitution fails (e.g. T? not registered in arena for
                // this elem_type), skip this method — it can't be compiled without a concrete
                // return type. Params fall back to abstract type on failure (safe for ptr-size).
                let maybe_type_ids: Option<(Vec<TypeId>, TypeId)> = {
                    let method_def = self.analyzed.get_method(*semantic_method_id);
                    let subst_params: Vec<TypeId> = method_def
                        .param_types
                        .iter()
                        .map(|&vir_ty| {
                            if vir_ty == VirTypeId::UNKNOWN {
                                self_type_id
                            } else {
                                let tid = self.cv_type_id_from_vir(vir_ty);
                                self.vir_query_lookup_substitute(tid, &concrete_subs)
                                    .unwrap_or(tid)
                            }
                        })
                        .collect();
                    let subst_ret = if method_def.return_type == VirTypeId::UNKNOWN {
                        Some(self_type_id)
                    } else {
                        let tid = self.cv_type_id_from_vir(method_def.return_type);
                        self.vir_query_lookup_substitute(tid, &concrete_subs)
                    };
                    subst_ret.map(|ret| (subst_params, ret))
                };
                let (param_type_ids, return_type_id) = match maybe_type_ids {
                    Some(x) => x,
                    None => continue, // return type unresolvable for this elem_type; skip
                };

                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    SelfParam::TypedId(self_type_id),
                );

                // Declare JIT function with the mangled name and register in func_registry
                let func_id = self.jit.declare_function(&mangled_name, &sig);
                let func_key = self.func_registry.intern_raw(mangled_name);
                self.func_registry.set_func_id(func_key, func_id);

                // Register in array_iterable_func_keys for call-site lookup.
                // Key is (method_name_id, self_type_id) so arrays and primitives (range)
                // can each have their own compiled function for the same method.
                self.state
                    .array_iterable_func_keys
                    .insert((*method_name_id, self_type_id), func_key);

                // Find the interface's interner and module_id
                let iface_info =
                    self.find_interface_method_interner(&iface_name_str, method_name_str);
                let Some((iface_interner, iface_module_id)) = iface_info else {
                    continue;
                };

                // Set the function signature for compilation
                self.jit.ctx.func.signature = sig;

                // Build params from VirMethodDef.param_names using the interface's interner
                let method_def = self.analyzed.get_method(*semantic_method_id);
                let param_types = self.type_ids_to_cranelift(&param_type_ids);
                let params: Vec<_> = method_def
                    .param_names
                    .iter()
                    .zip(param_type_ids.iter())
                    .zip(param_types.iter())
                    .map(|((name_str, &type_id), &cranelift_type)| {
                        let sym = iface_interner
                            .lookup(name_str)
                            .or_else(|| self.analyzed.interner().lookup(name_str))
                            .unwrap_or_else(|| {
                                panic!(
                                    "param name '{}' not interned for iterable default method",
                                    name_str
                                )
                            });
                        (sym, type_id, cranelift_type)
                    })
                    .collect();

                let self_sym = iface_interner
                    .lookup("self")
                    .unwrap_or_else(|| self.self_symbol());

                let source_file_ptr = self.source_file_ptr();
                let self_cranelift_type = self.vir_query_type_to_cranelift(self_type_id);
                let self_binding = (self_sym, self_type_id, self_cranelift_type);

                let mut builder_ctx = FunctionBuilderContext::new();
                {
                    let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                    let env = compile_env!(self, &iface_interner, source_file_ptr);
                    let mut codegen_ctx = CodegenCtx::new(
                        &mut self.jit.module,
                        &mut self.func_registry,
                        &mut self.pending_monomorphs,
                    );
                    let config =
                        FunctionCompileConfig::method(params, self_binding, Some(return_type_id))
                            .with_iterable_default_body();
                    let vir_func = self.analyzed.get_vir_method(*semantic_method_id)
                        .unwrap_or_else(|| {
                            panic!("VIR must be available for array iterable default method (MethodId={semantic_method_id:?})")
                        });
                    compile_function_inner_with_vir(
                        builder,
                        &mut codegen_ctx,
                        &env,
                        config,
                        &vir_func.body,
                        iface_module_id,
                        Some(&concrete_subs),
                    )?;
                }
                self.finalize_function(func_id)?;
            }
        }

        Ok(())
    }

    /// Import (not compile) array Iterable default methods from a pre-compiled module cache.
    ///
    /// Called in the module cache path (when `can_use_cache == true`) instead of
    /// `compile_array_iterable_default_methods`. The functions were already compiled
    /// and stored in `CompiledModules`. This function:
    ///   1. Rebuilds the same mangled names as `compile_array_iterable_default_methods`
    ///   2. Declares them with Import linkage in the new JIT context
    ///   3. Registers them in `state.array_iterable_func_keys[(method_name_id, self_type_id)]`
    ///
    /// Must be called after `import_module_functions` sets up type metadata.
    pub(super) fn import_array_iterable_default_methods(&mut self) -> CodegenResult<()> {
        // Get array TypeDefId and Iterable TypeDefId
        let array_tdef_id = {
            let array_name_id = match self.analyzed.array_type_name_id() {
                Some(id) => id,
                None => return Ok(()),
            };
            match self.analyzed.try_type_def_id(array_name_id) {
                Some(id) => id,
                None => return Ok(()),
            }
        };

        let iterable_tdef_id = {
            let interfaces = self.analyzed.implemented_interfaces(array_tdef_id);
            if interfaces.is_empty() {
                return Ok(());
            }
            interfaces[0]
        };

        let t_name_id: NameId = {
            let subs = self
                .analyzed
                .interface_impl_type_param_subs(array_tdef_id, iterable_tdef_id);
            if subs.is_empty() {
                return Ok(());
            }
            match subs.into_keys().next() {
                Some(name_id) => name_id,
                None => return Ok(()),
            }
        };

        let default_methods: Vec<(MethodId, NameId, String)> = {
            let query = self.analyzed;
            let mut results = Vec::new();
            for iface_method_id in query.type_methods(iterable_tdef_id) {
                let method_def = query.get_method(iface_method_id);
                if !method_def.has_default || method_def.external_binding.is_some() {
                    continue;
                }
                let method_name_str = query
                    .last_segment(method_def.name_id)
                    .unwrap_or_default()
                    .to_string();
                if let Some(array_method_id) = query.find_method(array_tdef_id, method_def.name_id)
                {
                    results.push((array_method_id, method_def.name_id, method_name_str));
                }
            }
            results
        };

        if default_methods.is_empty() {
            return Ok(());
        }

        let elem_types: Vec<TypeId> = self.vir_query_all_concrete_runtime_iterator_elem_types();

        for elem_type in elem_types {
            let self_type_id = match self.vir_query_lookup_array(elem_type) {
                Some(tid) => tid,
                None => continue,
            };

            let mut concrete_subs = FxHashMap::default();
            concrete_subs.insert(t_name_id, elem_type);

            for (semantic_method_id, method_name_id, method_name_str) in &default_methods {
                let mangled_name =
                    format!("__array_iterable_{}_{}", elem_type.index(), method_name_str);

                // Build the concrete signature (same as compile path)
                let maybe_type_ids: Option<(Vec<TypeId>, TypeId)> = {
                    let method_def = self.analyzed.get_method(*semantic_method_id);
                    let subst_params: Vec<TypeId> = method_def
                        .param_types
                        .iter()
                        .map(|&vir_ty| {
                            if vir_ty == VirTypeId::UNKNOWN {
                                self_type_id
                            } else {
                                let tid = self.cv_type_id_from_vir(vir_ty);
                                self.vir_query_lookup_substitute(tid, &concrete_subs)
                                    .unwrap_or(tid)
                            }
                        })
                        .collect();
                    let subst_ret = if method_def.return_type == VirTypeId::UNKNOWN {
                        Some(self_type_id)
                    } else {
                        let tid = self.cv_type_id_from_vir(method_def.return_type);
                        self.vir_query_lookup_substitute(tid, &concrete_subs)
                    };
                    subst_ret.map(|ret| (subst_params, ret))
                };
                let (param_type_ids, return_type_id) = match maybe_type_ids {
                    Some(x) => x,
                    None => continue,
                };

                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    SelfParam::TypedId(self_type_id),
                );

                // Only import functions that exist in the pre-compiled module cache.
                // Element types from non-module code (e.g. test files) won't have
                // compiled iterable methods in the cache.
                if !self.jit.has_precompiled_symbol(&mangled_name) {
                    continue;
                }
                let func_id = self.jit.import_function(&mangled_name, &sig);
                let func_key = self.func_registry.intern_raw(mangled_name);
                self.func_registry.set_func_id(func_key, func_id);

                self.state
                    .array_iterable_func_keys
                    .insert((*method_name_id, self_type_id), func_key);
            }
        }

        Ok(())
    }
}
