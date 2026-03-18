//! Implement block registration and compilation.
//!
//! This module handles the "how-to-instantiate" logic for implement blocks:
//! - Implement block registration (first pass): `register_implement_block*`
//! - Implement block compilation (second pass): `compile_implement_block*`
//! - Module implement block compilation: `compile_module_implement_block`
//! - Individual implement method compilation: `compile_implement_method`, `compile_module_implement_method`
//! - Implement statics compilation: `compile_implement_statics`
//! - Interface interner resolution: `find_interface_method_interner`
//! - VIR implement method monomorphs: resolved via `VirProgram.implement_method_monomorphs`

use std::rc::Rc;

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::{Compiler, DeclareMode, SelfParam, VirSelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::vir_conversions::vir_type_to_cranelift;
use crate::types::{CodegenCtx, MethodInfo};
use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use vole_identity::{
    ImplementMethodMonomorphKey, Interner, MethodId, ModuleId, NameId, Symbol, TypeDefId, TypeId,
    VirTypeId,
};
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
            let method_def = self.analyzed.get_method_def(method_id);
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
            .map(|&mid| self.analyzed.get_method_def(mid).name_id)
            .collect();

        let iface_default_methods =
            self.collect_iface_default_methods(type_def_id, &direct_method_name_ids);

        let self_vir_ty = self.vir_lookup(self_type_id);
        for (semantic_method_id, method_name_id, interface_tdef_id) in iface_default_methods {
            // Build VirTypeId-native substitution map for this interface implementation.
            let vir_subs = self
                .analyzed
                .interface_impl_type_param_vir_subs(type_def_id, interface_tdef_id);
            // Skip abstract/generic default methods (not compiled in the module).
            if !vir_subs.is_empty() {
                let has_abstract = vir_subs
                    .values()
                    .any(|&v| self.vir_query_unwrap_type_param_v(v).is_some());
                if has_abstract {
                    continue;
                }
            }
            let method_def = self.analyzed.get_method_def(semantic_method_id);
            let sig = self
                .build_substituted_method_sig(
                    &method_def.param_types,
                    method_def.return_type,
                    self_vir_ty,
                    &vir_subs,
                    VirSelfParam::Typed(self_vir_ty),
                )
                .unwrap_or_else(|| {
                    self.build_signature_for_method(
                        semantic_method_id,
                        SelfParam::TypedId(self_type_id),
                    )
                });
            let func_key = self.register_method_func(semantic_method_id, &sig, DeclareMode::Import);
            self.state
                .method_func_keys
                .insert((type_name_id, method_name_id), func_key);
        }

        // Import static methods
        for &method_id in &entry.static_methods {
            let method_def = self.analyzed.get_method_def(method_id);
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
            let method_def = self.analyzed.get_method_def(method_id);
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
            .map(|&mid| self.analyzed.get_method_def(mid).name_id)
            .collect();

        let iface_default_methods =
            self.collect_iface_default_methods(type_def_id, &direct_method_name_ids);

        // Register each default method in the JIT function registry and method_func_keys.
        // Build signatures with UNKNOWN (Self placeholder) substituted by self_vir_ty,
        // and TypeParam(T) substituted with the concrete interface type arg (e.g., i64
        // for Iterable<i64>), so that the JIT declaration signature matches the emitted code.
        let self_vir_ty = self.vir_lookup(self_type_id);
        for (semantic_method_id, method_name_id, interface_tdef_id) in iface_default_methods {
            // Build VirTypeId-native substitution map for this interface's implementation.
            let vir_subs = self
                .analyzed
                .interface_impl_type_param_vir_subs(type_def_id, interface_tdef_id);
            // Skip registration if any substitution value is still a TypeParam (abstract).
            // Generic interface implementations (e.g., `extend [T] with Iterable<T>`) are
            // handled via monomorphization at the call site, not registered here.
            if !vir_subs.is_empty() {
                let has_abstract = vir_subs
                    .values()
                    .any(|&v| self.vir_query_unwrap_type_param_v(v).is_some());
                if has_abstract {
                    continue;
                }
            }
            let method_def = self.analyzed.get_method_def(semantic_method_id);
            let sig = self
                .build_substituted_method_sig(
                    &method_def.param_types,
                    method_def.return_type,
                    self_vir_ty,
                    &vir_subs,
                    VirSelfParam::Typed(self_vir_ty),
                )
                .unwrap_or_else(|| {
                    self.build_signature_for_method(
                        semantic_method_id,
                        SelfParam::TypedId(self_type_id),
                    )
                });
            let func_key =
                self.register_method_func(semantic_method_id, &sig, DeclareMode::Declare);
            self.state
                .method_func_keys
                .insert((type_name_id, method_name_id), func_key);
        }

        // Register static methods (VirImplementBlockEntry only includes methods with bodies)
        for &method_id in &entry.static_methods {
            let method_def = self.analyzed.get_method_def(method_id);
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
            let method_def = self.analyzed.get_method_def(method_id);
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
            let method_def = self.analyzed.get_method_def(method_id);
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
            let method_def = self.analyzed.get_method_def(method_id);
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

        let method_return_vir_ty = {
            let method_def = self.analyzed.get_method_def(method_id);
            Some(method_def.return_type)
        };

        // Get the VIR function (must be available — implement block methods are always lowered)
        let vir_func = self.analyzed.get_method(method_id).unwrap_or_else(|| {
            panic!("VIR must be available for module implement method (MethodId={method_id:?})")
        });

        let self_vir_ty = self.vir_lookup(self_type_id);
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

            let self_binding = (self_sym, self_vir_ty, self_cranelift_type);
            let config = FunctionCompileConfig::method(params, self_binding, method_return_vir_ty);
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
            let method_def = self.analyzed.get_method_def(method_id);
            let param_vir_types = method_def.param_types.clone();
            let return_vir_type = method_def.return_type;
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            let return_vir_ty_opt = if return_vir_type == VirTypeId::VOID {
                None
            } else {
                Some(return_vir_type)
            };
            self.jit.ctx.func.signature = sig;

            // Build param info from VirMethodDef.param_names
            let interner = self.interner_for_module(module_id);
            let table = self.vir_type_table();
            let method_def = self.analyzed.get_method_def(method_id);
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
                    (sym, vir_ty, cranelift_type)
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

                let config = FunctionCompileConfig::top_level(params, return_vir_ty_opt);

                // VIR path — all implement block statics are lowered
                let vir_func = self
                    .analyzed
                    .get_method(method_id)
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
            let method_def = self.analyzed.get_method_def(method_id);
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
        let method_return_vir_ty = {
            let method_def = self.analyzed.get_method_def(method_id);
            Some(method_def.return_type)
        };

        // Create function builder and compile
        let self_vir_ty = self.vir_lookup(self_type_id);
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

            let self_binding = (self_sym, self_vir_ty, self_cranelift_type);
            let config = FunctionCompileConfig::method(params, self_binding, method_return_vir_ty);

            // VIR path — all implement block methods are lowered
            let vir_func = self
                .analyzed
                .get_method(method_id)
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
        let method_def = self.analyzed.get_method_def(method_id);

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
            let interner = self.analyzed.module_interner_rc(module_path)?;
            Some((interner, Some(iface_module_id)))
        }
    }

    /// Build `(Symbol, VirTypeId, cranelift::Type)` param triples from VirMethodDef.
    ///
    /// Uses `VirMethodDef.param_names` to look up Symbols in the given interner.
    /// Excludes the `self` parameter (handled separately via self_binding).
    fn build_method_params_from_vir(
        &self,
        method_id: MethodId,
        interner: &Interner,
    ) -> CodegenResult<Vec<(Symbol, VirTypeId, types::Type)>> {
        let method_def = self.analyzed.get_method_def(method_id);
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
                (sym, vir_ty, cranelift_type)
            })
            .collect();
        Ok(params)
    }

    /// Get the appropriate interner for a module, falling back to the program interner.
    fn interner_for_module(&self, module_id: Option<ModuleId>) -> Rc<Interner> {
        if let Some(mod_id) = module_id {
            let module_path = self.analyzed.name_table().module_path(mod_id);
            if let Some(interner) = self.analyzed.module_interner_rc(module_path) {
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
                let method_def = query.get_method_def(iface_method_id);
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
            .map(|&mid| self.analyzed.get_method_def(mid).name_id)
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
                    let method_def = query.get_method_def(iface_method_id);
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

            // Build VirTypeId-native substitution map for this interface implementation.
            let vir_subs = self
                .analyzed
                .interface_impl_type_param_vir_subs(type_def_id, interface_tdef_id);

            // Skip compilation if any substitution value is still a TypeParam (abstract/generic).
            if !vir_subs.is_empty() {
                let has_abstract = vir_subs
                    .values()
                    .any(|&v| self.vir_query_unwrap_type_param_v(v).is_some());
                if has_abstract {
                    continue;
                }
            }

            // Substitute VirTypeIds: UNKNOWN → self, TypeParam(T) → concrete type.
            let self_vir_ty = self.vir_lookup(self_type_id);
            let method_def = self.analyzed.get_method_def(semantic_method_id);
            let (subst_param_virs, return_vir_ty) = self
                .substitute_method_vir_types(
                    &method_def.param_types,
                    method_def.return_type,
                    self_vir_ty,
                    &vir_subs,
                )
                .unwrap_or_else(|| {
                    // Fallback: keep original types (safe for ptr-sized)
                    (
                        method_def.param_types.clone().into(),
                        method_def.return_type,
                    )
                });

            let struct_slots = self.vir_struct_field_count(return_vir_ty);
            let abi = vole_vir::func::ReturnAbi::classify(
                return_vir_ty,
                self.vir_type_table(),
                struct_slots,
            );
            let sig = self.build_signature_from_vir_types(
                &subst_param_virs,
                return_vir_ty,
                VirSelfParam::Typed(self_vir_ty),
                abi,
            );
            self.jit.ctx.func.signature = sig;

            // Build params from VirMethodDef.param_names using the interface's interner
            let method_def = self.analyzed.get_method_def(semantic_method_id);
            let param_cranelift_types = self.vir_ids_to_cranelift(&subst_param_virs);
            let params: Vec<_> = method_def
                .param_names
                .iter()
                .zip(subst_param_virs.iter())
                .zip(param_cranelift_types.iter())
                .map(|((name_str, &vir_ty), &cranelift_type)| {
                    let sym = iface_interner
                        .lookup(name_str)
                        .or_else(|| self.analyzed.interner().lookup(name_str))
                        .unwrap_or_else(|| {
                            panic!(
                                "param name '{}' not interned for default method {:?}",
                                name_str, semantic_method_id
                            )
                        });
                    (sym, vir_ty, cranelift_type)
                })
                .collect();

            let self_sym = iface_interner
                .lookup("self")
                .unwrap_or_else(|| self.self_symbol());

            let source_file_ptr = self.source_file_ptr();
            let table = self.vir_type_table();
            let self_cranelift_type = vir_type_to_cranelift(self_vir_ty, table, self.pointer_type);
            let self_binding = (self_sym, self_vir_ty, self_cranelift_type);

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
                    FunctionCompileConfig::method(params, self_binding, Some(return_vir_ty))
                        .with_self_vir_type(self_vir_ty);
                let subs = if vir_subs.is_empty() {
                    None
                } else {
                    Some(&vir_subs)
                };
                let vir_func = self
                    .analyzed
                    .get_method(semantic_method_id)
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

    /// Declare, compile, and register implement-block default methods for
    /// metadata-based dispatch via `try_resolve_implement_method_monomorph`.
    ///
    /// Walks all concrete element types (e.g. i64, string) and compiles
    /// each non-external Iterable default method (map, filter, count, etc.)
    /// with the generic VIR template body and concrete substitutions.
    /// Registers each function via `intern_name_id` so that
    /// `try_resolve_implement_method_monomorph` can find it.
    pub(super) fn compile_implement_method_monomorphs(&mut self) -> CodegenResult<()> {
        use rustc_hash::FxHashMap;

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
            match subs.into_keys().next() {
                Some(name_id) => name_id,
                None => return Ok(()),
            }
        };

        let iface_name_str: String = {
            let iface_name_id = self.analyzed.entity_type_name_id(iterable_tdef_id);
            self.analyzed
                .name_table()
                .last_segment_str(iface_name_id)
                .unwrap_or("Iterable".to_string())
        };

        let default_methods: Vec<(MethodId, NameId, String)> = {
            let query = self.analyzed;
            let mut results = Vec::new();
            for iface_method_id in query.type_methods(iterable_tdef_id) {
                let method_def = query.get_method_def(iface_method_id);
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

        let elem_types: Vec<TypeId> = self
            .vir_type_table()
            .all_concrete_iterator_elem_types_sema();

        for elem_type in elem_types {
            let self_type_id = match self.vir_type_table().lookup_array_sema(elem_type) {
                Some(tid) => tid,
                None => continue,
            };

            let vir_elem_type = self.vir_lookup(elem_type);
            let mut concrete_vir_subs: FxHashMap<NameId, VirTypeId> = FxHashMap::default();
            concrete_vir_subs.insert(t_name_id, vir_elem_type);
            let self_vir_ty = self.vir_lookup(self_type_id);

            // Skip if already registered (check first method's NameId key).
            if let Some((_, first_name_id, _)) = default_methods.first() {
                let key = ImplementMethodMonomorphKey::new(
                    iterable_tdef_id,
                    array_tdef_id,
                    *first_name_id,
                    vec![vir_elem_type],
                );
                if let Some(info) = self.analyzed.implement_method_monomorphs.get(&key) {
                    let fk = self.func_registry.intern_name_id(info.mangled_name);
                    if self.func_registry.func_id(fk).is_some() {
                        continue;
                    }
                }
            }

            for (semantic_method_id, method_name_id, method_name_str) in &default_methods {
                self.compile_single_implement_method_monomorph(
                    iterable_tdef_id,
                    array_tdef_id,
                    *semantic_method_id,
                    *method_name_id,
                    method_name_str,
                    elem_type,
                    vir_elem_type,
                    self_vir_ty,
                    &concrete_vir_subs,
                    &iface_name_str,
                )?;
            }
        }

        Ok(())
    }

    /// Compile a single implement method monomorph (e.g. `[i64].count()`).
    #[expect(clippy::too_many_arguments)]
    fn compile_single_implement_method_monomorph(
        &mut self,
        iterable_tdef_id: TypeDefId,
        array_tdef_id: TypeDefId,
        semantic_method_id: MethodId,
        method_name_id: NameId,
        method_name_str: &str,
        elem_type: TypeId,
        vir_elem_type: VirTypeId,
        self_vir_ty: VirTypeId,
        concrete_vir_subs: &rustc_hash::FxHashMap<NameId, VirTypeId>,
        iface_name_str: &str,
    ) -> CodegenResult<()> {
        let mangled_name = format!("__array_iterable_{}_{}", elem_type.index(), method_name_str);

        let method_def = self.analyzed.get_method_def(semantic_method_id);
        let Some((subst_param_virs, return_vir_ty)) = self.substitute_method_vir_types(
            &method_def.param_types,
            method_def.return_type,
            self_vir_ty,
            concrete_vir_subs,
        ) else {
            return Ok(());
        };

        {
            let table = self.vir_type_table();
            if table.lookup_vir_type_id(return_vir_ty).is_none()
                && return_vir_ty.raw() >= VirTypeId::FIRST_DYNAMIC
            {
                return Ok(());
            }
        }

        let struct_slots = self.vir_struct_field_count(return_vir_ty);
        let abi =
            vole_vir::func::ReturnAbi::classify(return_vir_ty, self.vir_type_table(), struct_slots);
        let sig = self.build_signature_from_vir_types(
            &subst_param_virs,
            return_vir_ty,
            VirSelfParam::Typed(self_vir_ty),
            abi,
        );

        // Import from cache or declare for compilation.
        let precompiled = self.jit.has_precompiled_symbol(&mangled_name);
        let func_id = if precompiled {
            self.jit.import_function(&mangled_name, &sig)
        } else {
            self.jit.declare_function(&mangled_name, &sig)
        };
        let func_key = self.func_registry.intern_raw(mangled_name);
        self.func_registry.set_func_id(func_key, func_id);
        // Register by NameId for metadata-based dispatch.
        self.register_implement_monomorph_name_id(
            iterable_tdef_id,
            array_tdef_id,
            method_name_id,
            vir_elem_type,
            func_id,
        );
        if precompiled {
            return Ok(());
        }

        let iface_info = self.find_interface_method_interner(iface_name_str, method_name_str);
        let Some((iface_interner, iface_module_id)) = iface_info else {
            return Ok(());
        };

        self.jit.ctx.func.signature = sig;

        let method_def = self.analyzed.get_method_def(semantic_method_id);
        let param_cranelift_types = self.vir_ids_to_cranelift(&subst_param_virs);
        let params: Vec<_> = method_def
            .param_names
            .iter()
            .zip(subst_param_virs.iter())
            .zip(param_cranelift_types.iter())
            .map(|((name_str, &vir_ty), &cranelift_type)| {
                let sym = iface_interner
                    .lookup(name_str)
                    .or_else(|| self.analyzed.interner().lookup(name_str))
                    .unwrap_or_else(|| {
                        panic!(
                            "param name '{}' not interned for iterable default method",
                            name_str
                        )
                    });
                (sym, vir_ty, cranelift_type)
            })
            .collect();

        let self_sym = iface_interner
            .lookup("self")
            .unwrap_or_else(|| self.self_symbol());
        let source_file_ptr = self.source_file_ptr();
        let table = self.vir_type_table();
        let self_cranelift_type = vir_type_to_cranelift(self_vir_ty, table, self.pointer_type);
        let self_binding = (self_sym, self_vir_ty, self_cranelift_type);

        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, &iface_interner, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );
            let config = FunctionCompileConfig::method(params, self_binding, Some(return_vir_ty))
                .with_self_vir_type(self_vir_ty);
            let vir_func = self
                .analyzed
                .get_method(semantic_method_id)
                .unwrap_or_else(|| panic!("VIR must be available for iterable default method"));
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir_func.body,
                iface_module_id,
                Some(concrete_vir_subs),
            )?;
        }
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Register a NameId-based function key for an implement method monomorph
    /// so that metadata-based dispatch can find it via `intern_name_id`.
    fn register_implement_monomorph_name_id(
        &mut self,
        interface_type_def_id: TypeDefId,
        implementing_type_def_id: TypeDefId,
        method_name: NameId,
        elem_vir_type: VirTypeId,
        func_id: cranelift_module::FuncId,
    ) {
        let key = ImplementMethodMonomorphKey::new(
            interface_type_def_id,
            implementing_type_def_id,
            method_name,
            vec![elem_vir_type],
        );
        if let Some(info) = self.analyzed.implement_method_monomorphs.get(&key) {
            let name_key = self.func_registry.intern_name_id(info.mangled_name);
            self.func_registry.set_func_id(name_key, func_id);
        }
    }
}
