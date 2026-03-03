//! Class/struct method declaration, registration, and compilation.
//!
//! This module handles the "what-to-compile" logic for type methods:
//! - Type method orchestration (`compile_type_methods`)
//! - Individual method compilation (`compile_method_by_id`)
//! - Static method compilation (`compile_static_methods`)
//! - Module type method compilation (`compile_module_type_methods` and helpers)
//! - Shared helpers (`register_method_func`)

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::impls::ModuleCompileInfo;
use super::{Compiler, DeclareMode, SelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::vir_conversions::vir_type_to_cranelift;
use crate::types::{CodegenCtx, TypeMetadata};
use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use rustc_hash::FxHashSet;
use vole_identity::{Interner, MethodId, ModuleId, Symbol, TypeDefId, VirTypeId};

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

    /// Compile methods for a type (class or struct) by TypeDefId.
    ///
    /// Used when iterating VirEntityMetadata type definitions instead of
    /// walking AST declarations.  Skips generic types (compiled via monomorphized
    /// instances).
    pub(super) fn compile_type_methods_by_id(
        &mut self,
        type_def_id: TypeDefId,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_def = self.analyzed.get_type(type_def_id);
        // Skip generic types - they're compiled via monomorphized instances
        if type_def.has_type_params() {
            return Ok(());
        }
        // Skip types with no methods
        if type_def.methods.is_empty() && type_def.static_methods.is_empty() {
            return Ok(());
        }
        self.compile_type_methods_inner(type_def_id, module_id)
    }

    /// Inner implementation for compiling methods of a class or struct by TypeDefId.
    ///
    /// Iterates method IDs from VirTypeDef.methods and compiles class-body
    /// and inherited default methods using VIR. Implement-block methods are
    /// excluded -- they are compiled separately by the implement block path.
    fn compile_type_methods_inner(
        &mut self,
        type_def_id: TypeDefId,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_def = self.analyzed.get_type(type_def_id);
        let type_name_id = type_def.name_id;
        let method_ids = type_def.methods.clone();
        let static_method_ids = type_def.static_methods.clone();
        let type_kind = type_def.type_kind();

        let type_display = self.analyzed.display_name(type_name_id);

        let metadata = self
            .state
            .type_metadata
            .get(&type_def_id)
            .cloned()
            .ok_or_else(|| {
                CodegenError::not_found("type_metadata", format!("{} {}", type_kind, type_display))
            })?;

        // Build sets of method IDs owned by implement blocks for this type.
        // When a type has implement blocks, default methods from ALL interfaces
        // are compiled by compile_iface_default_methods (which iterates
        // implemented_interfaces, not just the implement block's interface).
        let mut impl_instance_ids: FxHashSet<MethodId> = FxHashSet::default();
        let mut impl_static_ids: FxHashSet<MethodId> = FxHashSet::default();
        for entry in self.analyzed.implement_blocks_for_type(type_def_id) {
            impl_instance_ids.extend(entry.instance_methods.iter().copied());
            impl_static_ids.extend(entry.static_methods.iter().copied());
        }
        let has_impl_blocks = !impl_instance_ids.is_empty() || !impl_static_ids.is_empty();

        // Compile instance methods from VIR method IDs, skipping:
        // - implement-block direct methods (compiled by compile_implement_block)
        // - inherited default methods when implement blocks exist
        //   (compiled by compile_iface_default_methods for ALL interfaces)
        // - methods without VIR bodies
        for &method_id in &method_ids {
            if impl_instance_ids.contains(&method_id) {
                continue;
            }
            if has_impl_blocks {
                let method_def = self.analyzed.get_method(method_id);
                if method_def.has_default {
                    // When implement blocks exist, compile_iface_default_methods
                    // handles ALL default methods (from all interfaces, not just
                    // the implement block's interface).
                    continue;
                }
            }
            if self.analyzed.get_vir_method(method_id).is_none() {
                continue;
            }
            self.compile_method_by_id_inner(method_id, &type_display, &metadata)?;
        }

        // Compile static methods from VIR metadata, excluding implement-block statics.
        if !static_method_ids.is_empty() {
            let non_impl_statics: Vec<MethodId> = static_method_ids
                .iter()
                .copied()
                .filter(|id| !impl_static_ids.contains(id))
                .collect();
            if !non_impl_statics.is_empty() {
                self.compile_static_methods_by_id_inner(
                    &non_impl_statics,
                    &type_display,
                    module_id,
                )?;
            }
        }

        Ok(())
    }

    /// Compile a single method by MethodId (VIR-based).
    ///
    /// Uses VIR function params for Symbol bindings, ensuring correctness for
    /// both direct methods and inherited default methods (including those from
    /// module interfaces where param Symbols may differ from the main interner).
    fn compile_method_by_id_inner(
        &mut self,
        method_id: MethodId,
        type_name_str: &str,
        metadata: &TypeMetadata,
    ) -> CodegenResult<()> {
        let method_def = self.analyzed.get_method(method_id);
        let method_name_id = method_def.name_id;
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

        // Get param and return types from VIR method definition
        let method_def = self.analyzed.get_method(method_id);
        let param_vir_types = &method_def.param_types;
        let return_vir_type = method_def.return_type;

        // Get VIR function (must be available at this point)
        let vir_func = self
            .analyzed
            .get_vir_method(method_id)
            .expect("VIR must be available for type method");

        // Build params using VIR function param Symbols (not interner lookup).
        // This ensures correctness for inherited default methods from module
        // interfaces, where param Symbols may come from a different interner.
        //
        // VIR function params may include an explicit `self` parameter (from
        // `func foo(self: T, ...)`) which is NOT included in the method
        // signature's param types (since codegen adds `self` separately via
        // SelfParam::Pointer). If VIR has more params than the signature,
        // skip the leading `self` entry to keep the zip aligned.
        let vir_params_offset = vir_func.params.len().saturating_sub(param_vir_types.len());
        let params: Vec<(Symbol, VirTypeId, types::Type)> = {
            let table = self.vir_type_table();
            vir_func
                .params
                .iter()
                .skip(vir_params_offset)
                .zip(param_vir_types.iter())
                .map(|(&(sym, _, _), &vir_ty)| {
                    let cranelift_type = vir_type_to_cranelift(vir_ty, table, self.pointer_type);
                    (sym, vir_ty, cranelift_type)
                })
                .collect()
        };

        // Get self Symbol from the VIR function's identity context.
        // For module interface default methods, "self" may be a different Symbol
        // than the main interner's. We look it up in the VIR body's interner context
        // by using the method's defining type module.
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();
        let method_return_vir_ty = Some(return_vir_type);

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
            let self_binding = (self_sym, self_vir_ty, self.pointer_type);
            let config = FunctionCompileConfig::method(params, self_binding, method_return_vir_ty);
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

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile static methods by MethodId from VIR metadata.
    fn compile_static_methods_by_id_inner(
        &mut self,
        static_method_ids: &[MethodId],
        type_display: &str,
        _module_id: ModuleId,
    ) -> CodegenResult<()> {
        for &method_id in static_method_ids {
            let method_def = self.analyzed.get_method(method_id);

            // Only compile methods with bodies (skip external-only)
            if method_def.external_binding.is_some() {
                continue;
            }

            let method_name_str = self
                .analyzed
                .last_segment(method_def.name_id)
                .unwrap_or_default();

            // Function key from EntityRegistry full_name_id
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!("{}::{}", type_display, method_name_str,),
                )
            })?;

            // Create signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from VIR method definition
            let method_def = self.analyzed.get_method(method_id);
            let param_vir_types = &method_def.param_types;
            let return_vir_type = method_def.return_type;

            // Get VIR function (must be available)
            let vir_func = self
                .analyzed
                .get_vir_method(method_id)
                .expect("VIR must be available for static method");

            // Build params using VIR function param Symbols
            let params: Vec<_> = {
                let table = self.vir_type_table();
                vir_func
                    .params
                    .iter()
                    .zip(param_vir_types.iter())
                    .map(|(&(sym, _, _), &vir_ty)| {
                        let cranelift_type =
                            vir_type_to_cranelift(vir_ty, table, self.pointer_type);
                        (sym, vir_ty, cranelift_type)
                    })
                    .collect()
            };

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

                let config = FunctionCompileConfig::top_level(params, Some(return_vir_type));
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

            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                let method_name_str = self
                    .analyzed
                    .last_segment(method_def.name_id)
                    .unwrap_or_default();
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

            // Get param and return types from VIR method definition
            let method_def = self.analyzed.get_method(method_id);
            let param_vir_types = &method_def.param_types;
            let return_vir_type = method_def.return_type;

            // Get VIR function (must be available)
            let vir_func = self
                .analyzed
                .get_vir_method(method_id)
                .expect("VIR must be available for module method");

            let self_sym = module_info
                .interner
                .lookup("self")
                .ok_or_else(|| CodegenError::internal("method compilation: 'self' not interned"))?;
            // Build params using VIR function param Symbols.
            // Skip leading `self` param if VIR has more params than the signature
            // (explicit `self: T` in source is excluded from the method signature).
            let vir_params_offset = vir_func.params.len().saturating_sub(param_vir_types.len());
            let params: Vec<_> = {
                let table = self.vir_type_table();
                vir_func
                    .params
                    .iter()
                    .skip(vir_params_offset)
                    .zip(param_vir_types.iter())
                    .map(|(&(sym, _, _), &vir_ty)| {
                        let cranelift_type =
                            vir_type_to_cranelift(vir_ty, table, self.pointer_type);
                        (sym, vir_ty, cranelift_type)
                    })
                    .collect()
            };
            let self_vir_ty = self.vir_lookup(metadata.vole_type);
            let self_binding = (self_sym, self_vir_ty, self.pointer_type);

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

                let config =
                    FunctionCompileConfig::method(params, self_binding, Some(return_vir_type));
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
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
            let param_vir_types = &method_def.param_types;
            let return_vir_type = method_def.return_type;

            // Get VIR function (must be available)
            let vir_func = self
                .analyzed
                .get_vir_method(method_id)
                .expect("VIR must be available for module static method");

            // Build params using VIR function param Symbols
            let params: Vec<_> = {
                let table = self.vir_type_table();
                vir_func
                    .params
                    .iter()
                    .zip(param_vir_types.iter())
                    .map(|(&(sym, _, _), &vir_ty)| {
                        let cranelift_type =
                            vir_type_to_cranelift(vir_ty, table, self.pointer_type);
                        (sym, vir_ty, cranelift_type)
                    })
                    .collect()
            };

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

                let config = FunctionCompileConfig::top_level(params, Some(return_vir_type));
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
                    Some(module_info.module_id),
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile methods for a module type by TypeDefId using the VirProgram interner.
    ///
    /// Used when iterating VirEntityMetadata type definitions by module,
    /// where we already have the TypeDefId without needing AST name resolution.
    pub(super) fn compile_module_type_methods_by_id(
        &mut self,
        type_def_id: TypeDefId,
        module_interner: &Interner,
        module_path: &str,
    ) -> CodegenResult<()> {
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);
        let type_name_str = self
            .analyzed
            .name_table()
            .last_segment_str(type_name_id)
            .unwrap_or_else(|| self.analyzed.display_name(type_name_id));
        self.compile_module_type_methods(&type_name_str, module_interner, module_path)
    }
}
