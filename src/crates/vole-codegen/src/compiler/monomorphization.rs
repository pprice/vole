use rustc_hash::{FxHashMap, FxHashSet};

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext};

use super::Compiler;
use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};

use crate::errors::{CodegenError, CodegenResult};
use crate::types::CodegenCtx;
use vole_identity::{ModuleId, MonomorphInstanceTrait, NameId, TypeId, VirTypeId};
use vole_vir::monomorph::instance::{
    VirClassMethodMonomorphInfo, VirMonomorphInfo, VirStaticMethodMonomorphInfo,
};
use vole_vir::types::VirType;

use crate::types::MonomorphIndexEntry;

/// Data for an expanded class method monomorph (used during template expansion).
struct ExpandedMethodData {
    concrete_key: vole_identity::ClassMethodMonomorphKey,
    mangled_name_str: String,
    template_mangled_name: NameId,
    func_type: vole_identity::FunctionType,
    /// VirTypeId-native substitutions for Cg context.
    vir_substitutions: FxHashMap<NameId, VirTypeId>,
    class_name: NameId,
    self_type: TypeId,
    external_info: Option<crate::analyzed::ExternalMethodInfoRef>,
    /// FunctionKey assigned during JIT declaration (set in step 4)
    func_key: Option<crate::FunctionKey>,
}

impl Compiler<'_> {
    /// Declare a single monomorphized instance using the common trait interface.
    /// `has_self_param` indicates if a self pointer should be prepended to parameters.
    pub(super) fn declare_monomorph_instance<T: MonomorphInstanceTrait>(
        &mut self,
        instance: &T,
        has_self_param: bool,
    ) {
        use super::signatures::SelfParam;

        let mangled_name = self.analyzed.display_name(instance.mangled_name());
        let func_type = instance.func_type();

        // Get TypeId versions of params and return type
        let param_type_ids: Vec<TypeId> = func_type.params_id.to_vec();
        let return_type_id = func_type.return_type_id;

        // Build signature using the shared builder which handles struct returns,
        // fallible returns, and other special calling conventions.
        let self_param = if has_self_param {
            SelfParam::Pointer
        } else {
            SelfParam::None
        };
        let sig =
            self.build_signature_from_type_ids(&param_type_ids, Some(return_type_id), self_param);
        let func_id = self.jit.declare_function(&mangled_name, &sig);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name());
        self.func_registry.set_func_id(func_key, func_id);

        // Record return type for call expressions
        self.func_registry.set_return_type(func_key, return_type_id);
    }

    /// Declare all monomorphized function instances
    pub(super) fn declare_monomorphized_instances(&mut self) -> CodegenResult<()> {
        // Collect from VirProgram.free_monomorphs to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .vir_program()
            .free_monomorphs
            .values()
            .cloned()
            .collect();

        for instance in &instances {
            // Skip external functions - they don't need JIT compilation
            // They're called directly via native_registry
            if self.is_external_func(instance.original_name) {
                continue;
            }

            self.declare_monomorph_instance(instance, false);
        }

        Ok(())
    }

    /// Compile all monomorphized function instances.
    ///
    /// When `program` is `Some`, main-program generic function ASTs are checked first.
    /// When `program` is `None` (module-only phase), only module programs are searched
    /// and instances whose ASTs aren't found are silently skipped — they will be
    /// compiled later by the program phase or the demand-driven fixpoint loop.
    pub(super) fn compile_monomorphized_instances(
        &mut self,
        is_program_phase: bool,
    ) -> CodegenResult<()> {
        // Collect instances from VirProgram.free_monomorphs to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .vir_program()
            .free_monomorphs
            .values()
            .cloned()
            .collect();

        let program_module = self.program_module();

        for instance in &instances {
            // Skip external functions - they don't have VIR bodies
            // Generic externals are called directly with type erasure at call sites
            if self.is_external_func(instance.original_name) {
                continue;
            }

            // Check if this function belongs to the program module or a loaded module
            let func_module = self.analyzed.name_table().module_of(instance.original_name);
            if func_module == program_module {
                // During module phase, skip program-level monomorphs — their types
                // (classes, structs) aren't registered in type_metadata yet.  They
                // will be compiled later in compile_program_body's program phase.
                if !is_program_phase {
                    continue;
                }
                self.compile_monomorphized_function(instance)?;
            } else {
                // Module function — needs module interner for compile_env
                let found = self.compile_monomorphized_module_function(instance)?;
                if !found && is_program_phase {
                    let func_name = self.analyzed.display_name(instance.original_name);
                    return Err(CodegenError::internal_with_context(
                        "VIR monomorphized function not found",
                        func_name,
                    ));
                }
            }
        }

        Ok(())
    }

    /// Compile a monomorphized instance of a module function via its VIR body.
    fn compile_monomorphized_module_function(
        &mut self,
        instance: &VirMonomorphInfo,
    ) -> CodegenResult<bool> {
        let module_id = self.analyzed.name_table().module_of(instance.original_name);
        let module_path = self
            .analyzed
            .name_table()
            .module_path(module_id)
            .to_string();

        // Need the module interner for compile_env
        if !self.analyzed.vir_program().has_module(&module_path) {
            return Ok(false);
        }

        let mangled_name = self.analyzed.display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized function", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(true);
        }

        // Get the VIR function (must be available — module monomorphs are always lowered)
        let vir_func = self
            .analyzed
            .get_vir_monomorph(instance.mangled_name)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "VIR module monomorphized function",
                    format!("{mangled_name} ({:?})", instance.mangled_name),
                )
            })?;

        // Clear main-program module bindings while compiling module interner code.
        // The IIFE ensures bindings are restored even when `?` returns early.
        let saved_bindings = std::mem::take(&mut self.global_module_bindings);
        let compile_result = (|| -> CodegenResult<bool> {
            let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
            let return_type_id = instance.func_type.return_type_id;
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = vir_func
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((vp, &type_id), &cranelift_type)| {
                    (vp.0, self.vir_lookup(type_id), cranelift_type)
                })
                .collect();

            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(return_type_id),
                super::signatures::SelfParam::None,
            );
            self.jit.ctx.func.signature = sig;

            let source_file_ptr = self.source_file_ptr();
            let return_vir_ty = self.vir_lookup(return_type_id);
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let module_interner = self
                    .analyzed
                    .vir_program()
                    .module_interner_rc(&module_path)
                    .expect("module interner not found for module path");
                let env = compile_env!(self, &module_interner, source_file_ptr);
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(params, Some(return_vir_ty));
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
                    Some(module_id),
                    Some(&instance.vir_substitutions),
                )?;
            }

            self.finalize_function(func_id)?;
            Ok(true)
        })();
        self.global_module_bindings = saved_bindings;
        compile_result
    }

    /// Compile a single monomorphized function instance.
    ///
    /// Uses VIR when available; falls back to AST when sema data is
    /// incomplete (e.g. structural type parameter monomorphs).
    fn compile_monomorphized_function(&mut self, instance: &VirMonomorphInfo) -> CodegenResult<()> {
        let mangled_name = self.analyzed.display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized function", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(());
        }

        // Get VIR function (provides param names and body)
        let vir_func = self
            .analyzed
            .get_vir_monomorph(instance.mangled_name)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "VIR monomorphized function",
                    format!("{mangled_name} ({:?})", instance.mangled_name),
                )
            })?;

        // Get parameter types and build config using VIR param names
        let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
        let return_type_id = instance.func_type.return_type_id;
        let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = vir_func
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_cranelift_types.iter())
            .map(|((vp, &type_id), &cranelift_type)| {
                (vp.0, self.vir_lookup(type_id), cranelift_type)
            })
            .collect();

        // Create function signature from concrete types using shared builder
        let sig = self.build_signature_from_type_ids(
            &param_type_ids,
            Some(return_type_id),
            super::signatures::SelfParam::None,
        );
        self.jit.ctx.func.signature = sig;

        let source_file_ptr = self.source_file_ptr();
        let return_vir_ty = self.vir_lookup(return_type_id);
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let config = FunctionCompileConfig::top_level(params, Some(return_vir_ty));
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir_func.body,
                None,
                Some(&instance.vir_substitutions),
            )?;
        }

        self.finalize_function(func_id)?;

        Ok(())
    }

    /// VIR-native: check if a class method monomorph is abstract (contains Param substitutions).
    fn is_abstract_vir_class_method_monomorph(
        &self,
        instance: &VirClassMethodMonomorphInfo,
    ) -> bool {
        let type_table = &self.analyzed.vir_program().type_table;
        instance
            .vir_substitutions
            .values()
            .any(|&vir_type_id| matches!(type_table.get(vir_type_id), VirType::Param { .. }))
    }

    /// VIR-native: check if a static method monomorph is abstract (contains Param substitutions).
    fn is_abstract_vir_static_method_monomorph(
        &self,
        instance: &VirStaticMethodMonomorphInfo,
    ) -> bool {
        let type_table = &self.analyzed.vir_program().type_table;
        instance
            .vir_substitutions
            .values()
            .any(|&vir_type_id| matches!(type_table.get(vir_type_id), VirType::Param { .. }))
    }

    /// Returns true when the type references a nominal definition from the main
    /// program (or a tests virtual module), not from imported module programs.
    fn type_depends_on_program_definitions(&self, type_id: TypeId) -> bool {
        let mut visited = FxHashSet::default();
        self.type_depends_on_program_definitions_inner(self.vir_lookup(type_id), &mut visited)
    }

    /// VirTypeId variant of `type_depends_on_program_definitions`.
    fn type_depends_on_program_definitions_v(&self, vir_ty: VirTypeId) -> bool {
        let mut visited = FxHashSet::default();
        self.type_depends_on_program_definitions_inner(vir_ty, &mut visited)
    }

    fn type_depends_on_program_definitions_inner(
        &self,
        vir_ty: VirTypeId,
        visited: &mut FxHashSet<VirTypeId>,
    ) -> bool {
        if !visited.insert(vir_ty) {
            return false; // cycle — treat as not program-owned
        }

        let nominal_is_program_owned = |type_def_id| {
            let name_id = self.analyzed.entity_type_name_id(type_def_id);
            let module_id = self.analyzed.name_table().module_of(name_id);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            !self.analyzed.vir_program().has_module(&module_path)
        };

        if let Some((type_def_id, type_args)) = self.vir_query_unwrap_class_v(vir_ty) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((type_def_id, type_args)) = self.vir_query_unwrap_struct_v(vir_ty) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((type_def_id, type_args)) = self.vir_query_unwrap_interface_v(vir_ty) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some(elem) = self.vir_query_unwrap_array_v(vir_ty) {
            return self.type_depends_on_program_definitions_inner(elem, visited);
        }
        if let Some((elem, _)) = self.vir_query_unwrap_fixed_array_v(vir_ty) {
            return self.type_depends_on_program_definitions_inner(elem, visited);
        }
        if let Some(elements) = self.vir_query_unwrap_tuple_v(vir_ty) {
            return elements
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some(variants) = self.vir_query_unwrap_union_v(vir_ty) {
            return variants
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((ok_type, error_types)) = self.vir_query_unwrap_fallible_v(vir_ty) {
            return self.type_depends_on_program_definitions_inner(ok_type, visited)
                || error_types
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((params, ret)) = self.vir_query_unwrap_function_v(vir_ty) {
            return params
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited))
                || self.type_depends_on_program_definitions_inner(ret, visited);
        }

        false
    }

    /// Returns true when any substitution type depends on main-program definitions.
    /// Used during the module-only phase to skip monomorphs that reference program
    /// types — their implement-block methods aren't available yet.
    fn substitutions_depend_on_program_definitions(
        &self,
        substitutions: &FxHashMap<NameId, TypeId>,
    ) -> bool {
        substitutions
            .values()
            .copied()
            .any(|ty| self.type_depends_on_program_definitions(ty))
    }

    /// Declare all monomorphized class method instances
    pub(super) fn declare_class_method_monomorphized_instances(&mut self) -> CodegenResult<()> {
        // Collect from VirProgram.class_method_monomorphs to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .vir_program()
            .class_method_monomorphs
            .values()
            .cloned()
            .collect();

        tracing::debug!(
            instance_count = instances.len(),
            "declaring class method monomorphized instances"
        );

        for instance in &instances {
            // External methods are runtime functions - no declaration needed
            if instance.external_info.is_some() {
                continue;
            }

            // Skip abstract monomorph templates (e.g., T -> Param(T)).
            if self.is_abstract_vir_class_method_monomorph(instance) {
                continue;
            }

            // Class methods have self parameter
            self.declare_monomorph_instance(instance, true);
        }

        Ok(())
    }

    /// Compile all monomorphized class method instances.
    ///
    /// When `program` is `Some`, errors on missing VIR bodies.
    /// When `None` (module-only phase), instances that depend on program-defined
    /// types are silently skipped (compiled later during the program phase).
    pub(super) fn compile_class_method_monomorphized_instances(
        &mut self,
        is_program_phase: bool,
    ) -> CodegenResult<()> {
        // Collect from VirProgram.class_method_monomorphs to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .vir_program()
            .class_method_monomorphs
            .values()
            .cloned()
            .collect();

        let program_module = self.program_module();

        tracing::debug!(
            instance_count = instances.len(),
            "compiling class method monomorphized instances"
        );

        for instance in &instances {
            // External methods are runtime functions - no compilation needed
            if instance.external_info.is_some() {
                tracing::debug!(
                    class_name = ?instance.class_name,
                    method_name = ?instance.method_name,
                    "skipping external method - calls runtime function directly"
                );
                continue;
            }

            // Skip abstract monomorph templates (e.g., T -> Param(T)).
            if self.is_abstract_vir_class_method_monomorph(instance) {
                continue;
            }

            // During the module-only phase, skip instances whose substitutions
            // reference program-defined types. Their implement-block methods
            // (e.g. Color.hash()) aren't declared yet and compilation would fail.
            // These are compiled later during the program phase.
            if !is_program_phase
                && self.substitutions_depend_on_program_definitions(&instance.substitutions)
            {
                continue;
            }

            // Determine module_path for interner selection
            let class_module = self.analyzed.name_table().module_of(instance.class_name);
            let module_path = if class_module == program_module {
                None
            } else {
                Some(
                    self.analyzed
                        .name_table()
                        .module_path(class_module)
                        .to_string(),
                )
            };

            self.compile_monomorphized_class_method(instance, module_path.as_deref())?;
        }

        Ok(())
    }

    /// Compile a single monomorphized class method instance.
    /// When `module_path` is Some, the method AST comes from a loaded module
    /// and its symbols must be resolved with that module's interner.
    fn compile_monomorphized_class_method(
        &mut self,
        instance: &VirClassMethodMonomorphInfo,
        module_path: Option<&str>,
    ) -> CodegenResult<()> {
        let mangled_name = self.analyzed.display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized class method", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(());
        }

        // Get VIR function (provides param names and body)
        let vir_func = self
            .analyzed
            .get_vir_monomorph(instance.mangled_name)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "VIR class method monomorph",
                    format!("{mangled_name} ({:?})", instance.mangled_name),
                )
            })?;

        // Only use module interner if the module is actually loaded
        let effective_module_path =
            module_path.filter(|p| self.analyzed.vir_program().has_module(p));

        // Save/restore module bindings when compiling module code via IIFE.
        // Ensures bindings are restored even when `?` returns early.
        // A panic would skip the restore, but panics are fatal anyway.
        let saved_bindings = if effective_module_path.is_some() {
            Some(std::mem::take(&mut self.global_module_bindings))
        } else {
            None
        };
        let compile_result = (|| -> CodegenResult<()> {
            // Get param and return types, build config using VIR param names
            let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
            let return_type_id = instance.func_type.return_type_id;
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = vir_func
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((vp, &type_id), &cranelift_type)| {
                    (vp.0, self.vir_lookup(type_id), cranelift_type)
                })
                .collect();

            // Create method signature (self + params) with concrete types using shared builder
            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(return_type_id),
                super::signatures::SelfParam::Pointer,
            );
            self.jit.ctx.func.signature = sig;

            // Use pre-computed self type from sema
            let self_type_id = instance.self_type;
            let self_sym = self.self_symbol();
            let self_vir_ty = self.vir_lookup(self_type_id);
            let self_binding = (self_sym, self_vir_ty, self.pointer_type);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let return_vir_ty = self.vir_lookup(return_type_id);
            let mut builder_ctx = FunctionBuilderContext::new();
            // Determine module_id for Cg context (needed for expression data lookup)
            let cg_module_id = effective_module_path
                .map(|_| self.analyzed.name_table().module_of(instance.class_name));
            // Hoist module interner Rc so it outlives the compile_env borrow.
            let module_interner_rc = effective_module_path
                .and_then(|p| self.analyzed.vir_program().module_interner_rc(p));
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = if let Some(ref interner) = module_interner_rc {
                    compile_env!(self, interner, source_file_ptr)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config =
                    FunctionCompileConfig::method(params, self_binding, Some(return_vir_ty));
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
                    cg_module_id,
                    Some(&instance.vir_substitutions),
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
            Ok(())
        })();
        if let Some(bindings) = saved_bindings {
            self.global_module_bindings = bindings;
        }
        compile_result
    }

    /// Declare all monomorphized static method instances
    pub(super) fn declare_static_method_monomorphized_instances(&mut self) -> CodegenResult<()> {
        // Collect from VirProgram.static_method_monomorphs to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .vir_program()
            .static_method_monomorphs
            .values()
            .cloned()
            .collect();

        tracing::debug!(
            instance_count = instances.len(),
            "declaring static method monomorphized instances"
        );

        for instance in &instances {
            if self.is_abstract_vir_static_method_monomorph(instance) {
                continue;
            }
            // Static methods don't have self parameter
            self.declare_monomorph_instance(instance, false);
        }

        Ok(())
    }

    /// Compile all monomorphized static method instances.
    ///
    /// When `program` is `Some`, main-program class ASTs are checked first.
    /// When `None` (module-only phase), instances that depend on program-defined
    /// types are silently skipped (compiled later during the program phase).
    pub(super) fn compile_static_method_monomorphized_instances(
        &mut self,
        is_program_phase: bool,
    ) -> CodegenResult<()> {
        // Collect from VirProgram.static_method_monomorphs to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .vir_program()
            .static_method_monomorphs
            .values()
            .cloned()
            .collect();

        let program_module = self.program_module();

        tracing::debug!(
            instance_count = instances.len(),
            "compiling static method monomorphized instances"
        );

        for instance in &instances {
            if self.is_abstract_vir_static_method_monomorph(instance) {
                continue;
            }

            // During the module-only phase, skip instances whose substitutions
            // reference program-defined types. Their implement-block methods
            // aren't declared yet and compilation would fail.
            if !is_program_phase
                && self.substitutions_depend_on_program_definitions(&instance.substitutions)
            {
                continue;
            }

            // Determine module_path for interner selection
            let class_module = self.analyzed.name_table().module_of(instance.class_name);
            let module_path = if class_module == program_module {
                None
            } else {
                Some(
                    self.analyzed
                        .name_table()
                        .module_path(class_module)
                        .to_string(),
                )
            };

            self.compile_monomorphized_static_method(instance, module_path.as_deref())?;
        }

        Ok(())
    }

    /// Compile a single monomorphized static method instance.
    /// When `module_path` is Some, the method comes from a loaded module
    /// and its symbols must be resolved with that module's interner.
    fn compile_monomorphized_static_method(
        &mut self,
        instance: &VirStaticMethodMonomorphInfo,
        module_path: Option<&str>,
    ) -> CodegenResult<()> {
        let mangled_name = self.analyzed.display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized static method", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(());
        }

        // Get VIR function (provides param names and body)
        let vir_func = self
            .analyzed
            .get_vir_monomorph(instance.mangled_name)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "VIR static method monomorph",
                    format!("{mangled_name} ({:?})", instance.mangled_name),
                )
            })?;

        // Only use module interner if the module is actually loaded
        let effective_module_path =
            module_path.filter(|p| self.analyzed.vir_program().has_module(p));

        // Save/restore module bindings when compiling module code via IIFE.
        // Ensures bindings are restored even when `?` returns early.
        // A panic would skip the restore, but panics are fatal anyway.
        let saved_bindings = if effective_module_path.is_some() {
            Some(std::mem::take(&mut self.global_module_bindings))
        } else {
            None
        };
        let compile_result = (|| -> CodegenResult<()> {
            // Get param and return types, build config using VIR param names
            let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
            let return_type_id = instance.func_type.return_type_id;
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = vir_func
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((vp, &type_id), &cranelift_type)| {
                    (vp.0, self.vir_lookup(type_id), cranelift_type)
                })
                .collect();

            // Create signature (no self parameter) with concrete types using shared builder
            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(return_type_id),
                super::signatures::SelfParam::None,
            );
            self.jit.ctx.func.signature = sig;

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let return_vir_ty = self.vir_lookup(return_type_id);
            let mut builder_ctx = FunctionBuilderContext::new();
            // Determine module_id for Cg context (needed for expression data lookup)
            let cg_module_id = effective_module_path
                .map(|_| self.analyzed.name_table().module_of(instance.class_name));
            // Hoist module interner Rc so it outlives the compile_env borrow.
            let module_interner_rc = effective_module_path
                .and_then(|p| self.analyzed.vir_program().module_interner_rc(p));
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = if let Some(ref interner) = module_interner_rc {
                    compile_env!(self, interner, source_file_ptr)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(params, Some(return_vir_ty));
                compile_function_inner_with_vir(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    &vir_func.body,
                    cg_module_id,
                    Some(&instance.vir_substitutions),
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
            Ok(())
        })();
        if let Some(bindings) = saved_bindings {
            self.global_module_bindings = bindings;
        }
        compile_result
    }

    // ===================================================================
    // Abstract class method template expansion
    // ===================================================================

    /// Expand abstract class method monomorph templates into concrete instances.
    ///
    /// When a module-internal generic function/static method (e.g. `Task.stream<T>`)
    /// calls instance methods on a generic class (e.g. `Channel<T>.close()`),
    /// sema only creates abstract templates with TypeParam substitutions.
    /// This method finds those abstract templates, matches them with concrete
    /// substitutions from other monomorph caches, creates concrete instances,
    /// declares them in JIT, compiles their bodies, and registers them in
    /// `expanded_class_method_monomorphs` for lookup by `Cg`.
    pub(super) fn expand_abstract_class_method_monomorphs(&mut self) -> CodegenResult<()> {
        use vole_identity::{ClassMethodMonomorphKey, FunctionType};

        // Early-exit if monomorph caches haven't grown since last expansion
        let current_cache_size = self.analyzed.vir_program().class_method_monomorphs.len()
            + self.analyzed.vir_program().static_method_monomorphs.len();
        if current_cache_size == self.last_expansion_cache_size {
            tracing::debug!("expand_abstract_class_method_monomorphs: caches unchanged, skipping");
            return Ok(());
        }
        self.last_expansion_cache_size = current_cache_size;

        // Step 1: Collect abstract class method templates (those with TypeParam in substitutions)
        tracing::debug!(
            current_cache_size,
            "expand_abstract_class_method_monomorphs: checking cache"
        );

        let type_table = &self.analyzed.vir_program().type_table;
        let abstract_templates: Vec<(ClassMethodMonomorphKey, VirClassMethodMonomorphInfo)> = self
            .analyzed
            .vir_program()
            .class_method_monomorphs
            .iter()
            .filter(|(_, inst)| {
                inst.vir_substitutions.values().any(|&vir_type_id| {
                    matches!(type_table.get(vir_type_id), VirType::Param { .. })
                })
            })
            .map(|(key, inst)| (key.clone(), inst.clone()))
            .collect();

        tracing::debug!(
            abstract_count = abstract_templates.len(),
            "expand_abstract_class_method_monomorphs: found abstract templates"
        );

        if abstract_templates.is_empty() {
            return Ok(());
        }

        // Step 2: Collect concrete type argument vectors per class.
        //
        // IMPORTANT: Type parameter NameIds (e.g. "T") are shared across all classes
        // that use the same parameter name (they're interned in the builtin module).
        // A substitution from Array.filled<Entry> ({T -> Entry}) has the SAME key NameId
        // as one from Channel<i64> ({T -> i64}). To prevent false cross-class expansion,
        // we collect concrete type argument vectors PER CLASS from the monomorph caches,
        // then in step 3 only expand a template with type args known for THAT class.
        //
        // Sources of concrete type arguments per class:
        // - Static method monomorphs: (class_name, class_type_keys)
        // - Class method monomorphs: (class_name, type_keys)
        let mut class_concrete_type_args: FxHashMap<NameId, Vec<Vec<VirTypeId>>> =
            FxHashMap::default();

        // Collect from concrete static method monomorphs
        for (key, inst) in &self.analyzed.vir_program().static_method_monomorphs {
            // Skip abstract entries (TypeParam in substitutions)
            if inst
                .vir_substitutions
                .values()
                .any(|&vir_type_id| matches!(type_table.get(vir_type_id), VirType::Param { .. }))
            {
                continue;
            }
            // Skip entries with no class type keys (non-generic class)
            if key.class_type_keys.is_empty() {
                continue;
            }
            // Skip entries where type keys still contain TypeParams
            if key
                .class_type_keys
                .iter()
                .any(|&tk| self.vir_query_contains_type_param_v(tk))
            {
                continue;
            }
            // Skip entries where type args reference program-defined types.
            //
            // Sema's `derive_concrete_static_method_monomorphs` cross-pollinates
            // substitutions across ALL classes sharing the same TypeParam name (e.g. "T").
            // This creates false entries like `Set.new<Entry|Empty>()` from
            // `Array.filled<Entry|Empty>()` — different classes sharing NameId("T").
            // These false entries are harmless as static methods (they compile fine)
            // but cause errors when we expand them into class method templates
            // (e.g. `Set<Entry|Empty>.equals()` fails because Entry|Empty doesn't
            // satisfy Set's `T: Equatable` constraint).
            //
            // Filtering out program-defined types is safe because:
            // - Module-internal generic code doesn't know about program types
            // - Legitimate program-type monomorphs are created directly by sema
            //   at the call site and exist as concrete (non-abstract) entries
            if key
                .class_type_keys
                .iter()
                .any(|&tk| self.type_depends_on_program_definitions_v(tk))
            {
                continue;
            }
            class_concrete_type_args
                .entry(key.class_name)
                .or_default()
                .push(key.class_type_keys.clone());
        }

        // Collect from concrete class method monomorphs
        for (key, inst) in &self.analyzed.vir_program().class_method_monomorphs {
            // Skip abstract entries
            if inst
                .vir_substitutions
                .values()
                .any(|&vir_type_id| matches!(type_table.get(vir_type_id), VirType::Param { .. }))
            {
                continue;
            }
            if key.type_keys.is_empty() {
                continue;
            }
            if key
                .type_keys
                .iter()
                .any(|&tk| self.vir_query_contains_type_param_v(tk))
            {
                continue;
            }
            class_concrete_type_args
                .entry(key.class_name)
                .or_default()
                .push(key.type_keys.clone());
        }

        // Deduplicate type arg vectors per class using a set.
        // TypeId doesn't implement Ord, so we use a HashSet for dedup.
        for type_arg_vecs in class_concrete_type_args.values_mut() {
            let mut seen = FxHashSet::default();
            type_arg_vecs.retain(|v| seen.insert(v.clone()));
        }

        if tracing::enabled!(tracing::Level::DEBUG) {
            for (class_name, type_arg_vecs) in &class_concrete_type_args {
                let class_name_str = self.analyzed.display_name(*class_name);
                tracing::debug!(
                    class = %class_name_str,
                    type_arg_count = type_arg_vecs.len(),
                    type_args = ?type_arg_vecs,
                    "expand: per-class concrete type args"
                );
            }
        }
        tracing::debug!(
            class_count = class_concrete_type_args.len(),
            "expand_abstract_class_method_monomorphs: collected per-class concrete type args"
        );

        // Step 3: For each abstract template, expand with concrete type args for its class.
        //
        // Look up concrete type argument vectors for the template's class, then build
        // substitutions by mapping each vector position to the template's TypeParam.
        let mut expanded: Vec<ExpandedMethodData> = Vec::new();
        let mut expanded_keys: FxHashSet<ClassMethodMonomorphKey> = FxHashSet::default();

        for (abstract_key, tmpl) in &abstract_templates {
            // Extract the TypeParam positions from the abstract type_keys.
            // These tell us which positions in the type_keys are TypeParams
            // and what their NameIds are (for building substitutions).
            let abstract_type_param_positions: Vec<(usize, NameId)> = abstract_key
                .type_keys
                .iter()
                .enumerate()
                .filter_map(|(i, &tk)| self.vir_query_unwrap_type_param_v(tk).map(|name| (i, name)))
                .collect();
            if abstract_type_param_positions.is_empty() {
                continue;
            }

            // Look up concrete type arg vectors for this class
            let empty_vec = Vec::new();
            let concrete_type_arg_vecs = class_concrete_type_args
                .get(&abstract_key.class_name)
                .unwrap_or(&empty_vec);

            for concrete_type_args in concrete_type_arg_vecs {
                // Build concrete type_keys by replacing TypeParams with concrete args
                if concrete_type_args.len() != abstract_key.type_keys.len() {
                    continue; // Arity mismatch
                }

                let concrete_type_keys: Vec<VirTypeId> = abstract_key
                    .type_keys
                    .iter()
                    .enumerate()
                    .map(|(i, &tk)| {
                        if self.vir_query_unwrap_type_param_v(tk).is_some() {
                            concrete_type_args[i]
                        } else {
                            tk
                        }
                    })
                    .collect();

                // Skip if any concrete type_keys still contain TypeParams
                if concrete_type_keys
                    .iter()
                    .any(|&tk| self.vir_query_contains_type_param_v(tk))
                {
                    continue;
                }

                let concrete_key = ClassMethodMonomorphKey::new(
                    abstract_key.class_name,
                    abstract_key.method_name,
                    concrete_type_keys,
                );

                // Skip if already in VirProgram or already expanded
                if self
                    .analyzed
                    .vir_program()
                    .class_method_monomorphs
                    .contains_key(&concrete_key)
                {
                    continue;
                }
                if expanded_keys.contains(&concrete_key) {
                    continue;
                }

                // Build a substitution map from TypeParam NameIds to concrete types
                // using the abstract template's substitution structure.
                // Convert VirTypeId back to TypeId for substitution operations
                // (only key construction uses VirTypeId natively).
                let concrete_subs: FxHashMap<NameId, TypeId> = abstract_type_param_positions
                    .iter()
                    .map(|&(i, param_name)| (param_name, self.sema_type_id(concrete_type_args[i])))
                    .collect();

                // Build concrete substitutions for the class method (key_name -> concrete_ty)
                let concrete_class_subs: FxHashMap<NameId, TypeId> = tmpl
                    .substitutions
                    .iter()
                    .map(|(&key_name, &value_type_id)| {
                        if let Some(param_name) = self.vir_query_unwrap_type_param(value_type_id)
                            && let Some(&concrete_ty) = concrete_subs.get(&param_name)
                        {
                            return (key_name, concrete_ty);
                        }
                        (key_name, value_type_id)
                    })
                    .collect();

                // Substitute func_type for concrete param/return types
                let concrete_params: Vec<TypeId> = tmpl
                    .func_type
                    .params_id
                    .iter()
                    .map(|&param_ty| {
                        self.vir_query_lookup_substitute(param_ty, &concrete_class_subs)
                            .unwrap_or(param_ty)
                    })
                    .collect();
                let concrete_return = self
                    .vir_query_lookup_substitute(
                        tmpl.func_type.return_type_id,
                        &concrete_class_subs,
                    )
                    .unwrap_or(tmpl.func_type.return_type_id);
                let concrete_func_type = FunctionType::from_ids(
                    &concrete_params,
                    concrete_return,
                    tmpl.func_type.is_closure,
                );

                let concrete_self_type = self
                    .vir_query_lookup_substitute(tmpl.self_type, &concrete_class_subs)
                    .unwrap_or(tmpl.self_type);

                // Skip if any resolved types still contain TypeParams.
                // This catches cases where the method body references types from
                // other generic contexts that our substitution set doesn't cover.
                if concrete_params
                    .iter()
                    .any(|&p| self.vir_query_contains_type_param(p))
                    || self.vir_query_contains_type_param(concrete_return)
                    || self.vir_query_contains_type_param(concrete_self_type)
                {
                    continue;
                }

                // Generate mangled name string (no NameId needed)
                let class_name_str = self.analyzed.display_name(tmpl.class_name);
                let method_name_str = self.analyzed.display_name(tmpl.method_name);
                let type_keys_str: Vec<String> = concrete_key
                    .type_keys
                    .iter()
                    .map(|&ty| format!("{:?}", ty))
                    .collect();
                let mangled_name_str = format!(
                    "{}__method_{}__expand_{}",
                    class_name_str,
                    method_name_str,
                    type_keys_str.join("_")
                );

                tracing::debug!(
                    name = %mangled_name_str,
                    class = %class_name_str,
                    method = %method_name_str,
                    "expanding abstract class method monomorph template"
                );

                // Build VirTypeId-native substitutions for Cg context.
                let concrete_vir_subs: FxHashMap<NameId, VirTypeId> = concrete_class_subs
                    .iter()
                    .map(|(&k, &v)| (k, self.vir_lookup(v)))
                    .collect();

                expanded_keys.insert(concrete_key.clone());
                expanded.push(ExpandedMethodData {
                    concrete_key,
                    mangled_name_str,
                    template_mangled_name: tmpl.mangled_name,
                    func_type: concrete_func_type,
                    vir_substitutions: concrete_vir_subs,
                    class_name: tmpl.class_name,
                    self_type: concrete_self_type,
                    external_info: tmpl
                        .external_info
                        .map(crate::analyzed::ExternalMethodInfoRef::from),
                    func_key: None,
                });
            }
        }

        if expanded.is_empty() {
            return Ok(());
        }

        // Step 4: Declare all expanded instances in JIT and register for Cg lookup.
        // Registration MUST happen here (before compilation) so that other monomorph
        // bodies compiled later (e.g. Task.stream<i64>) can resolve calls to these
        // expanded methods (e.g. Channel<i64>.close()) via expanded_class_method_monomorphs.
        for data in &mut expanded {
            if data.external_info.is_some() {
                continue;
            }
            let param_type_ids: Vec<TypeId> = data.func_type.params_id.to_vec();
            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(data.func_type.return_type_id),
                super::signatures::SelfParam::Pointer,
            );
            let func_id = self.jit.declare_function(&data.mangled_name_str, &sig);
            let func_key = self.func_registry.intern_raw(data.mangled_name_str.clone());
            self.func_registry.set_func_id(func_key, func_id);
            self.func_registry
                .set_return_type(func_key, data.func_type.return_type_id);
            data.func_key = Some(func_key);

            // Register for Cg lookup immediately so that method dispatch can
            // find this expanded method when compiling other monomorph bodies.
            self.state.expanded_class_method_monomorphs.insert(
                data.concrete_key.clone(),
                crate::types::ExpandedClassMethodInfo {
                    func_key,
                    return_type_id: data.func_type.return_type_id,
                },
            );
        }

        // Step 5: Compile each expanded instance body
        for data in expanded {
            if data.external_info.is_some() {
                continue;
            }

            let func_key = data.func_key.expect("func_key should be set in step 4");
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found("expanded class method", &data.mangled_name_str)
            })?;

            if self.defined_functions.contains(&func_id) {
                continue;
            }

            // Get VIR function (provides param names and body)
            let vir_func = self
                .analyzed
                .get_vir_monomorph(data.template_mangled_name)
                .ok_or_else(|| {
                    CodegenError::not_found(
                        "VIR expanded class method monomorph template",
                        format!("{:?}", data.template_mangled_name),
                    )
                })?;

            // Compile the method body
            let module_id = self.analyzed.name_table().module_of(data.class_name);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();

            let saved_bindings = Some(std::mem::take(&mut self.global_module_bindings));
            let compile_result = (|| -> CodegenResult<()> {
                let param_type_ids: Vec<TypeId> = data.func_type.params_id.to_vec();
                let return_type_id = data.func_type.return_type_id;
                let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
                let params: Vec<_> = vir_func
                    .params
                    .iter()
                    .zip(param_type_ids.iter())
                    .zip(param_cranelift_types.iter())
                    .map(|((vp, &type_id), &cranelift_type)| {
                        (vp.0, self.vir_lookup(type_id), cranelift_type)
                    })
                    .collect();

                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    super::signatures::SelfParam::Pointer,
                );
                self.jit.ctx.func.signature = sig;

                let self_type_id = data.self_type;
                let self_sym = self.self_symbol();
                let self_vir_ty = self.vir_lookup(self_type_id);
                let self_binding = (self_sym, self_vir_ty, self.pointer_type);

                let source_file_ptr = self.source_file_ptr();
                let return_vir_ty = self.vir_lookup(return_type_id);
                let mut builder_ctx = FunctionBuilderContext::new();
                let cg_module_id = Some(module_id);
                // Hoist module interner Rc so it outlives the compile_env borrow.
                let module_interner_rc =
                    self.analyzed.vir_program().module_interner_rc(&module_path);
                {
                    let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                    let env = if let Some(ref interner) = module_interner_rc {
                        compile_env!(self, interner, source_file_ptr)
                    } else {
                        compile_env!(self, source_file_ptr)
                    };
                    let mut codegen_ctx = CodegenCtx::new(
                        &mut self.jit.module,
                        &mut self.func_registry,
                        &mut self.pending_monomorphs,
                    );

                    let config =
                        FunctionCompileConfig::method(params, self_binding, Some(return_vir_ty));
                    compile_function_inner_with_vir(
                        builder,
                        &mut codegen_ctx,
                        &env,
                        config,
                        &vir_func.body,
                        cg_module_id,
                        Some(&data.vir_substitutions),
                    )?;
                }

                self.finalize_function(func_id)?;
                Ok(())
            })();
            if let Some(bindings) = saved_bindings {
                self.global_module_bindings = bindings;
            }
            compile_result?;
        }

        tracing::debug!("expanded abstract class method monomorphs complete");

        Ok(())
    }

    // ===================================================================
    // Unified monomorphization entry points
    // ===================================================================

    /// Declare all monomorphized instances (functions, class methods, static methods)
    pub(super) fn declare_all_monomorphized_instances(&mut self) -> CodegenResult<()> {
        // Note: Nested generic calls are now discovered during sema analysis,
        // so we don't need to expand instances here.
        self.declare_monomorphized_instances()?;
        self.declare_class_method_monomorphized_instances()?;
        self.declare_static_method_monomorphized_instances()?;
        Ok(())
    }

    /// Compile all monomorphized instances (functions, class methods, static methods).
    ///
    /// When `program` is `Some`, main-program ASTs are available for lookup.
    /// When `None` (module-only phase), only module programs are searched and
    /// instances whose ASTs aren't found are silently skipped — they will be
    /// compiled later by the program phase or the demand-driven fixpoint loop.
    pub(super) fn compile_all_monomorphized_instances(
        &mut self,
        is_program_phase: bool,
    ) -> CodegenResult<()> {
        self.compile_monomorphized_instances(is_program_phase)?;
        self.compile_class_method_monomorphized_instances(is_program_phase)?;
        self.compile_static_method_monomorphized_instances(is_program_phase)?;
        Ok(())
    }

    // ===================================================================
    // Fixpoint loop for pending (demand-declared) monomorphs
    // ===================================================================

    /// Compile any monomorphs that were lazily declared during expression compilation.
    ///
    /// During compilation of function bodies, calls to undeclared monomorphs trigger
    /// demand-declaration (via `Cg::try_demand_declare_monomorph`) which assigns a
    /// FuncId but does not compile the body. This method drains those pending
    /// monomorphs and compiles their bodies. Since compiling one body may trigger
    /// further demand-declarations, this repeats until the queue is empty (fixpoint).
    ///
    pub(super) fn compile_pending_monomorphs(&mut self) -> CodegenResult<()> {
        use crate::types::PendingMonomorph;

        const MAX_FIXPOINT_ITERATIONS: usize = 100;

        let program_module = self.program_module();
        let mut prev_batch_size: usize = 0;

        for iteration in 0..MAX_FIXPOINT_ITERATIONS {
            let batch = std::mem::take(&mut self.pending_monomorphs);
            if batch.is_empty() {
                tracing::debug!(
                    iterations = iteration,
                    "compile_pending_monomorphs: fixpoint reached"
                );
                return Ok(());
            }

            if tracing::enabled!(tracing::Level::DEBUG) {
                let names: Vec<String> = batch
                    .iter()
                    .map(|p| self.describe_pending_monomorph(p))
                    .collect();
                tracing::debug!(
                    iteration,
                    count = batch.len(),
                    monomorphs = ?names,
                    "compile_pending_monomorphs: compiling batch"
                );
            }

            let defined_before = self.defined_functions.len();
            let batch_size = batch.len();

            for pending in &batch {
                match pending {
                    PendingMonomorph::Function(instance) => {
                        self.compile_pending_function(instance, program_module)?;
                    }
                    PendingMonomorph::ClassMethod(instance) => {
                        self.compile_pending_class_method(instance, program_module)?;
                    }
                    PendingMonomorph::StaticMethod(instance) => {
                        self.compile_pending_static_method(instance, program_module)?;
                    }
                }
            }

            let newly_defined = self.defined_functions.len() - defined_before;
            let next_pending = self.pending_monomorphs.len();

            // No-progress detection: if we compiled nothing new and still have at
            // least as many pending monomorphs as before, the loop is stuck.
            if newly_defined == 0 && next_pending >= prev_batch_size && next_pending > 0 {
                return Err(self.stuck_monomorphs_error(&batch, iteration + 1, "no progress"));
            }

            prev_batch_size = batch_size;
        }

        // Cap exceeded — build a diagnostic from whatever is still pending.
        let stuck = std::mem::take(&mut self.pending_monomorphs);
        Err(self.stuck_monomorphs_error(&stuck, MAX_FIXPOINT_ITERATIONS, "iteration cap exceeded"))
    }

    /// Return a one-line description of a pending monomorph for tracing / errors.
    fn describe_pending_monomorph(&self, pending: &crate::types::PendingMonomorph) -> String {
        use crate::types::PendingMonomorph;
        match pending {
            PendingMonomorph::Function(inst) => {
                let name = self.analyzed.display_name(inst.original_name);
                let subs = self.format_substitutions(&inst.substitutions);
                let module = self.module_of_name(inst.original_name);
                format!("fn {name}<{subs}> (module: {module})")
            }
            PendingMonomorph::ClassMethod(inst) => {
                let class = self.analyzed.display_name(inst.class_name);
                let method = self.analyzed.display_name(inst.method_name);
                let subs = self.format_substitutions(&inst.substitutions);
                let module = self.module_of_name(inst.class_name);
                format!("{class}.{method}<{subs}> (module: {module})")
            }
            PendingMonomorph::StaticMethod(inst) => {
                let class = self.analyzed.display_name(inst.class_name);
                let method = self.analyzed.display_name(inst.method_name);
                let subs = self.format_substitutions(&inst.substitutions);
                let module = self.module_of_name(inst.class_name);
                format!("{class}::{method}<{subs}> (module: {module})")
            }
        }
    }

    /// Format a substitution map as `T=TypeId(3), U=TypeId(7)`.
    fn format_substitutions(&self, subs: &FxHashMap<NameId, TypeId>) -> String {
        let mut parts: Vec<String> = subs
            .iter()
            .map(|(&name_id, &type_id)| {
                let name = self.analyzed.display_name(name_id);
                format!("{name}={type_id:?}")
            })
            .collect();
        parts.sort();
        parts.join(", ")
    }

    /// Get the module path for a NameId (for diagnostics).
    fn module_of_name(&self, name_id: NameId) -> String {
        let module_id = self.analyzed.name_table().module_of(name_id);
        let path = self.analyzed.name_table().module_path(module_id);
        if path.is_empty() {
            "<main>".to_string()
        } else {
            path.to_string()
        }
    }

    /// Build a structured error for stuck/capped monomorphs.
    fn stuck_monomorphs_error(
        &self,
        stuck: &[crate::types::PendingMonomorph],
        iterations: usize,
        reason: &str,
    ) -> CodegenError {
        let mut details = format!(
            "monomorph fixpoint loop failed ({reason}) after {iterations} iteration(s)\n\
             stuck monomorphs ({count}):\n",
            count = stuck.len(),
        );
        for pending in stuck {
            details.push_str("  - ");
            details.push_str(&self.describe_pending_monomorph(pending));
            details.push('\n');
        }
        CodegenError::internal_with_context("monomorph fixpoint loop did not converge", details)
    }

    /// Compile a single pending free-function monomorph.
    fn compile_pending_function(
        &mut self,
        instance: &VirMonomorphInfo,
        program_module: ModuleId,
    ) -> CodegenResult<()> {
        // Skip external functions
        if self.is_external_func(instance.original_name) {
            return Ok(());
        }

        let func_module = self.analyzed.name_table().module_of(instance.original_name);
        if func_module == program_module {
            self.compile_monomorphized_function(instance)?;
        } else {
            let found = self.compile_monomorphized_module_function(instance)?;
            if !found {
                let func_name = self.analyzed.display_name(instance.original_name);
                return Err(CodegenError::internal_with_context(
                    "pending monomorph: VIR function not found",
                    func_name,
                ));
            }
        }
        Ok(())
    }

    /// Compile a single pending class method monomorph.
    fn compile_pending_class_method(
        &mut self,
        instance: &VirClassMethodMonomorphInfo,
        program_module: ModuleId,
    ) -> CodegenResult<()> {
        // Skip external and abstract instances
        if instance.external_info.is_some() {
            return Ok(());
        }
        if self.is_abstract_vir_class_method_monomorph(instance) {
            return Ok(());
        }

        let class_module = self.analyzed.name_table().module_of(instance.class_name);
        let module_path = if class_module == program_module {
            None
        } else {
            Some(
                self.analyzed
                    .name_table()
                    .module_path(class_module)
                    .to_string(),
            )
        };

        self.compile_monomorphized_class_method(instance, module_path.as_deref())
    }

    /// Compile a single pending static method monomorph.
    fn compile_pending_static_method(
        &mut self,
        instance: &VirStaticMethodMonomorphInfo,
        program_module: ModuleId,
    ) -> CodegenResult<()> {
        if self.is_abstract_vir_static_method_monomorph(instance) {
            return Ok(());
        }

        let class_module = self.analyzed.name_table().module_of(instance.class_name);
        let module_path = if class_module == program_module {
            None
        } else {
            Some(
                self.analyzed
                    .name_table()
                    .module_path(class_module)
                    .to_string(),
            )
        };

        self.compile_monomorphized_static_method(instance, module_path.as_deref())
    }

    /// Build the monomorph name index from VirProgram's monomorph maps.
    ///
    /// Creates a `FxHashMap<NameId, MonomorphIndexEntry>` keyed by `mangled_name`
    /// for O(1) lookup in `try_demand_declare_monomorph`. Entries that would be
    /// skipped during demand-declaration (external methods, abstract templates)
    /// are excluded.
    ///
    /// Called before body compilation in both `compile_module_functions` and
    /// `compile_program_body`.
    pub(super) fn build_monomorph_index(&mut self) {
        let vir_program = self.analyzed.vir_program();
        let type_table = &vir_program.type_table;
        let mut index = FxHashMap::default();

        // Index free-function monomorphs (no filtering needed)
        for instance in vir_program.free_monomorphs.values() {
            index.insert(
                instance.mangled_name,
                MonomorphIndexEntry::Function(instance.clone()),
            );
        }

        // Index class method monomorphs (skip external + abstract templates)
        for instance in vir_program.class_method_monomorphs.values() {
            if instance.external_info.is_some() {
                continue;
            }
            if instance
                .vir_substitutions
                .values()
                .any(|&vir_type_id| matches!(type_table.get(vir_type_id), VirType::Param { .. }))
            {
                continue;
            }
            index.insert(
                instance.mangled_name,
                MonomorphIndexEntry::ClassMethod(instance.clone()),
            );
        }

        // Index static method monomorphs (skip abstract templates)
        for instance in vir_program.static_method_monomorphs.values() {
            if instance
                .vir_substitutions
                .values()
                .any(|&vir_type_id| matches!(type_table.get(vir_type_id), VirType::Param { .. }))
            {
                continue;
            }
            index.insert(
                instance.mangled_name,
                MonomorphIndexEntry::StaticMethod(instance.clone()),
            );
        }

        tracing::debug!(entry_count = index.len(), "built monomorph name index");
        self.state.monomorph_index = index;
    }
}
