use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext};

use super::Compiler;
use super::common::{FunctionCompileConfig, compile_function_inner_with_params};

use crate::errors::{CodegenError, CodegenResult};
use crate::types::CodegenCtx;
use vole_frontend::ast::InterfaceMethod;
use vole_frontend::{Decl, FuncDecl, Interner, Program};
use vole_identity::{ModuleId, NameId};
use vole_sema::generic::{
    ClassMethodMonomorphInstance, MonomorphInstance, MonomorphInstanceTrait,
    StaticMethodMonomorphInstance,
};
use vole_sema::type_arena::TypeId;

use crate::types::function_name_id_with_interner;

impl Compiler<'_> {
    /// Declare a single monomorphized instance using the common trait interface.
    /// `has_self_param` indicates if a self pointer should be prepended to parameters.
    pub(super) fn declare_monomorph_instance<T: MonomorphInstanceTrait>(
        &mut self,
        instance: &T,
        has_self_param: bool,
    ) {
        use super::signatures::SelfParam;

        let mangled_name = self.query().display_name(instance.mangled_name());
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
    pub(super) fn declare_monomorphized_instances(
        &mut self,
        modules_only: bool,
    ) -> CodegenResult<()> {
        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry()
            .monomorph_cache
            .collect_instances();

        for instance in instances {
            // Skip external functions - they don't need JIT compilation
            // They're called directly via native_registry
            if self.is_external_func(instance.original_name) {
                continue;
            }

            // When compiling modules only, skip monomorphs whose original function
            // lives in the main program — they would be declared but never compiled.
            if modules_only {
                let module_id = self.analyzed.name_table().module_of(instance.original_name);
                let module_path = self
                    .analyzed
                    .name_table()
                    .module_path(module_id)
                    .to_string();
                if !self.analyzed.module_programs.contains_key(&module_path) {
                    continue;
                }
            }

            self.declare_monomorph_instance(&instance, false);
        }

        Ok(())
    }

    /// Compile all monomorphized function instances
    pub(super) fn compile_monomorphized_instances(
        &mut self,
        program: &Program,
    ) -> CodegenResult<()> {
        // Build a map of generic function names to their ASTs
        // Include both explicit generics (type_params in AST) and implicit generics
        // (structural type params that create generic_info in entity registry)
        // Recursively walks into tests blocks to find scoped generic functions.
        let mut generic_func_asts: FxHashMap<NameId, &FuncDecl> = FxHashMap::default();
        let program_module = self.program_module();
        self.collect_generic_func_asts(
            &program.declarations,
            program_module,
            &mut generic_func_asts,
        );

        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry()
            .monomorph_cache
            .collect_instances();

        for instance in instances {
            // Skip external functions - they don't have AST bodies
            // Generic externals are called directly with type erasure at call sites
            if self.is_external_func(instance.original_name) {
                continue;
            }

            // First try the main program's generic functions
            if let Some(func) = generic_func_asts.get(&instance.original_name) {
                self.compile_monomorphized_function(func, &instance)?;
                continue;
            }

            // Then try module programs (for prelude generic functions like print/println)
            let found = self.compile_monomorphized_module_function(&instance)?;
            if !found {
                let func_name = self.query().display_name(instance.original_name);
                return Err(CodegenError::internal_with_context(
                    "generic function AST not found",
                    func_name,
                ));
            }
        }

        Ok(())
    }

    /// Compile monomorphized function instances that belong to modules.
    /// Skips external functions and main-program functions (those are compiled later).
    pub(super) fn compile_module_monomorphized_instances(&mut self) -> CodegenResult<()> {
        let instances = self
            .analyzed
            .entity_registry()
            .monomorph_cache
            .collect_instances();

        for instance in instances {
            if self.is_external_func(instance.original_name) {
                continue;
            }

            // Only compile instances whose original function lives in a module
            let module_id = self.analyzed.name_table().module_of(instance.original_name);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            if !self.analyzed.module_programs.contains_key(&module_path) {
                continue;
            }

            self.compile_monomorphized_module_function(&instance)?;
        }

        Ok(())
    }

    /// Compile a monomorphized instance of a module function.
    /// Searches module programs for the generic function AST.
    fn compile_monomorphized_module_function(
        &mut self,
        instance: &MonomorphInstance,
    ) -> CodegenResult<bool> {
        // Find which module contains this function
        let module_id = self.analyzed.name_table().module_of(instance.original_name);
        let module_path = self
            .analyzed
            .name_table()
            .module_path(module_id)
            .to_string();

        let Some((module_program, module_interner)) =
            self.analyzed.module_programs.get(&module_path)
        else {
            return Ok(false);
        };

        // Find the generic function in the module
        let func = module_program.declarations.iter().find_map(|decl| {
            if let Decl::Function(func) = decl {
                let name_id = function_name_id_with_interner(
                    self.analyzed,
                    module_interner,
                    module_id,
                    func.name,
                );
                if name_id == Some(instance.original_name) {
                    return Some(func);
                }
            }
            None
        });

        let Some(func) = func else {
            return Ok(false);
        };

        self.compile_monomorphized_function_with_module(func, instance, module_interner, module_id)
    }

    /// Compile a monomorphized function from a module with its own interner.
    fn compile_monomorphized_function_with_module(
        &mut self,
        func: &FuncDecl,
        instance: &MonomorphInstance,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<bool> {
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized function", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(true);
        }

        // Clear main-program module bindings while compiling module interner code.
        let saved_bindings = std::mem::take(&mut self.global_module_bindings);
        let compile_result = (|| -> CodegenResult<bool> {
            let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
            let return_type_id = instance.func_type.return_type_id;
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = func
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(return_type_id),
                super::signatures::SelfParam::None,
            );
            self.jit.ctx.func.signature = sig;

            let source_file_ptr = self.source_file_ptr();
            let no_global_inits = FxHashMap::default();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(
                    self,
                    module_interner,
                    &no_global_inits,
                    source_file_ptr,
                    module_id
                );
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config =
                    FunctionCompileConfig::top_level(&func.body, params, Some(return_type_id));
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    Some(module_id),
                    Some(&instance.substitutions),
                )?;
            }

            self.finalize_function(func_id)?;
            Ok(true)
        })();
        self.global_module_bindings = saved_bindings;
        compile_result
    }

    /// Compile a single monomorphized function instance
    fn compile_monomorphized_function(
        &mut self,
        func: &FuncDecl,
        instance: &MonomorphInstance,
    ) -> CodegenResult<()> {
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized function", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(());
        }

        // Get parameter types and build config
        let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
        let return_type_id = instance.func_type.return_type_id;
        let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = func
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_cranelift_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Create function signature from concrete types using shared builder
        let sig = self.build_signature_from_type_ids(
            &param_type_ids,
            Some(return_type_id),
            super::signatures::SelfParam::None,
        );
        self.jit.ctx.func.signature = sig;

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let config = FunctionCompileConfig::top_level(&func.body, params, Some(return_type_id));
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                Some(&instance.substitutions),
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Check if a class method monomorph is abstract (contains TypeParam substitutions).
    /// Abstract entries are templates from generic class body analysis and are not compilable.
    fn is_abstract_class_method_monomorph(&self, instance: &ClassMethodMonomorphInstance) -> bool {
        let arena = self.analyzed.type_arena();
        instance
            .substitutions
            .values()
            .any(|&type_id| arena.unwrap_type_param(type_id).is_some())
    }

    /// Check if a static method monomorph is abstract (contains TypeParam substitutions).
    fn is_abstract_static_method_monomorph(
        &self,
        instance: &StaticMethodMonomorphInstance,
    ) -> bool {
        let arena = self.analyzed.type_arena();
        instance
            .substitutions
            .values()
            .any(|&type_id| arena.unwrap_type_param(type_id).is_some())
    }

    /// Returns true when the type references a nominal definition from the main
    /// program (or a tests virtual module), not from imported module programs.
    fn type_depends_on_program_definitions(&self, type_id: TypeId) -> bool {
        let arena = self.analyzed.type_arena();

        let nominal_is_program_owned = |type_def_id| {
            let name_id = self.query().get_type(type_def_id).name_id;
            let module_id = self.analyzed.name_table().module_of(name_id);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            !self.analyzed.module_programs.contains_key(&module_path)
        };

        if let Some((type_def_id, type_args)) = arena.unwrap_class(type_id) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions(ty));
        }
        if let Some((type_def_id, type_args)) = arena.unwrap_struct(type_id) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions(ty));
        }
        if let Some((type_def_id, type_args)) = arena.unwrap_interface(type_id) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions(ty));
        }
        if let Some(elem) = arena.unwrap_array(type_id) {
            return self.type_depends_on_program_definitions(elem);
        }
        if let Some((elem, _)) = arena.unwrap_fixed_array(type_id) {
            return self.type_depends_on_program_definitions(elem);
        }
        if let Some(elements) = arena.unwrap_tuple(type_id) {
            return elements
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions(ty));
        }
        if let Some(variants) = arena.unwrap_union(type_id) {
            return variants
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions(ty));
        }
        if let Some((ok_type, err_type)) = arena.unwrap_fallible(type_id) {
            return self.type_depends_on_program_definitions(ok_type)
                || self.type_depends_on_program_definitions(err_type);
        }
        if let Some((params, ret, _)) = arena.unwrap_function(type_id) {
            return params
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions(ty))
                || self.type_depends_on_program_definitions(ret);
        }

        false
    }

    /// Returns true when any substitution type depends on main-program definitions.
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
        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry()
            .class_method_monomorph_cache
            .collect_instances();

        tracing::debug!(
            instance_count = instances.len(),
            "declaring class method monomorphized instances"
        );

        for instance in instances {
            // External methods are runtime functions - no declaration needed
            if instance.external_info.is_some() {
                continue;
            }

            // Skip abstract monomorph templates (e.g., T -> TypeParam(T)).
            if self.is_abstract_class_method_monomorph(&instance) {
                continue;
            }

            // Class methods have self parameter
            self.declare_monomorph_instance(&instance, true);
        }

        Ok(())
    }

    /// Compile all monomorphized class method instances
    pub(super) fn compile_class_method_monomorphized_instances(
        &mut self,
        program: &Program,
    ) -> CodegenResult<()> {
        let class_asts = self.build_generic_type_asts(program);

        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry()
            .class_method_monomorph_cache
            .collect_instances();

        tracing::debug!(
            instance_count = instances.len(),
            "compiling class method monomorphized instances"
        );

        for instance in instances {
            // External methods are runtime functions - no compilation needed
            if instance.external_info.is_some() {
                tracing::debug!(
                    class_name = ?instance.class_name,
                    method_name = ?instance.method_name,
                    "skipping external method - calls runtime function directly"
                );
                continue;
            }

            // Skip abstract monomorph templates (e.g., T -> TypeParam(T)).
            if self.is_abstract_class_method_monomorph(&instance) {
                continue;
            }

            let class_name_str = self.query().display_name(instance.class_name);
            tracing::debug!(
                class_name = %class_name_str,
                class_name_id = ?instance.class_name,
                method_name = ?instance.method_name,
                "looking for method to compile"
            );

            // Try to find the method in a class
            let method_name_str = self.query().display_name(instance.method_name);
            if let Some(class) = class_asts.get(&instance.class_name) {
                let method = class
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_class_method(method, &instance, None)?;
                    continue;
                }
            }

            // Fallback: search module programs for generic classes from imported modules (e.g. prelude)
            // Clone the method AST to avoid borrow conflict with mutable self borrow.
            {
                let found = self
                    .find_class_method_in_modules(instance.class_name, &method_name_str)
                    .cloned();
                if let Some(method) = found {
                    // Determine the module path so compile can look up the correct interner
                    let module_id = self.analyzed.name_table().module_of(instance.class_name);
                    let module_path = self
                        .analyzed
                        .name_table()
                        .module_path(module_id)
                        .to_string();
                    self.compile_monomorphized_class_method(
                        &method,
                        &instance,
                        Some(&module_path),
                    )?;
                    continue;
                }
            }

            // Fallback: search implement blocks for methods on generic classes
            let program_module = self.program_module();
            if let Some(method) = self.find_implement_block_method(
                &program.declarations,
                instance.class_name,
                &method_name_str,
                program_module,
            ) {
                self.compile_monomorphized_class_method(method, &instance, None)?;
                continue;
            }

            // Method not found - this shouldn't happen if sema was correct
            let class_name = self.query().display_name(instance.class_name);
            return Err(CodegenError::not_found(
                "method",
                format!("{} in class {}", method_name_str, class_name),
            ));
        }

        Ok(())
    }

    /// Compile a single monomorphized class method instance.
    /// When `module_path` is Some, the method AST comes from a loaded module
    /// and its symbols must be resolved with that module's interner.
    fn compile_monomorphized_class_method(
        &mut self,
        method: &FuncDecl,
        instance: &ClassMethodMonomorphInstance,
        module_path: Option<&str>,
    ) -> CodegenResult<()> {
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized class method", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(());
        }

        let saved_bindings = if module_path.is_some() {
            Some(std::mem::take(&mut self.global_module_bindings))
        } else {
            None
        };
        let compile_result = (|| -> CodegenResult<()> {
            // Get param and return types, build config
            let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
            let return_type_id = instance.func_type.return_type_id;
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
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
            let self_binding = (self_sym, self_type_id, self.pointer_type);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let empty_inits = FxHashMap::default();
            let mut builder_ctx = FunctionBuilderContext::new();
            // Determine module_id for Cg context (needed for expression data lookup)
            let cg_module_id =
                module_path.map(|_| self.analyzed.name_table().module_of(instance.class_name));
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = if let Some(path) = module_path {
                    let (_, interner) = &self.analyzed.module_programs[path];
                    let module_id =
                        cg_module_id.expect("cg_module_id set when module_path is Some");
                    compile_env!(self, interner, &empty_inits, source_file_ptr, module_id)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config = FunctionCompileConfig::method(
                    &method.body,
                    params,
                    self_binding,
                    Some(return_type_id),
                );
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    cg_module_id,
                    Some(&instance.substitutions),
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
        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry()
            .static_method_monomorph_cache
            .collect_instances();

        tracing::debug!(
            instance_count = instances.len(),
            "declaring static method monomorphized instances"
        );

        for instance in instances {
            if self.is_abstract_static_method_monomorph(&instance) {
                continue;
            }
            // Static methods don't have self parameter
            self.declare_monomorph_instance(&instance, false);
        }

        Ok(())
    }

    /// Compile all monomorphized static method instances
    pub(super) fn compile_static_method_monomorphized_instances(
        &mut self,
        program: &Program,
    ) -> CodegenResult<()> {
        let class_asts = self.build_generic_type_asts(program);

        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry()
            .static_method_monomorph_cache
            .collect_instances();

        tracing::debug!(
            instance_count = instances.len(),
            "compiling static method monomorphized instances"
        );

        for instance in instances {
            if self.is_abstract_static_method_monomorph(&instance) {
                continue;
            }
            let class_name_str = self.query().display_name(instance.class_name);
            tracing::debug!(
                class_name = %class_name_str,
                class_name_id = ?instance.class_name,
                method_name = ?instance.method_name,
                "looking for static method to compile"
            );

            let method_name_str = self.query().display_name(instance.method_name);

            // Try to find the static method in a class from the main program
            if let Some(class) = class_asts.get(&instance.class_name)
                && let Some(ref statics) = class.statics
            {
                let method = statics
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_static_method(method, &instance, None)?;
                    continue;
                }
            }

            // Fallback: search module programs for generic classes from imported modules
            {
                let found = self
                    .find_static_method_in_modules(instance.class_name, &method_name_str)
                    .cloned();
                if let Some(method) = found {
                    let module_id = self.analyzed.name_table().module_of(instance.class_name);
                    let module_path = self
                        .analyzed
                        .name_table()
                        .module_path(module_id)
                        .to_string();
                    self.compile_monomorphized_static_method(
                        &method,
                        &instance,
                        Some(&module_path),
                    )?;
                    continue;
                }
            }

            // Method not found - this shouldn't happen if sema was correct
            let class_name = self.query().display_name(instance.class_name);
            let method_name = self.query().display_name(instance.method_name);
            return Err(CodegenError::not_found(
                "static method",
                format!("{} in class {}", method_name, class_name),
            ));
        }

        Ok(())
    }

    /// Compile a single monomorphized static method instance.
    /// When `module_path` is Some, the method AST comes from a loaded module
    /// and its symbols must be resolved with that module's interner.
    fn compile_monomorphized_static_method(
        &mut self,
        method: &InterfaceMethod,
        instance: &StaticMethodMonomorphInstance,
        module_path: Option<&str>,
    ) -> CodegenResult<()> {
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("monomorphized static method", &mangled_name))?;
        if self.defined_functions.contains(&func_id) {
            return Ok(());
        }

        let saved_bindings = if module_path.is_some() {
            Some(std::mem::take(&mut self.global_module_bindings))
        } else {
            None
        };
        let compile_result = (|| -> CodegenResult<()> {
            // Get param and return types, build config
            let param_type_ids: Vec<TypeId> = instance.func_type.params_id.to_vec();
            let return_type_id = instance.func_type.return_type_id;
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            // Create signature (no self parameter) with concrete types using shared builder
            let sig = self.build_signature_from_type_ids(
                &param_type_ids,
                Some(return_type_id),
                super::signatures::SelfParam::None,
            );
            self.jit.ctx.func.signature = sig;

            // Get method body
            let body = method.body.as_ref().ok_or_else(|| {
                CodegenError::internal_with_context("static method has no body", &mangled_name)
            })?;

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let empty_inits = FxHashMap::default();
            let mut builder_ctx = FunctionBuilderContext::new();
            // Determine module_id for Cg context (needed for expression data lookup)
            let cg_module_id =
                module_path.map(|_| self.analyzed.name_table().module_of(instance.class_name));
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = if let Some(path) = module_path {
                    let (_, interner) = &self.analyzed.module_programs[path];
                    let module_id =
                        cg_module_id.expect("cg_module_id set when module_path is Some");
                    compile_env!(self, interner, &empty_inits, source_file_ptr, module_id)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config = FunctionCompileConfig::top_level(body, params, Some(return_type_id));
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    cg_module_id,
                    Some(&instance.substitutions),
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

    /// Compile only class method monomorphized instances that belong to imported modules.
    pub(super) fn compile_module_class_method_monomorphized_instances(
        &mut self,
    ) -> CodegenResult<()> {
        let instances = self
            .analyzed
            .entity_registry()
            .class_method_monomorph_cache
            .collect_instances();

        let mut module_instances: Vec<(ClassMethodMonomorphInstance, String)> = Vec::new();
        for instance in instances {
            if instance.external_info.is_some()
                || self.is_abstract_class_method_monomorph(&instance)
            {
                continue;
            }

            let module_id = self.analyzed.name_table().module_of(instance.class_name);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            if !self.analyzed.module_programs.contains_key(&module_path) {
                continue;
            }
            if self.substitutions_depend_on_program_definitions(&instance.substitutions) {
                continue;
            }

            module_instances.push((instance, module_path));
        }

        // Declare all module-safe instances first so cross-calls between generic
        // methods resolve regardless of compilation order.
        for (instance, _) in &module_instances {
            self.declare_monomorph_instance(instance, true);
        }

        for (instance, module_path) in module_instances {
            let method_name_str = self.query().display_name(instance.method_name);

            // Class body methods
            if let Some(method) = self
                .find_class_method_in_modules(instance.class_name, &method_name_str)
                .cloned()
            {
                self.compile_monomorphized_class_method(&method, &instance, Some(&module_path))?;
                continue;
            }

            // Implement block methods in the module
            let module_id = self.analyzed.name_table().module_of(instance.class_name);
            let method_from_impl = {
                let (module_program, _) = &self.analyzed.module_programs[&module_path];
                self.find_implement_block_method(
                    &module_program.declarations,
                    instance.class_name,
                    &method_name_str,
                    module_id,
                )
                .cloned()
            };
            if let Some(method) = method_from_impl {
                self.compile_monomorphized_class_method(&method, &instance, Some(&module_path))?;
                continue;
            }

            let class_name = self.query().display_name(instance.class_name);
            return Err(CodegenError::not_found(
                "module class method",
                format!("{} in class {}", method_name_str, class_name),
            ));
        }

        Ok(())
    }

    /// Compile only static method monomorphized instances that belong to imported modules.
    pub(super) fn compile_module_static_method_monomorphized_instances(
        &mut self,
    ) -> CodegenResult<()> {
        let instances = self
            .analyzed
            .entity_registry()
            .static_method_monomorph_cache
            .collect_instances();

        let mut module_instances: Vec<(StaticMethodMonomorphInstance, String)> = Vec::new();
        for instance in instances {
            if self.is_abstract_static_method_monomorph(&instance) {
                continue;
            }
            let module_id = self.analyzed.name_table().module_of(instance.class_name);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            if !self.analyzed.module_programs.contains_key(&module_path) {
                continue;
            }
            if self.substitutions_depend_on_program_definitions(&instance.substitutions) {
                continue;
            }

            module_instances.push((instance, module_path));
        }

        // Declare all module-safe instances first so static methods can call
        // other generic static methods independent of compile order.
        for (instance, _) in &module_instances {
            self.declare_monomorph_instance(instance, false);
        }

        for (instance, module_path) in module_instances {
            let method_name_str = self.query().display_name(instance.method_name);
            if let Some(method) = self
                .find_static_method_in_modules(instance.class_name, &method_name_str)
                .cloned()
            {
                self.compile_monomorphized_static_method(&method, &instance, Some(&module_path))?;
                continue;
            }

            let class_name = self.query().display_name(instance.class_name);
            return Err(CodegenError::not_found(
                "module static method",
                format!("{} in class {}", method_name_str, class_name),
            ));
        }

        Ok(())
    }

    // ===================================================================
    // Unified monomorphization entry points
    // ===================================================================

    /// Declare all monomorphized instances (functions, class methods, static methods)
    pub(super) fn declare_all_monomorphized_instances(&mut self) -> CodegenResult<()> {
        // Note: Nested generic calls are now discovered during sema analysis,
        // so we don't need to expand instances here.
        self.declare_monomorphized_instances(false)?;
        self.declare_class_method_monomorphized_instances()?;
        self.declare_static_method_monomorphized_instances()?;
        Ok(())
    }

    /// Compile all monomorphized instances (functions, class methods, static methods)
    pub(super) fn compile_all_monomorphized_instances(
        &mut self,
        program: &Program,
    ) -> CodegenResult<()> {
        self.compile_monomorphized_instances(program)?;
        self.compile_class_method_monomorphized_instances(program)?;
        self.compile_static_method_monomorphized_instances(program)?;
        Ok(())
    }
}
