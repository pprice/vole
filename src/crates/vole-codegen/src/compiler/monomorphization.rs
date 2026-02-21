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

/// Data for an expanded class method monomorph (used during template expansion).
struct ExpandedMethodData {
    concrete_key: vole_sema::generic::ClassMethodMonomorphKey,
    mangled_name_str: String,
    func_type: vole_sema::types::FunctionType,
    substitutions: FxHashMap<NameId, TypeId>,
    class_name: NameId,
    method_name: NameId,
    self_type: TypeId,
    external_info: Option<vole_sema::implement_registry::ExternalMethodInfo>,
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
        // The IIFE ensures bindings are restored even when `?` returns early.
        // Note: a panic inside the closure would skip the restore, but panics
        // during compilation are fatal to the entire process anyway.
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
                let env = compile_env!(self, module_interner, &no_global_inits, source_file_ptr);
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

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
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

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
        let mut visited = rustc_hash::FxHashSet::default();
        self.type_depends_on_program_definitions_inner(type_id, &mut visited)
    }

    fn type_depends_on_program_definitions_inner(
        &self,
        type_id: TypeId,
        visited: &mut rustc_hash::FxHashSet<TypeId>,
    ) -> bool {
        if !visited.insert(type_id) {
            return false; // cycle — treat as not program-owned
        }

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
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((type_def_id, type_args)) = arena.unwrap_struct(type_id) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((type_def_id, type_args)) = arena.unwrap_interface(type_id) {
            return nominal_is_program_owned(type_def_id)
                || type_args
                    .iter()
                    .copied()
                    .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some(elem) = arena.unwrap_array(type_id) {
            return self.type_depends_on_program_definitions_inner(elem, visited);
        }
        if let Some((elem, _)) = arena.unwrap_fixed_array(type_id) {
            return self.type_depends_on_program_definitions_inner(elem, visited);
        }
        if let Some(elements) = arena.unwrap_tuple(type_id) {
            return elements
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some(variants) = arena.unwrap_union(type_id) {
            return variants
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited));
        }
        if let Some((ok_type, err_type)) = arena.unwrap_fallible(type_id) {
            return self.type_depends_on_program_definitions_inner(ok_type, visited)
                || self.type_depends_on_program_definitions_inner(err_type, visited);
        }
        if let Some((params, ret, _)) = arena.unwrap_function(type_id) {
            return params
                .iter()
                .copied()
                .any(|ty| self.type_depends_on_program_definitions_inner(ty, visited))
                || self.type_depends_on_program_definitions_inner(ret, visited);
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

        // Save/restore module bindings when compiling module code via IIFE.
        // Ensures bindings are restored even when `?` returns early.
        // A panic would skip the restore, but panics are fatal anyway.
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
                    compile_env!(self, interner, &empty_inits, source_file_ptr)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

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
                && let Some(statics) = class.statics
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

        // Save/restore module bindings when compiling module code via IIFE.
        // Ensures bindings are restored even when `?` returns early.
        // A panic would skip the restore, but panics are fatal anyway.
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
                    compile_env!(self, interner, &empty_inits, source_file_ptr)
                } else {
                    compile_env!(self, source_file_ptr)
                };
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
        use vole_sema::generic::ClassMethodMonomorphKey;
        use vole_sema::types::FunctionType;

        let arena = self.arena();

        // Step 1: Collect abstract class method templates (those with TypeParam in substitutions)
        let all_class_method_count = self
            .registry()
            .class_method_monomorph_cache
            .collect_instances()
            .len();
        tracing::debug!(
            all_class_method_count,
            "expand_abstract_class_method_monomorphs: checking cache"
        );

        let abstract_templates: Vec<(ClassMethodMonomorphKey, ClassMethodMonomorphInstance)> = self
            .registry()
            .class_method_monomorph_cache
            .instances()
            .filter(|(_, inst)| {
                inst.substitutions
                    .values()
                    .any(|&type_id| arena.unwrap_type_param(type_id).is_some())
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
        let mut class_concrete_type_args: FxHashMap<NameId, Vec<Vec<TypeId>>> =
            FxHashMap::default();

        // Collect from concrete static method monomorphs
        for (key, inst) in self.registry().static_method_monomorph_cache.instances() {
            // Skip abstract entries (TypeParam in substitutions)
            if inst
                .substitutions
                .values()
                .any(|&ty| arena.unwrap_type_param(ty).is_some())
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
                .any(|&tk| arena.contains_type_param(tk))
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
                .any(|&tk| self.type_depends_on_program_definitions(tk))
            {
                continue;
            }
            class_concrete_type_args
                .entry(key.class_name)
                .or_default()
                .push(key.class_type_keys.clone());
        }

        // Collect from concrete class method monomorphs
        for (key, inst) in self.registry().class_method_monomorph_cache.instances() {
            // Skip abstract entries
            if inst
                .substitutions
                .values()
                .any(|&ty| arena.unwrap_type_param(ty).is_some())
            {
                continue;
            }
            if key.type_keys.is_empty() {
                continue;
            }
            if key
                .type_keys
                .iter()
                .any(|&tk| arena.contains_type_param(tk))
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
            let mut seen = rustc_hash::FxHashSet::default();
            type_arg_vecs.retain(|v| seen.insert(v.clone()));
        }

        if tracing::enabled!(tracing::Level::DEBUG) {
            for (class_name, type_arg_vecs) in &class_concrete_type_args {
                let class_name_str = self.query().display_name(*class_name);
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
        let mut expanded_keys: rustc_hash::FxHashSet<ClassMethodMonomorphKey> =
            rustc_hash::FxHashSet::default();

        for (abstract_key, tmpl) in &abstract_templates {
            // Extract the TypeParam positions from the abstract type_keys.
            // These tell us which positions in the type_keys are TypeParams
            // and what their NameIds are (for building substitutions).
            let abstract_type_param_positions: Vec<(usize, NameId)> = abstract_key
                .type_keys
                .iter()
                .enumerate()
                .filter_map(|(i, &tk)| arena.unwrap_type_param(tk).map(|name| (i, name)))
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

                let concrete_type_keys: Vec<TypeId> = abstract_key
                    .type_keys
                    .iter()
                    .enumerate()
                    .map(|(i, &tk)| {
                        if arena.unwrap_type_param(tk).is_some() {
                            concrete_type_args[i]
                        } else {
                            tk
                        }
                    })
                    .collect();

                // Skip if any concrete type_keys still contain TypeParams
                if concrete_type_keys
                    .iter()
                    .any(|&tk| arena.contains_type_param(tk))
                {
                    continue;
                }

                let concrete_key = ClassMethodMonomorphKey::new(
                    abstract_key.class_name,
                    abstract_key.method_name,
                    concrete_type_keys,
                );

                // Skip if already in sema cache or already expanded
                if self
                    .registry()
                    .class_method_monomorph_cache
                    .get(&concrete_key)
                    .is_some()
                {
                    continue;
                }
                if expanded_keys.contains(&concrete_key) {
                    continue;
                }

                // Build a substitution map from TypeParam NameIds to concrete types
                // using the abstract template's substitution structure.
                let concrete_subs: FxHashMap<NameId, TypeId> = abstract_type_param_positions
                    .iter()
                    .map(|&(i, param_name)| (param_name, concrete_type_args[i]))
                    .collect();

                // Build concrete substitutions for the class method (key_name -> concrete_ty)
                let concrete_class_subs: FxHashMap<NameId, TypeId> = tmpl
                    .substitutions
                    .iter()
                    .map(|(&key_name, &value_type_id)| {
                        if let Some(param_name) = arena.unwrap_type_param(value_type_id)
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
                        arena
                            .lookup_substitute(param_ty, &concrete_class_subs)
                            .unwrap_or(param_ty)
                    })
                    .collect();
                let concrete_return = arena
                    .lookup_substitute(tmpl.func_type.return_type_id, &concrete_class_subs)
                    .unwrap_or(tmpl.func_type.return_type_id);
                let concrete_func_type = FunctionType::from_ids(
                    &concrete_params,
                    concrete_return,
                    tmpl.func_type.is_closure,
                );

                let concrete_self_type = arena
                    .lookup_substitute(tmpl.self_type, &concrete_class_subs)
                    .unwrap_or(tmpl.self_type);

                // Skip if any resolved types still contain TypeParams.
                // This catches cases where the method body references types from
                // other generic contexts that our substitution set doesn't cover.
                if concrete_params
                    .iter()
                    .any(|&p| arena.contains_type_param(p))
                    || arena.contains_type_param(concrete_return)
                    || arena.contains_type_param(concrete_self_type)
                {
                    continue;
                }

                // Generate mangled name string (no NameId needed)
                let class_name_str = self.query().display_name(tmpl.class_name);
                let method_name_str = self.query().display_name(tmpl.method_name);
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

                expanded_keys.insert(concrete_key.clone());
                expanded.push(ExpandedMethodData {
                    concrete_key,
                    mangled_name_str,
                    func_type: concrete_func_type,
                    substitutions: concrete_class_subs,
                    class_name: tmpl.class_name,
                    method_name: tmpl.method_name,
                    self_type: concrete_self_type,
                    external_info: tmpl.external_info,
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

            let method_name_str = self.query().display_name(data.method_name);
            let func_key = data.func_key.expect("func_key should be set in step 4");
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found("expanded class method", &data.mangled_name_str)
            })?;

            if self.defined_functions.contains(&func_id) {
                continue;
            }

            // Find the method body AST
            let method_ast = self
                .find_class_method_in_modules(data.class_name, &method_name_str)
                .cloned();

            let method_ast = if let Some(ast) = method_ast {
                ast
            } else {
                // Try implement block methods
                let module_id = self.analyzed.name_table().module_of(data.class_name);
                let module_path = self
                    .analyzed
                    .name_table()
                    .module_path(module_id)
                    .to_string();
                if let Some((module_program, _)) = self.analyzed.module_programs.get(&module_path) {
                    self.find_implement_block_method(
                        &module_program.declarations,
                        data.class_name,
                        &method_name_str,
                        module_id,
                    )
                    .cloned()
                    .ok_or_else(|| {
                        let class_name = self.query().display_name(data.class_name);
                        CodegenError::not_found(
                            "expanded class method",
                            format!("{} in class {}", method_name_str, class_name),
                        )
                    })?
                } else {
                    let class_name = self.query().display_name(data.class_name);
                    return Err(CodegenError::not_found(
                        "expanded class method",
                        format!("{} in class {}", method_name_str, class_name),
                    ));
                }
            };

            // Compile the method body (adapted from compile_monomorphized_class_method)
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
                let params: Vec<_> = method_ast
                    .params
                    .iter()
                    .zip(param_type_ids.iter())
                    .zip(param_cranelift_types.iter())
                    .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                    .collect();

                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    super::signatures::SelfParam::Pointer,
                );
                self.jit.ctx.func.signature = sig;

                let self_type_id = data.self_type;
                let self_sym = self.self_symbol();
                let self_binding = (self_sym, self_type_id, self.pointer_type);

                let source_file_ptr = self.source_file_ptr();
                let empty_inits = FxHashMap::default();
                let mut builder_ctx = FunctionBuilderContext::new();
                let cg_module_id = Some(module_id);
                {
                    let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                    let env = if let Some((_, interner)) =
                        self.analyzed.module_programs.get(&module_path)
                    {
                        compile_env!(self, interner, &empty_inits, source_file_ptr)
                    } else {
                        compile_env!(self, source_file_ptr)
                    };
                    let mut codegen_ctx = CodegenCtx::new(
                        &mut self.jit.module,
                        &mut self.func_registry,
                        &mut self.pending_monomorphs,
                    );

                    let config = FunctionCompileConfig::method(
                        &method_ast.body,
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
                        Some(&data.substitutions),
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
    /// `program` is `Some` when called from `compile_program_body` (needed to find
    /// main-program generic function ASTs) and `None` when called from
    /// `compile_module_functions` (all monomorphs live in modules).
    pub(super) fn compile_pending_monomorphs(
        &mut self,
        program: Option<&Program>,
    ) -> CodegenResult<()> {
        use crate::types::PendingMonomorph;

        const MAX_FIXPOINT_ITERATIONS: usize = 100;

        for iteration in 0..MAX_FIXPOINT_ITERATIONS {
            let batch = std::mem::take(&mut self.pending_monomorphs);
            if batch.is_empty() {
                tracing::debug!(
                    iterations = iteration,
                    "compile_pending_monomorphs: fixpoint reached"
                );
                return Ok(());
            }

            tracing::debug!(
                iteration,
                count = batch.len(),
                "compile_pending_monomorphs: compiling batch"
            );

            for pending in batch {
                match pending {
                    PendingMonomorph::Function(instance) => {
                        self.compile_pending_function(&instance, program)?;
                    }
                    PendingMonomorph::ClassMethod(instance) => {
                        self.compile_pending_class_method(&instance, program)?;
                    }
                    PendingMonomorph::StaticMethod(instance) => {
                        self.compile_pending_static_method(&instance, program)?;
                    }
                }
            }
        }

        Err(CodegenError::internal(
            "pending monomorph fixpoint loop exceeded 100 iterations",
        ))
    }

    /// Compile a single pending free-function monomorph.
    fn compile_pending_function(
        &mut self,
        instance: &MonomorphInstance,
        program: Option<&Program>,
    ) -> CodegenResult<()> {
        // Skip external functions
        if self.is_external_func(instance.original_name) {
            return Ok(());
        }

        // Try main program generic functions first
        if let Some(program) = program {
            let mut generic_func_asts: FxHashMap<NameId, &FuncDecl> = FxHashMap::default();
            let program_module = self.program_module();
            self.collect_generic_func_asts(
                &program.declarations,
                program_module,
                &mut generic_func_asts,
            );
            if let Some(func) = generic_func_asts.get(&instance.original_name) {
                self.compile_monomorphized_function(func, instance)?;
                return Ok(());
            }
        }

        // Fallback: search module programs
        let found = self.compile_monomorphized_module_function(instance)?;
        if !found {
            let func_name = self.query().display_name(instance.original_name);
            return Err(CodegenError::internal_with_context(
                "pending monomorph: generic function AST not found",
                func_name,
            ));
        }
        Ok(())
    }

    /// Compile a single pending class method monomorph.
    fn compile_pending_class_method(
        &mut self,
        instance: &ClassMethodMonomorphInstance,
        program: Option<&Program>,
    ) -> CodegenResult<()> {
        // Skip external and abstract instances
        if instance.external_info.is_some() {
            return Ok(());
        }
        if self.is_abstract_class_method_monomorph(instance) {
            return Ok(());
        }

        let method_name_str = self.query().display_name(instance.method_name);

        // Try main program class ASTs
        if let Some(program) = program {
            let class_asts = self.build_generic_type_asts(program);
            if let Some(class) = class_asts.get(&instance.class_name) {
                let method = class
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_class_method(method, instance, None)?;
                    return Ok(());
                }
            }

            // Try implement blocks in the main program
            let program_module = self.program_module();
            if let Some(method) = self.find_implement_block_method(
                &program.declarations,
                instance.class_name,
                &method_name_str,
                program_module,
            ) {
                self.compile_monomorphized_class_method(method, instance, None)?;
                return Ok(());
            }
        }

        // Fallback: search module programs for class methods
        if let Some(method) = self
            .find_class_method_in_modules(instance.class_name, &method_name_str)
            .cloned()
        {
            let module_id = self.analyzed.name_table().module_of(instance.class_name);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            self.compile_monomorphized_class_method(&method, instance, Some(&module_path))?;
            return Ok(());
        }

        // Fallback: search implement blocks in modules
        let module_id = self.analyzed.name_table().module_of(instance.class_name);
        let module_path = self
            .analyzed
            .name_table()
            .module_path(module_id)
            .to_string();
        if let Some((module_program, _)) = self.analyzed.module_programs.get(&module_path)
            && let Some(method) = self
                .find_implement_block_method(
                    &module_program.declarations,
                    instance.class_name,
                    &method_name_str,
                    module_id,
                )
                .cloned()
            {
                self.compile_monomorphized_class_method(&method, instance, Some(&module_path))?;
                return Ok(());
            }

        let class_name = self.query().display_name(instance.class_name);
        Err(CodegenError::not_found(
            "pending monomorph: class method",
            format!("{} in class {}", method_name_str, class_name),
        ))
    }

    /// Compile a single pending static method monomorph.
    fn compile_pending_static_method(
        &mut self,
        instance: &StaticMethodMonomorphInstance,
        program: Option<&Program>,
    ) -> CodegenResult<()> {
        if self.is_abstract_static_method_monomorph(instance) {
            return Ok(());
        }

        let method_name_str = self.query().display_name(instance.method_name);

        // Try main program class ASTs
        if let Some(program) = program {
            let class_asts = self.build_generic_type_asts(program);
            if let Some(class) = class_asts.get(&instance.class_name)
                && let Some(statics) = class.statics
            {
                let method = statics
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_static_method(method, instance, None)?;
                    return Ok(());
                }
            }
        }

        // Fallback: search module programs
        if let Some(method) = self
            .find_static_method_in_modules(instance.class_name, &method_name_str)
            .cloned()
        {
            let module_id = self.analyzed.name_table().module_of(instance.class_name);
            let module_path = self
                .analyzed
                .name_table()
                .module_path(module_id)
                .to_string();
            self.compile_monomorphized_static_method(&method, instance, Some(&module_path))?;
            return Ok(());
        }

        let class_name = self.query().display_name(instance.class_name);
        Err(CodegenError::not_found(
            "pending monomorph: static method",
            format!("{} in class {}", method_name_str, class_name),
        ))
    }
}
