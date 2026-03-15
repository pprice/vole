use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use cranelift_module::Module;

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::{Compiler, DeclareMode};

use crate::FunctionKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CodegenCtx;
use vole_identity::{Interner, NameId, Symbol, TypeId, VirTypeId};
use vole_log::compile_timing;
use vole_vir::calls::CallTarget;
use vole_vir::expr::{VirExpr, VirMetaKind, VirPattern, VirStringPart};
use vole_vir::func::VirBody;
use vole_vir::refs::VirRef;
use vole_vir::stmt::VirStmt;

impl Compiler<'_> {
    pub(super) fn test_function_key(&mut self, test_index: usize) -> FunctionKey {
        if let Some(func_key) = self.test_func_keys.get(test_index).copied() {
            return func_key;
        }

        let func_key = self.func_registry.intern_test(test_index);
        if self.test_func_keys.len() == test_index {
            self.test_func_keys.push(func_key);
        } else if self.test_func_keys.len() < test_index {
            self.test_func_keys.resize(test_index + 1, func_key);
        } else {
            self.test_func_keys[test_index] = func_key;
        }
        func_key
    }

    pub(super) fn test_display_name(&self, func_key: FunctionKey) -> String {
        self.func_registry.display(func_key)
    }

    /// Register global module bindings from VirProgram's pre-resolved module bindings.
    ///
    /// Reads `module_bindings` from VirProgram (populated during VIR lowering)
    /// and registers them in `global_module_bindings` for use during compilation.
    pub(super) fn register_global_module_bindings(&mut self) {
        let vir = self.analyzed;
        for (&binding_sym, &(module_id, export_name, vir_export_ty)) in &vir.module_bindings {
            self.global_module_bindings
                .insert(binding_sym, (module_id, export_name, vir_export_ty));
        }
    }

    /// Extract destructured import bindings for a module from VirProgram.
    ///
    /// Reads pre-resolved bindings from `module_module_bindings` in VirProgram
    /// (populated during VIR lowering). Returns a list of `(local_symbol, binding)`
    /// pairs that should be inserted into `global_module_bindings` before compiling
    /// the module's function bodies.
    fn extract_module_destructured_bindings(
        &self,
        module_path: &str,
    ) -> Vec<(Symbol, super::ModuleExportBinding)> {
        let vir = self.analyzed;
        let Some(module_bindings) = vir.module_module_bindings.get(module_path) else {
            return Vec::new();
        };
        module_bindings
            .iter()
            .map(|(&binding_sym, &binding)| (binding_sym, binding))
            .collect()
    }

    /// Compile a complete program
    pub fn compile_program(&mut self) -> CodegenResult<()> {
        // Bail early if any modules had sema errors - their VIR may be missing
        // and compiling their function bodies would panic.
        if !self.analyzed.modules_with_errors.is_empty() {
            let module_list: Vec<_> = self.analyzed.modules_with_errors.iter().cloned().collect();
            return Err(CodegenError::internal_with_context(
                "module(s) with type errors",
                module_list.join(", "),
            ));
        }
        // Compile module functions first (before main program)
        self.compile_module_functions(None)?;
        self.compile_program_body()
    }

    /// Compile only module functions (prelude, imports).
    /// Call this once before compile_program_only for batched compilation.
    pub fn compile_modules_only(&mut self) -> CodegenResult<()> {
        // Bail early if any modules had sema errors - their expression data may
        // contain INVALID type IDs that would cause panics in codegen.
        if !self.analyzed.modules_with_errors.is_empty() {
            let module_list: Vec<_> = self.analyzed.modules_with_errors.iter().cloned().collect();
            return Err(CodegenError::internal_with_context(
                "module(s) with type errors",
                module_list.join(", "),
            ));
        }
        self.compile_module_functions(None)
    }

    /// Compile only the modules not in `skip_modules`.
    ///
    /// Pass 1 (declarations) runs for ALL modules so cross-module references
    /// resolve. Pass 2 (body compilation) skips modules already present in
    /// `skip_modules`, avoiding redundant Cranelift IR work.
    pub fn compile_modules_only_incremental(
        &mut self,
        skip_modules: &HashSet<String>,
    ) -> CodegenResult<()> {
        if !self.analyzed.modules_with_errors.is_empty() {
            let module_list: Vec<_> = self.analyzed.modules_with_errors.iter().cloned().collect();
            return Err(CodegenError::internal_with_context(
                "module(s) with type errors",
                module_list.join(", "),
            ));
        }
        self.compile_module_functions(Some(skip_modules))
    }

    /// Compile a single module's function bodies during lazy compilation.
    ///
    /// This is the per-module counterpart of `compile_modules_only()`. When
    /// `compile_trigger(module_idx)` fires, only the triggered module needs
    /// its bodies compiled.
    ///
    /// # Passes
    ///
    /// - **Pass 1** (declarations): always runs for ALL modules so cross-module
    ///   references resolve. Declarations are idempotent on JitContext.
    /// - **Passes 1.5a–1.8** (global passes): run on `first_trigger` only.
    ///   Subsequent triggers skip them because the bodies they compile are
    ///   already in the overflow JitContext (guarded by `defined_functions`).
    /// - **Pass 2** (body compilation): runs ONLY for `target_module`.
    /// - **Pending monomorphs**: drained after body compilation.
    pub fn compile_single_module_lazy(
        &mut self,
        target_module: &str,
        _first_trigger: bool,
    ) -> CodegenResult<()> {
        // Bail early if any modules had sema errors.
        if !self.analyzed.modules_with_errors.is_empty() {
            let module_list: Vec<_> = self.analyzed.modules_with_errors.iter().cloned().collect();
            return Err(CodegenError::internal_with_context(
                "module(s) with type errors",
                module_list.join(", "),
            ));
        }

        // Pre-populate defined_functions from the overflow JitContext so that
        // re-running declaration/compilation passes correctly skips functions
        // that were compiled by previous triggers.
        self.init_defined_from_jit();

        let module_paths = self.analyzed.module_paths();

        // Pass 0: Pre-declare external function imports (idempotent).
        self.declare_external_imports();

        // Pass 1: Declare types and functions for all modules.
        //
        // Target module: Export linkage (will be defined).
        // Other modules: Import linkage (resolved via stub symbols registered
        // in the overflow JitContext's symbol table from the main JitContext).
        //
        // On subsequent triggers, functions previously compiled (now in
        // defined_func_ids) are redeclared — Cranelift returns the existing
        // FuncId, and the function is already defined, so linkage is irrelevant.
        let target_paths: Vec<String> = vec![target_module.to_string()];
        let other_paths: Vec<String> = module_paths
            .iter()
            .filter(|p| p.as_str() != target_module)
            .cloned()
            .collect();

        // Declare target module with Export linkage (bodies will be compiled).
        self.declare_module_types_and_functions(&target_paths)?;
        // Import other modules with Import linkage (resolved via stub symbols).
        self.import_module_types_and_functions(&other_paths)?;

        // Global passes: array Iterable defaults, monomorphs, VIR monomorphs,
        // abstract class method expansion, monomorph index. Run on every trigger
        // because each creates a fresh Compiler with empty CodegenState — the
        // method_func_keys / array_iterable_func_keys registrations from earlier
        // triggers are lost. finalize_function() guards against re-defining
        // function bodies that were already compiled on previous triggers.
        self.compile_array_iterable_default_methods()?;
        self.declare_all_monomorphized_instances()?;
        self.declare_vir_monomorphized_functions()?;
        self.expand_abstract_class_method_monomorphs()?;
        self.build_monomorph_index();
        // VIR first (~17x cheaper), then AST fallback for remaining monomorphs.
        self.compile_vir_monomorphized_functions_phased(false)?;
        self.compile_all_monomorphized_instances(false)?;

        // Pass 2: Compile function bodies ONLY for the target module.
        self.compile_module_function_bodies(target_module)?;

        // Compile any monomorphs lazily declared during the target module's
        // body compilation.
        self.compile_pending_monomorphs()?;

        tracing::debug!(target_module, "compile_single_module_lazy complete");
        Ok(())
    }

    /// Import pre-compiled module functions without compiling them.
    /// Use this when modules were already compiled in a shared CompiledModules cache.
    pub fn import_modules(&mut self) -> CodegenResult<()> {
        self.import_module_functions()
    }

    /// Compile a program without recompiling module functions.
    /// Use with compile_modules_only for batched compilation.
    pub fn compile_program_only(&mut self) -> CodegenResult<()> {
        self.compile_program_body()
    }

    /// Pre-declare all external function imports from `VirProgram.external_imports`.
    ///
    /// For each external function declared in `external("module:path") { ... }` blocks,
    /// looks up the native function in the runtime's `NativeRegistry`, builds a
    /// Cranelift signature, and declares it as an import in the JIT module.
    ///
    /// This runs before any function compilation (VIR or AST) so that native
    /// imports are available for direct calls. Idempotent: Cranelift returns
    /// existing `FuncId`s on re-declaration.
    fn declare_external_imports(&mut self) {
        use cranelift::prelude::AbiParam;
        use vole_runtime::native_registry::NativeType;

        let ptr_type = self.pointer_type;
        for import in &self.analyzed.external_imports {
            let Some(native_func) = self
                .state
                .native_registry
                .lookup(&import.module_path, &import.func_name)
            else {
                continue;
            };

            // Look up the JIT symbol name from the function pointer.
            let Some(symbol_name) = self.state.ptr_to_symbol.get(&(native_func.ptr as usize))
            else {
                continue;
            };

            // Build the Cranelift signature from the native function's signature.
            let mut sig = self.jit.module.make_signature();
            for param_type in &native_func.signature.params {
                sig.params
                    .push(AbiParam::new(crate::types::native_type_to_cranelift(
                        param_type, ptr_type,
                    )));
            }
            if native_func.signature.return_type != NativeType::Nil {
                sig.returns
                    .push(AbiParam::new(crate::types::native_type_to_cranelift(
                        &native_func.signature.return_type,
                        ptr_type,
                    )));
            }

            // Declare the function as an import in the JIT module.
            // This is idempotent — returns existing FuncId if already declared.
            let _ = self.jit.module.declare_function(
                symbol_name,
                cranelift_module::Linkage::Import,
                &sig,
            );
        }
    }

    /// First pass: declare all functions and tests, collect globals, finalize type metadata.
    ///
    /// Iterates VirEntityMetadata instead of walking AST `program.declarations`.
    fn declare_program_declarations(&mut self) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        // Bulk-register top-level module import bindings from VirProgram.
        self.register_global_module_bindings();

        let program_module = self.program_module();

        // Declare non-generic, non-external functions from VirEntityMetadata.
        // This covers both top-level and test-scoped functions (both are
        // registered under program_module by sema).
        //
        // Dedup by NameId: when the same source file is both imported as a
        // module and compiled as the main program (common in test-runner batch
        // mode), VirEntityMetadata may contain duplicate FunctionDefs with
        // different FunctionIds but the same NameId.  Deduplicating matches
        // the old AST-walk behavior where each Decl::Function appeared once.
        let mut seen = HashSet::new();
        let func_defs: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_function_defs(program_module)
            .into_iter()
            .filter(|fd| !fd.is_generic && !fd.is_external)
            .filter_map(|fd| seen.insert(fd.name_id).then_some(fd.name_id))
            .collect();
        for name_id in func_defs {
            // Use the bare (last-segment) name for main-program functions so
            // the JIT key matches what `get_function_ptr("main")` looks up.
            // Module functions use the fully-qualified display_name instead.
            let bare_name = self
                .analyzed
                .last_segment(name_id)
                .unwrap_or_else(|| self.analyzed.display_name(name_id));
            let func_key =
                self.declare_function_by_name_id(name_id, &bare_name, DeclareMode::Declare);
            // If this is a generator, override the return type to
            // RuntimeIterator(T) so callers compiled before the
            // generator itself use the correct (non-interface) type.
            if let Some(func_key) = func_key {
                self.override_generator_return_type(name_id, func_key);
            }
        }

        // Finalize classes in the main program module.
        let class_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_type_defs_by_kind(program_module, VirTypeDefKind::Class)
            .into_iter()
            .map(|td| td.id)
            .collect();
        for type_def_id in class_ids {
            self.finalize_type_by_id(type_def_id)?;
        }

        // Finalize structs in the main program module.
        let struct_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_type_defs_by_kind(program_module, VirTypeDefKind::Struct)
            .into_iter()
            .map(|td| td.id)
            .collect();
        for type_def_id in struct_ids {
            self.finalize_type_by_id(type_def_id)?;
        }

        // Finalize test-scoped classes (registered under virtual test modules).
        if !self.skip_tests {
            let virtual_module_ids = self.analyzed.tests_virtual_module_ids();
            for vm_id in virtual_module_ids {
                let class_ids: Vec<_> = self
                    .analyzed
                    .entity_metadata
                    .module_type_defs_by_kind(vm_id, VirTypeDefKind::Class)
                    .into_iter()
                    .map(|td| td.id)
                    .collect();
                for type_def_id in class_ids {
                    self.finalize_module_type_by_id(type_def_id, DeclareMode::Declare)?;
                }
            }
        }

        // Register implement block methods from VIR metadata (pass 1).
        let impl_blocks = self.analyzed.entity_metadata.implement_blocks();
        for entry in impl_blocks {
            self.register_implement_block(entry)?;
        }

        // Declare all test functions from VirProgram's flat test list.
        // This uses VirProgram.tests order (outer tests first, then nested),
        // matching the order used during compilation in compile_all_tests.
        if !self.skip_tests {
            let num_tests = self.analyzed.tests.len();
            let i64_type_id = TypeId::I64;
            for test_index in 0..num_tests {
                let func_key = self.test_function_key(test_index);
                let func_name = self.test_display_name(func_key);
                let sig = self.jit.create_signature(&[], Some(types::I64));
                let func_id = self.jit.declare_function(&func_name, &sig);
                self.func_registry.set_return_type(func_key, i64_type_id);
                self.func_registry.set_func_id(func_key, func_id);
            }
        }

        Ok(())
    }

    /// If `func` is a generator (sema marked it with `generator_element_type`),
    /// override its declared return type to `RuntimeIterator(T)`.
    ///
    /// Called during pass 1 so that any function compiled in pass 2 that calls
    /// this generator sees the correct (non-interface) return type.
    fn override_generator_return_type(&mut self, name_id: NameId, func_key: FunctionKey) {
        let elem_type_id = {
            let func_id = match self.analyzed.function_id_by_name_id(name_id) {
                Some(id) => id,
                None => return,
            };
            match self
                .analyzed
                .function_def(func_id)
                .sema_generator_element_type
            {
                Some(e) => e,
                None => return,
            }
        };

        if let Some(runtime_iter_type_id) = self.vir_query_lookup_runtime_iterator(elem_type_id) {
            self.func_registry
                .set_return_type(func_key, runtime_iter_type_id);
        }
    }

    /// Second pass: compile function bodies and tests.
    ///
    /// Iterates VirEntityMetadata instead of walking AST `program.declarations`.
    /// Decl::Let globals are handled by inlining their initializers when
    /// referenced (see compile_expr for ExprKind::Identifier).
    fn compile_program_declarations(&mut self) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        let program_module = self.program_module();

        // Compile non-generic, non-external function bodies from VirEntityMetadata.
        // This covers both top-level and test-scoped functions (both are
        // registered under program_module by sema).
        // Dedup by NameId (see declare_program_declarations for rationale).
        let mut seen = HashSet::new();
        let func_name_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_function_defs(program_module)
            .into_iter()
            .filter(|fd| !fd.is_generic && !fd.is_external)
            .filter_map(|fd| seen.insert(fd.name_id).then_some(fd.name_id))
            .collect();
        for name_id in func_name_ids {
            self.compile_main_function_by_name_id(name_id)?;
        }

        // Compile class methods in the main program module.
        let class_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_type_defs_by_kind(program_module, VirTypeDefKind::Class)
            .into_iter()
            .map(|td| td.id)
            .collect();
        for type_def_id in class_ids {
            self.compile_type_methods_by_id(type_def_id, program_module)?;
        }

        // Compile struct methods in the main program module.
        let struct_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_type_defs_by_kind(program_module, VirTypeDefKind::Struct)
            .into_iter()
            .map(|td| td.id)
            .collect();
        for type_def_id in struct_ids {
            self.compile_type_methods_by_id(type_def_id, program_module)?;
        }

        // Compile test-scoped class methods (registered under virtual test modules).
        if !self.skip_tests {
            let virtual_module_ids = self.analyzed.tests_virtual_module_ids();
            for vm_id in virtual_module_ids {
                let class_ids: Vec<_> = self
                    .analyzed
                    .entity_metadata
                    .module_type_defs_by_kind(vm_id, VirTypeDefKind::Class)
                    .into_iter()
                    .map(|td| td.id)
                    .collect();
                for type_def_id in class_ids {
                    self.compile_type_methods_by_id(type_def_id, vm_id)?;
                }
            }
        }

        // Compile implement block methods from VIR metadata (pass 2).
        for entry in self.analyzed.entity_metadata.implement_blocks().to_vec() {
            self.compile_implement_block(&entry)?;
        }

        // Compile all test bodies from VirProgram's flat test list.
        // This must happen after scoped declarations are compiled above,
        // since test bodies may reference scoped functions/classes/impls.
        if !self.skip_tests {
            let vir_tests = &self.analyzed.tests;
            // Clone the tests slice to avoid borrowing self.analyzed during compilation.
            let vir_tests: Vec<_> = vir_tests.clone();
            self.compile_all_tests(&vir_tests)?;
        }

        Ok(())
    }

    /// Compile the main program body (functions, tests, classes, etc.)
    fn compile_program_body(&mut self) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        // Pre-declare all external function imports from VirProgram.
        // Idempotent: JIT returns existing FuncIds on re-declaration.
        {
            let _timing = compile_timing!(DEBUG, "declare_external_imports").entered();
            self.declare_external_imports();
        }

        // Pre-pass: Register all type names from VirEntityMetadata so they're
        // available for field type resolution (classes can reference each other).
        let program_module = self.program_module();
        let type_kinds = [
            VirTypeDefKind::Class,
            VirTypeDefKind::Struct,
            VirTypeDefKind::Sentinel,
        ];
        for kind in &type_kinds {
            let type_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(program_module, *kind)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in type_ids {
                self.pre_register_type_by_id(type_def_id)?;
            }
        }

        // First pass: declare all functions and tests, collect globals, finalize type metadata
        {
            let _timing = compile_timing!(DEBUG, "declare_program_declarations").entered();
            self.declare_program_declarations()?;
        }

        // Declare monomorphized function instances before second pass
        {
            let _timing = compile_timing!(DEBUG, "declare_all_monomorphized_instances").entered();
            self.declare_all_monomorphized_instances()?;
        }

        // Declare VIR-monomorphized functions (produced by run_vir_monomorphize).
        self.declare_vir_monomorphized_functions()?;

        // Expand abstract class method templates for program-level generics.
        // MUST run after declarations (which provide concrete substitutions) but
        // before any body compilation (which may call expanded methods).
        {
            let _timing =
                compile_timing!(DEBUG, "expand_abstract_class_method_monomorphs").entered();
            self.expand_abstract_class_method_monomorphs()?;
        }

        // Compile array Iterable default methods for program-level element types.
        // Module-level types already have methods from the module cache (imported
        // via import_array_iterable_default_methods); the sentinel check inside
        // compile_array_iterable_default_methods skips those.
        {
            let _timing = compile_timing!(DEBUG, "compile_array_iterable_defaults").entered();
            self.compile_array_iterable_default_methods()?;
        }

        // Build monomorph name index for O(1) lookup during body compilation.
        // Must run after declare_all + expand_abstract so all instances are visible.
        {
            let _timing = compile_timing!(DEBUG, "build_monomorph_index").entered();
            self.build_monomorph_index();
        }

        // Second pass: compile function bodies and tests
        {
            let _timing = compile_timing!(DEBUG, "compile_program_declarations").entered();
            self.compile_program_declarations()?;
        }

        // Compile VIR-monomorphized function bodies first — VIR compilation is
        // ~17x cheaper than AST fallback (18ms vs 293ms at full load). The
        // defined_functions guard prevents double-compilation of any function.
        // Functions with free_monomorphs entries are skipped here (their
        // CallTarget::Native Symbols may reference the module interner) and
        // handled correctly by compile_all_monomorphized_instances below.
        {
            let _timing = compile_timing!(DEBUG, "compile_vir_monomorphized_functions").entered();
            self.compile_vir_monomorphized_functions()?;
        }

        // AST fallback: compile monomorphized instances that lack VIR versions
        // (~8% of monomorphs). Only handles instances not already compiled above.
        {
            let _timing = compile_timing!(DEBUG, "compile_monomorphized_instances").entered();
            self.compile_all_monomorphized_instances(true)?;
        }

        // Compile any monomorphs that were lazily declared during expression compilation.
        // This fixpoint loop handles transitive demand-declarations: compiling one pending
        // monomorph body may trigger demand-declaration of another.
        {
            let _timing = compile_timing!(DEBUG, "compile_pending_monomorphs").entered();
            self.compile_pending_monomorphs()?;
        }

        Ok(())
    }

    /// Compile pure Vole functions from imported modules.
    /// These are functions defined in module files (not external FFI functions).
    /// Declare all module functions, finalize types, and register implement blocks.
    /// Must run before compiling function bodies so cross-module calls can be resolved.
    ///
    /// Iterates VirEntityMetadata (function_defs, type_defs) instead of walking
    /// AST module programs.
    fn declare_module_types_and_functions(&mut self, module_paths: &[String]) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        for module_path in module_paths {
            tracing::debug!(module_path, "compile_module_functions: declaring functions");
            let module_id = self.analyzed.module_id_or_main(module_path);

            // Declare pure Vole functions from VirEntityMetadata.
            // Skip generic functions (declared via monomorphized instances) and
            // external functions (declared via implement block / FFI path).
            let func_defs: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_function_defs(module_id)
                .into_iter()
                .filter(|fd| !fd.is_generic && !fd.is_external)
                .map(|fd| fd.name_id)
                .collect();
            for name_id in func_defs {
                let display_name = self.analyzed.display_name(name_id);
                self.declare_function_by_name_id(name_id, &display_name, DeclareMode::Declare);
            }

            // Finalize module classes (register type metadata, declare methods)
            // MUST happen before implement block registration, which needs type_metadata
            let class_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in class_ids {
                self.finalize_module_type_by_id(type_def_id, DeclareMode::Declare)?;
            }

            // Finalize module structs (register type metadata, declare methods)
            let struct_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in struct_ids {
                self.finalize_module_type_by_id(type_def_id, DeclareMode::Declare)?;
            }

            // Register module sentinels (zero-field struct types like Done, nil)
            let sentinel_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Sentinel)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in sentinel_ids {
                self.finalize_module_sentinel_by_id(type_def_id)?;
            }

            // Register implement block methods from VIR metadata
            // MUST happen after class finalization so type_metadata is populated
            let entries = self
                .analyzed
                .entity_metadata
                .module_implement_blocks(module_path)
                .to_vec();
            for entry in &entries {
                // The interner_override parameter is unused in the inner implementation,
                // so we can use register_implement_block directly.
                self.register_implement_block(entry)?;
            }
        }

        Ok(())
    }

    /// Declare types and import functions for modules using Import linkage.
    ///
    /// Used by `compile_single_module_lazy` for non-target modules. Functions
    /// are declared with Import linkage so Cranelift resolves them via the
    /// overflow JitContext's symbol table (stub pointers from the main JitContext).
    /// Type finalization and implement block registration are identical to the
    /// Export path since they only produce metadata, not linkage-sensitive code.
    fn import_module_types_and_functions(&mut self, module_paths: &[String]) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        for module_path in module_paths {
            tracing::debug!(module_path, "lazy: importing module types and functions");
            let module_id = self.analyzed.module_id_or_main(module_path);

            // Import functions with Import linkage (resolved via symbol table).
            let func_defs: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_function_defs(module_id)
                .into_iter()
                .filter(|fd| !fd.is_generic && !fd.is_external)
                .map(|fd| fd.name_id)
                .collect();
            for name_id in func_defs {
                let display_name = self.analyzed.display_name(name_id);
                let func_key =
                    self.declare_function_by_name_id(name_id, &display_name, DeclareMode::Import);
                // Override generator return types for imported module functions
                if let Some(func_key) = func_key {
                    self.override_generator_return_type(name_id, func_key);
                }
            }

            // Finalize module classes (register type metadata, import methods)
            let class_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in class_ids {
                self.finalize_module_type_by_id(type_def_id, DeclareMode::Import)?;
            }

            // Finalize module structs (register type metadata, import methods)
            let struct_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in struct_ids {
                self.finalize_module_type_by_id(type_def_id, DeclareMode::Import)?;
            }

            // Register module sentinels
            let sentinel_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Sentinel)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in sentinel_ids {
                self.finalize_module_sentinel_by_id(type_def_id)?;
            }

            // Import implement block methods with Import linkage
            let entries = self
                .analyzed
                .entity_metadata
                .module_implement_blocks(module_path)
                .to_vec();
            for entry in &entries {
                self.import_module_implement_block(entry)?;
            }
        }

        // Import array Iterable default methods so array_iterable_func_keys is
        // populated and the sentinel skip in compile_array_iterable_default_methods
        // can fire, avoiding redundant recompilation per element type.
        self.import_array_iterable_default_methods()?;

        Ok(())
    }

    pub(super) fn compile_module_functions(
        &mut self,
        skip_modules: Option<&HashSet<String>>,
    ) -> CodegenResult<()> {
        // Collect module paths first to avoid borrow issues
        let module_paths = self.analyzed.module_paths();
        tracing::debug!(
            ?module_paths,
            skip_count = skip_modules.map_or(0, |s| s.len()),
            "compile_module_functions: processing module paths"
        );

        // Pass 0: Pre-declare all external function imports from VirProgram.
        // This ensures native function imports are available in the JIT module
        // before any compilation (VIR or AST) begins.
        self.declare_external_imports();

        // Pass 1: Declare functions and finalize types across all modules.
        // Modules in skip_modules use Import linkage (resolved from pre-compiled
        // symbols); new modules use Export linkage (bodies will be compiled here).
        if let Some(skip) = skip_modules {
            let new_paths: Vec<String> = module_paths
                .iter()
                .filter(|p| !skip.contains(*p))
                .cloned()
                .collect();
            let cached_paths: Vec<String> = module_paths
                .iter()
                .filter(|p| skip.contains(*p))
                .cloned()
                .collect();
            // Import cached modules (Import linkage — resolved from pre-compiled symbols)
            self.import_module_types_and_functions(&cached_paths)?;
            // Declare new modules (Export linkage — bodies will be compiled)
            self.declare_module_types_and_functions(&new_paths)?;
        } else {
            self.declare_module_types_and_functions(&module_paths)?;
        }

        // Pass 1.5a: Declare and compile array Iterable default methods for each concrete
        // element type (e.g. count/map/filter on [i64], [string], etc.).
        self.compile_array_iterable_default_methods()?;

        // Pass 1.5: Declare all monomorphized instances (functions, class methods,
        // static methods). This pre-declares known monomorphs so they have FuncIds
        // before any body compilation begins. Instances whose ASTs live in the main
        // program are declared but not compiled here — the program phase or the
        // demand-driven fixpoint loop handles them.
        self.declare_all_monomorphized_instances()?;

        // Pass 1.5b: Declare VIR-monomorphized functions (produced by
        // run_vir_monomorphize).  Module function bodies may contain
        // CallTarget::VirDirect references to these monomorphized functions
        // (e.g., a concrete module function calling a generic function like
        // wrap<string>).  Without declaring them here, compile_module_function_bodies
        // would fail with "VirDirect function not found".
        self.declare_vir_monomorphized_functions()?;

        // Pass 1.6: Expand abstract class method templates into concrete instances.
        // Abstract templates are created by sema when generic code (e.g. Task.stream<T>)
        // calls instance methods on generic classes (e.g. Channel<T>.close()).
        // This MUST run before monomorph body compilation because compiled bodies
        // (e.g. Task.stream<i64>) may call these expanded methods (e.g. ch.close()).
        self.expand_abstract_class_method_monomorphs()?;

        // Build monomorph name index for O(1) lookup during body compilation.
        // Must run after declare_all + expand_abstract so all instances are visible.
        self.build_monomorph_index();

        // Pass 1.7: Compile VIR-monomorphized function bodies first — VIR
        // compilation is ~17x cheaper than AST fallback. These are the concrete
        // functions produced by VIR monomorphization (e.g., wrap<string>,
        // wrap<i64>). The defined_functions guard prevents double-compilation.
        // Functions with free_monomorphs entries are skipped (their
        // CallTarget::Native Symbols may reference the module interner) and
        // handled by compile_all_monomorphized_instances below.
        // Passes false for is_program_phase — functions from the main program are
        // skipped and compiled later in compile_program_body.
        self.compile_vir_monomorphized_functions_phased(false)?;

        // Pass 1.8: AST fallback — compile monomorphized instances that lack VIR
        // versions (~8% of monomorphs). Passes false for is_program_phase —
        // instances from the main program are silently skipped and compiled later
        // in compile_program_body.
        self.compile_all_monomorphized_instances(false)?;

        // Pass 2: Compile function bodies (cross-module calls now resolved).
        // When lazy_modules is enabled, skip body compilation — functions are declared
        // with signatures but compiled on demand later.
        // When skip_modules is provided, skip body compilation for modules already
        // in the CompiledModules cache — only new modules need their bodies built.
        if !self.jit.lazy_modules {
            for module_path in &module_paths {
                if skip_modules.is_some_and(|skip| skip.contains(module_path)) {
                    tracing::debug!(module_path, "skipping already-compiled module");
                    continue;
                }
                self.compile_module_function_bodies(module_path)?;
            }

            // Compile any monomorphs that were lazily declared during module body compilation.
            // No main-program AST is available here; all pending monomorphs should originate
            // from module code.
            self.compile_pending_monomorphs()?;
        } else {
            // Lazy mode: generate CLIF stubs for declared-but-not-defined module functions.
            self.generate_lazy_stubs(&module_paths)?;
        }

        tracing::debug!("compile_module_functions complete");
        Ok(())
    }

    /// Generate CLIF stub functions for all declared-but-not-defined module functions.
    ///
    /// When `lazy_modules=true`, Phase 2 is skipped. This method creates a dispatch
    /// table mapping module functions to pointer slots and compiled flags, then
    /// generates a small Cranelift stub for each function that:
    /// 1. Checks the compiled flag
    /// 2. Calls `compile_trigger(module_id)` if not compiled
    /// 3. Loads the real function pointer from the dispatch table
    /// 4. Tail-calls it via `call_indirect`
    fn generate_lazy_stubs(&mut self, module_paths: &[String]) -> CodegenResult<()> {
        use super::lazy::{LazyDispatchTable, generate_lazy_stub};
        use vole_vir::entity_metadata::VirTypeDefKind;

        tracing::debug!("generate_lazy_stubs: building dispatch table");

        // Build the dispatch table by iterating module functions that were
        // declared (in func_ids) but not defined (not in defined_functions).
        let mut table = LazyDispatchTable::new();

        // Collect (func_idx, func_id, display_name) for each declared-but-not-defined
        // module function. Covers top-level functions, class/struct methods (instance
        // and static), implement block methods, and interface default methods.
        let mut stub_entries: Vec<(usize, cranelift_module::FuncId, String)> = Vec::new();

        // Helper: try to register a FuncId as a stub entry if it's declared but not defined.
        // Uses a macro because we need mutable access to table and stub_entries while
        // borrowing self immutably for display_name lookup.
        macro_rules! try_register_stub {
            ($func_id:expr, $display_name:expr, $module_idx:expr) => {
                let func_id = $func_id;
                if !self.defined_functions.contains(&func_id) {
                    // Skip if already registered in the dispatch table (e.g. method
                    // appears in both type_def.methods and implement_block.instance_methods)
                    if !table.func_index.contains_key(&func_id) {
                        let func_idx = table.register_function(func_id, $module_idx);
                        stub_entries.push((func_idx, func_id, $display_name));
                    }
                }
            };
        }

        for module_path in module_paths {
            let module_id = self.analyzed.module_id_or_main(module_path);
            let module_idx = table.register_module(module_path);

            // --- Top-level module functions ---
            // Find non-generic, non-external functions in this module
            let func_defs: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_function_defs(module_id)
                .into_iter()
                .filter(|fd| !fd.is_generic && !fd.is_external)
                .map(|fd| fd.name_id)
                .collect();

            for name_id in func_defs {
                let display_name = self.analyzed.display_name(name_id);

                // Look up the FuncId that was declared in Phase 1
                let Some(&func_id) = self.jit.func_ids.get(&display_name) else {
                    continue;
                };

                // Skip functions that are already defined (e.g. array iterable defaults)
                try_register_stub!(func_id, display_name, module_idx);
            }

            // --- Class instance and static methods ---
            // Use has_type_params() (not is_generic) to match finalize_module_type_by_id's
            // filter: generic types are compiled via monomorphized instances, not directly.
            let class_type_defs: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
                .into_iter()
                .filter(|td| {
                    !td.has_type_params()
                        && (!td.methods.is_empty() || !td.static_methods.is_empty())
                })
                .map(|td| (td.methods.clone(), td.static_methods.clone()))
                .collect();
            for (method_ids, static_method_ids) in &class_type_defs {
                self.collect_type_method_stubs(
                    method_ids,
                    static_method_ids,
                    module_idx,
                    &mut table,
                    &mut stub_entries,
                );
            }

            // --- Struct instance and static methods ---
            let struct_type_defs: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
                .into_iter()
                .filter(|td| {
                    !td.has_type_params()
                        && (!td.methods.is_empty() || !td.static_methods.is_empty())
                })
                .map(|td| (td.methods.clone(), td.static_methods.clone()))
                .collect();
            for (method_ids, static_method_ids) in &struct_type_defs {
                self.collect_type_method_stubs(
                    method_ids,
                    static_method_ids,
                    module_idx,
                    &mut table,
                    &mut stub_entries,
                );
            }

            // --- Implement block methods (instance, static, and interface defaults) ---
            let impl_entries: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_implement_blocks(module_path)
                .to_vec();
            for entry in &impl_entries {
                self.collect_implement_block_stubs(
                    entry,
                    module_idx,
                    &mut table,
                    &mut stub_entries,
                );
            }
        }

        // Populate func_name_to_idx so compile_trigger can map compiled
        // function names back to their dispatch table slots.
        for &(func_idx, _, ref display_name) in &stub_entries {
            table
                .func_name_to_idx
                .insert(display_name.clone(), func_idx);
        }

        if stub_entries.is_empty() {
            tracing::debug!("generate_lazy_stubs: no stubs needed");
            return Ok(());
        }

        tracing::debug!(
            count = stub_entries.len(),
            "generate_lazy_stubs: generating stubs"
        );

        // Import compile_trigger as a JIT function
        let trigger_sig = self.jit.create_signature(&[types::I64], None);
        let compile_trigger_func_id = self
            .jit
            .import_function("vole_compile_trigger", &trigger_sig);

        // Generate CLIF stubs for each undeclared module function.
        // We need to split jit fields to avoid borrowing conflicts:
        // generate_lazy_stub needs &mut module and &mut ctx, while we
        // read from the table (which is separate).
        for &(func_idx, func_id, _) in &stub_entries {
            let module_idx = table.func_to_module[func_idx];
            let compiled_flag_addr = table.compiled_flag_ptr(module_idx) as u64;
            let fn_ptr_addr = table.fn_ptr_slot_ptr(func_idx) as u64;

            generate_lazy_stub(
                &mut self.jit.module,
                &mut self.jit.ctx,
                func_id,
                compile_trigger_func_id,
                compiled_flag_addr,
                fn_ptr_addr,
                module_idx,
            )?;

            self.defined_functions.insert(func_id);
            self.jit.defined_func_ids.insert(func_id);
        }

        tracing::debug!(
            modules = table.module_index.len(),
            functions = table.fn_ptrs.len(),
            "generate_lazy_stubs: dispatch table built"
        );

        // Store the dispatch table for later use by compile_trigger.
        // Wrap in Arc for shared ownership — all mutations are done; from here
        // the table is only read (via atomic loads/stores in stubs and compile_trigger).
        self.dispatch_table = Some(Arc::new(table));

        Ok(())
    }

    /// Collect lazy stub entries for type instance and static methods.
    ///
    /// Iterates the given method_ids and static_method_ids, looks up each in the
    /// func_registry, and registers declared-but-not-defined ones as stub entries.
    fn collect_type_method_stubs(
        &self,
        method_ids: &[vole_identity::MethodId],
        static_method_ids: &[vole_identity::MethodId],
        module_idx: usize,
        table: &mut super::lazy::LazyDispatchTable,
        stub_entries: &mut Vec<(usize, cranelift_module::FuncId, String)>,
    ) {
        // Instance methods
        for &method_id in method_ids {
            let method_def = self.analyzed.get_method_def(method_id);
            // Skip inherited default methods — they are handled via implement block path
            if method_def.has_default {
                continue;
            }
            let func_key = self.func_registry.lookup_name_id(method_def.full_name_id);
            let Some(func_key) = func_key else { continue };
            let Some(func_id) = self.func_registry.func_id(func_key) else {
                continue;
            };

            if !self.defined_functions.contains(&func_id)
                && !table.func_index.contains_key(&func_id)
            {
                let display_name = self.func_registry.display(func_key);
                let func_idx = table.register_function(func_id, module_idx);
                stub_entries.push((func_idx, func_id, display_name));
            }
        }

        // Static methods
        for &method_id in static_method_ids {
            let method_def = self.analyzed.get_method_def(method_id);
            // Skip external-only statics (no Vole body to compile)
            if method_def.external_binding.is_some() {
                continue;
            }
            let func_key = self.func_registry.lookup_name_id(method_def.full_name_id);
            let Some(func_key) = func_key else { continue };
            let Some(func_id) = self.func_registry.func_id(func_key) else {
                continue;
            };

            if !self.defined_functions.contains(&func_id)
                && !table.func_index.contains_key(&func_id)
            {
                let display_name = self.func_registry.display(func_key);
                let func_idx = table.register_function(func_id, module_idx);
                stub_entries.push((func_idx, func_id, display_name));
            }
        }
    }

    /// Collect lazy stub entries for implement block methods (instance, static, default).
    ///
    /// Mirrors the methods registered in `register_implement_block_inner`:
    /// explicit instance methods, interface default methods, and static methods.
    fn collect_implement_block_stubs(
        &self,
        entry: &vole_vir::VirImplementBlockEntry,
        module_idx: usize,
        table: &mut super::lazy::LazyDispatchTable,
        stub_entries: &mut Vec<(usize, cranelift_module::FuncId, String)>,
    ) {
        // Helper closure to try registering a method
        let mut try_register = |method_id: vole_identity::MethodId| {
            let full_name_id = self.analyzed.method_full_name(method_id);
            let func_key = self.func_registry.lookup_name_id(full_name_id);
            let Some(func_key) = func_key else { return };
            let Some(func_id) = self.func_registry.func_id(func_key) else {
                return;
            };

            if !self.defined_functions.contains(&func_id)
                && !table.func_index.contains_key(&func_id)
            {
                let display_name = self.func_registry.display(func_key);
                let func_idx = table.register_function(func_id, module_idx);
                stub_entries.push((func_idx, func_id, display_name));
            }
        };

        // Instance methods
        for &method_id in &entry.instance_methods {
            try_register(method_id);
        }

        // Interface default methods (same logic as register_implement_block_inner)
        let type_def_id = entry.type_def_id;
        let direct_method_name_ids: HashSet<NameId> = entry
            .instance_methods
            .iter()
            .map(|&mid| self.analyzed.get_method_def(mid).name_id)
            .collect();

        for interface_tdef_id in self.analyzed.implemented_interfaces(type_def_id) {
            for iface_method_id in self.analyzed.type_methods(interface_tdef_id) {
                let method_def = self.analyzed.get_method_def(iface_method_id);
                if !method_def.has_default {
                    continue;
                }
                if method_def.external_binding.is_some() {
                    continue;
                }
                if direct_method_name_ids.contains(&method_def.name_id) {
                    continue;
                }
                // Skip abstract/generic default methods (not registered in pass 1)
                let vir_subs = self
                    .analyzed
                    .interface_impl_type_param_vir_subs(type_def_id, interface_tdef_id);
                if !vir_subs.is_empty()
                    && vir_subs
                        .values()
                        .any(|&v| self.vir_query_unwrap_type_param_v(v).is_some())
                {
                    continue;
                }
                if let Some(impl_method_id) =
                    self.analyzed.find_method(type_def_id, method_def.name_id)
                {
                    try_register(impl_method_id);
                }
            }
        }

        // Static methods
        for &method_id in &entry.static_methods {
            try_register(method_id);
        }
    }

    /// Compile all function bodies for a single module.
    ///
    /// Iterates VirEntityMetadata (function_defs, type_defs) instead of walking
    /// AST module programs.  The module interner is obtained from VirProgram's
    /// `module_interners` map (populated during VIR lowering).
    fn compile_module_function_bodies(&mut self, module_path: &str) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        tracing::debug!(module_path, "compile_module_functions: compiling bodies");

        // Get module interner from VirProgram (populated during VIR lowering)
        let module_interner = self
            .analyzed
            .module_interner_rc(module_path)
            .unwrap_or_else(|| self.analyzed.interner_rc());

        // Register destructured import bindings for this module from VirProgram.
        // When a module uses `let { add } = import "./other"`, the binding must
        // be available during compilation of the module's function bodies.
        let module_bindings = self.extract_module_destructured_bindings(module_path);
        let module_binding_keys: Vec<Symbol> = module_bindings.iter().map(|(k, _)| *k).collect();
        for (key, binding) in module_bindings {
            self.global_module_bindings.insert(key, binding);
        }

        let module_id = self.analyzed.module_id_or_main(module_path);

        // Compile pure Vole function bodies from VirEntityMetadata.
        // Skip generic functions (compiled via monomorphized instances) and
        // external functions (no Vole body to compile).
        let func_name_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_function_defs(module_id)
            .into_iter()
            .filter(|fd| !fd.is_generic && !fd.is_external)
            .map(|fd| fd.name_id)
            .collect();
        for name_id in func_name_ids {
            self.compile_module_function_by_name_id(module_path, name_id, &module_interner)?;
        }

        // Compile implement block methods from VIR metadata (both instance and static)
        let impl_entries = self
            .analyzed
            .entity_metadata
            .module_implement_blocks(module_path)
            .to_vec();
        for entry in &impl_entries {
            self.compile_module_implement_block(entry, &module_interner, module_id)?;
        }

        // Compile module class methods (both instance and static) from VirEntityMetadata
        let class_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
            .into_iter()
            .filter(|td| !td.methods.is_empty() || !td.static_methods.is_empty())
            .map(|td| td.id)
            .collect();
        for type_def_id in class_ids {
            self.compile_module_type_methods_by_id(type_def_id, &module_interner, module_path)?;
        }

        // Compile module struct methods (both instance and static) from VirEntityMetadata
        let struct_ids: Vec<_> = self
            .analyzed
            .entity_metadata
            .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
            .into_iter()
            .filter(|td| !td.methods.is_empty() || !td.static_methods.is_empty())
            .map(|td| td.id)
            .collect();
        for type_def_id in struct_ids {
            self.compile_module_type_methods_by_id(type_def_id, &module_interner, module_path)?;
        }

        // Remove module-specific destructured import bindings to avoid
        // symbol collisions with other modules (different interners).
        for key in &module_binding_keys {
            self.global_module_bindings.remove(key);
        }

        Ok(())
    }

    /// Import pre-compiled module functions as external symbols.
    /// This declares the functions so they can be called, but doesn't compile them.
    /// Used when modules are already compiled in a shared CompiledModules cache.
    fn import_module_functions(&mut self) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

        let module_paths = self.analyzed.module_paths();

        for module_path in &module_paths {
            let module_id = self.analyzed.module_id_or_main(module_path);

            // Import pure Vole functions from VirEntityMetadata (already compiled, just need declarations).
            // Skip generic functions (declared via monomorphized instances) and
            // external functions (declared via implement block / FFI path).
            let func_defs: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_function_defs(module_id)
                .into_iter()
                .filter(|fd| !fd.is_generic && !fd.is_external)
                .map(|fd| fd.name_id)
                .collect();
            for name_id in func_defs {
                let display_name = self.analyzed.display_name(name_id);
                let func_key =
                    self.declare_function_by_name_id(name_id, &display_name, DeclareMode::Import);
                // Override generator return types for imported module functions
                if let Some(func_key) = func_key {
                    self.override_generator_return_type(name_id, func_key);
                }
            }

            // Finalize module classes (register type metadata, import methods)
            // MUST happen before implement block import, which needs type_metadata
            let class_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in class_ids {
                self.finalize_module_type_by_id(type_def_id, DeclareMode::Import)?;
            }

            // Finalize module structs (register type metadata, import methods)
            let struct_ids: Vec<_> = self
                .analyzed
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in struct_ids {
                self.finalize_module_type_by_id(type_def_id, DeclareMode::Import)?;
            }

            // Import implement block methods from VIR metadata (using Linkage::Import)
            // MUST happen after class finalization so type_metadata is populated
            let impl_entries = self
                .analyzed
                .entity_metadata
                .module_implement_blocks(module_path)
                .to_vec();
            for entry in &impl_entries {
                self.import_module_implement_block(entry)?;
            }
        }

        // Import array Iterable default methods from the pre-compiled module cache.
        // compile_array_iterable_default_methods is only called in compile_modules_only;
        // when using the module cache, we must import these functions instead so that
        // array_iterable_func_keys is populated for call-site dispatch.
        self.import_array_iterable_default_methods()?;

        Ok(())
    }

    /// Compile a single module function using VIR metadata (no AST FuncDecl needed).
    ///
    /// Takes the function's `NameId` (from `VirFunctionDef`) and the module interner
    /// for symbol resolution during compilation.
    fn compile_module_function_by_name_id(
        &mut self,
        module_path: &str,
        name_id: NameId,
        module_interner: &Interner,
    ) -> CodegenResult<()> {
        let func_key = self.func_registry.intern_name_id(name_id);
        let display_name = self.analyzed.display_name(name_id);
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("module function", &display_name))?;
        let module_id = self.analyzed.module_id_or_main(module_path);

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .analyzed
            .function_id_by_name_id(name_id)
            .ok_or_else(|| CodegenError::not_found("function in registry", &display_name))?;
        let func_def = self.analyzed.function_def(semantic_func_id);
        let (param_type_ids, return_type_id) =
            (func_def.sema_param_types.clone(), func_def.sema_return_type);

        // Check if a VIR function was lowered for this function
        let vir_func = self.analyzed.get_function(semantic_func_id);

        // Check if this is a generator function (sema annotated it with element type)
        if let Some(elem_type_id) = func_def.sema_generator_element_type {
            let vir = vir_func.unwrap_or_else(|| {
                panic!(
                    "VIR must be available for generator function '{}'",
                    display_name,
                )
            });
            let source_file_ptr = self.source_file_ptr();
            let env = compile_env!(self, module_interner, source_file_ptr);
            let param_names: Vec<_> = vir.params.iter().map(|(name, _, _)| *name).collect();
            let gen_params = crate::generator::GeneratorParams {
                param_names: &param_names,
                jit_func_id,
                wrapper_func_key: func_key,
                param_type_ids: &param_type_ids,
                elem_type_id,
                module_id: Some(module_id),
                vir_body: &vir.body,
            };
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );
            crate::generator::compile_generator_function(&gen_params, &mut codegen_ctx, &env)?;
            // Track the wrapper function as defined so CompiledModules includes it.
            // (CodegenCtx calls module.define_function() directly, bypassing
            // JitContext::define_function() which normally updates defined_func_ids.)
            self.jit.defined_func_ids.insert(jit_func_id);
            self.jit.clear();
            return Ok(());
        }

        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Build params from VIR function param Symbols + pre-resolved TypeIds
        let vir = vir_func.expect("VIR must be available for module function");
        let params: Vec<(Symbol, VirTypeId, types::Type)> = vir
            .params
            .iter()
            .zip(param_type_ids.iter())
            .map(|(&(sym, _, _), &type_id)| {
                let cranelift_type = self.vir_query_type_to_cranelift(type_id);
                (sym, self.vir_lookup(type_id), cranelift_type)
            })
            .collect();

        // Get function return type id from pre-resolved signature
        let return_type_id_opt = if return_type_id.is_void() {
            None
        } else {
            Some(self.vir_lookup(return_type_id))
        };

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, module_interner, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let config = FunctionCompileConfig::top_level(params, return_type_id_opt);
            compile_function_inner_with_vir(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                &vir.body,
                Some(module_id),
                None,
            )?;
        }

        // Define the function
        self.finalize_function(jit_func_id)?;

        Ok(())
    }

    /// Compile a main-program function by NameId (VIR-based, no AST FuncDecl needed).
    ///
    /// Used when iterating VirEntityMetadata function definitions instead of
    /// walking AST declarations.
    fn compile_main_function_by_name_id(&mut self, name_id: NameId) -> CodegenResult<()> {
        let func_key = self.func_registry.intern_name_id(name_id);
        let display_name = self.analyzed.display_name(name_id);
        let _timing = compile_timing!(TRACE, "compile_function", name = %display_name).entered();
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("function", &display_name))?;

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .analyzed
            .function_id_by_name_id(name_id)
            .ok_or_else(|| CodegenError::not_found("function in registry", &display_name))?;
        let func_def = self.analyzed.function_def(semantic_func_id);
        let (param_type_ids, return_type_id) =
            (func_def.sema_param_types.clone(), func_def.sema_return_type);

        // Check if a VIR function was lowered for this function
        let vir_func = self.analyzed.get_function(semantic_func_id);

        // Check if this is a generator function (sema annotated it with element type)
        if let Some(elem_type_id) = func_def.sema_generator_element_type {
            let vir = vir_func.unwrap_or_else(|| {
                panic!(
                    "VIR must be available for generator function '{}'",
                    display_name,
                )
            });
            let source_file_ptr = self.source_file_ptr();
            let env = compile_env!(self, source_file_ptr);
            let param_names: Vec<_> = vir.params.iter().map(|(name, _, _)| *name).collect();
            let gen_params = crate::generator::GeneratorParams {
                param_names: &param_names,
                jit_func_id,
                wrapper_func_key: func_key,
                param_type_ids: &param_type_ids,
                elem_type_id,
                module_id: None,
                vir_body: &vir.body,
            };
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );
            crate::generator::compile_generator_function(&gen_params, &mut codegen_ctx, &env)?;
            // Track the wrapper function as defined (see module path comment above).
            self.jit.defined_func_ids.insert(jit_func_id);
            self.jit.clear();
            return Ok(());
        }

        // Create function signature from pre-resolved types
        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Build params using VIR function param Symbols
        let vir = vir_func.unwrap_or_else(|| {
            panic!(
                "VIR must be available for non-generic, non-generator function '{}'",
                display_name,
            )
        });
        let params: Vec<(Symbol, VirTypeId, types::Type)> = vir
            .params
            .iter()
            .zip(param_type_ids.iter())
            .map(|(&(sym, _, _), &type_id)| {
                let vir_ty = self.vir_lookup(type_id);
                let cranelift_type = self.vir_query_type_to_cranelift(type_id);
                (sym, vir_ty, cranelift_type)
            })
            .collect();

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let return_vir_ty = self.vir_lookup(return_type_id);
        let return_type_opt = Some(return_vir_ty).filter(|&id| id != VirTypeId::VOID);
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
            let config = FunctionCompileConfig::top_level(params, return_type_opt);
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
        self.finalize_function(jit_func_id)?;

        Ok(())
    }

    // =====================================================================
    // VIR-monomorphized function declaration and compilation
    // =====================================================================

    /// Return sorted indices of VIR monomorphized functions that may be
    /// targeted by `CallTarget::VirDirect`.
    ///
    /// Roots:
    /// - regular concrete VIR functions (non-monomorphized names), and
    /// - VIR-backed monomorphized instances (`mangled_name_id.is_some()`).
    ///
    /// From those roots, walk `VirDirect` edges transitively and collect
    /// target indices that must be declared/compiled.
    fn vir_monomorph_indices(&self) -> Vec<usize> {
        // When vir_monomorph_base is usize::MAX, no VIR monomorphs exist and
        // the entire graph traversal (including recursive test body walking)
        // can be skipped.  ~71% of test files have zero monomorphs.
        if self.analyzed.vir_monomorph_base == usize::MAX {
            return Vec::new();
        }
        collect_reachable_vir_direct_targets(&self.analyzed.functions, &self.analyzed.tests)
    }

    /// Declare VIR-monomorphized functions in the JIT module.
    ///
    /// Functions at indices `>= vir_monomorph_base` in `VirProgram.functions`
    /// were produced by `run_vir_monomorphize`.  Each is declared with a
    /// unique name derived from the VIR function's mangled name, and the
    /// resulting `FuncId` is stored in `state.vir_direct_func_ids` for lookup
    /// during `CallTarget::VirDirect` compilation.
    fn declare_vir_monomorphized_functions(&mut self) -> CodegenResult<()> {
        let indices = self.vir_monomorph_indices();
        if indices.is_empty() {
            return Ok(());
        }
        for idx in indices {
            let vir_func = &self.analyzed.functions[idx];

            // If this VIR-monomorphized function was also declared by
            // declare_monomorphized_instances (via its mangled NameId), reuse
            // that FuncId so that VirDirect calls and name-based calls both
            // resolve to the same compiled body.
            if let Some(mangled_name_id) = vir_func.mangled_name_id {
                let func_key = self.func_registry.intern_name_id(mangled_name_id);
                if let Some(existing_func_id) = self.func_registry.func_id(func_key) {
                    self.state.vir_direct_func_ids.insert(idx, existing_func_id);
                    continue;
                }
            }

            let sig = self.build_signature_for_vir_func(vir_func);
            let jit_name = format!("__vir_monomorph_{}", vir_func.name);

            // If already compiled in CompiledModules, import instead of declaring
            // for local compilation. Mark as defined to skip body compilation.
            let func_id = if self.jit.has_precompiled_symbol(&jit_name) {
                let fid = self.jit.import_function(&jit_name, &sig);
                self.defined_functions.insert(fid);
                fid
            } else {
                self.jit.declare_function(&jit_name, &sig)
            };
            self.state.vir_direct_func_ids.insert(idx, func_id);
        }
        Ok(())
    }

    /// Compile VIR-monomorphized function bodies.
    ///
    /// Must be called after [`declare_vir_monomorphized_functions`] so that
    /// all VirDirect targets have FuncIds for cross-referencing.
    fn compile_vir_monomorphized_functions(&mut self) -> CodegenResult<()> {
        self.compile_vir_monomorphized_functions_phased(true)
    }

    /// Phase-aware compilation of VIR-monomorphized function bodies.
    ///
    /// When `is_program_phase` is false (module compilation), functions whose
    /// original generic template belongs to the main program module are skipped
    /// — their types (classes, structs) aren't registered in `type_metadata`
    /// yet and will be compiled later in `compile_program_body`.
    fn compile_vir_monomorphized_functions_phased(
        &mut self,
        is_program_phase: bool,
    ) -> CodegenResult<()> {
        let indices = self.vir_monomorph_indices();
        if indices.is_empty() {
            return Ok(());
        }
        let program_module = self.program_module();
        for idx in indices {
            let Some(&func_id) = self.state.vir_direct_func_ids.get(&idx) else {
                continue;
            };
            if self.defined_functions.contains(&func_id) {
                continue;
            }
            let vir_func = &self.analyzed.functions[idx];

            // Skip VIR functions that have a corresponding free_monomorphs
            // entry. These functions were lowered from generic templates whose
            // CallTarget::Native Symbols may reference a different interner
            // context (module interner vs program interner). The free_monomorphs
            // path in compile_all_monomorphized_instances handles them correctly
            // via compile_function_inner_with_vir, which passes substitutions
            // and uses the proper compilation environment.
            if let Some(mangled_name_id) = vir_func.mangled_name_id
                && self.analyzed.free_monomorphs.contains_key(&mangled_name_id)
            {
                continue;
            }

            // Determine the module of the original generic template.
            // During the module phase, skip functions that belong to the
            // program module — their types aren't in type_metadata yet.
            let func_module = self
                .analyzed
                .entity_metadata
                .get_function_def(vir_func.id)
                .map(|fd| fd.module);
            let is_program_func = func_module.map(|m| m == program_module).unwrap_or(true); // conservatively treat unknown as program-owned
            if is_program_func && !is_program_phase {
                continue;
            }

            let sig = self.build_signature_for_vir_func(vir_func);
            self.jit.ctx.func.signature = sig;

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
                super::common::compile_vir_monomorph_function(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    vir_func,
                )?;
            }
            self.finalize_function(func_id)?;
        }
        Ok(())
    }
}

fn collect_reachable_vir_direct_targets(
    functions: &[vole_vir::func::VirFunction],
    tests: &[vole_vir::func::VirTest],
) -> Vec<usize> {
    let mut worklist: Vec<usize> = Vec::new();
    let mut visited = BTreeSet::new();
    let mut targets = BTreeSet::new();

    // Seed worklist with non-monomorph functions (entry points).
    for (idx, func) in functions.iter().enumerate() {
        let is_early_vir_monomorph = func.name.contains("<VirTypeId(");
        if func.mangled_name_id.is_some() || !is_early_vir_monomorph {
            worklist.push(idx);
        }
    }

    // Seed with VirDirect targets from test bodies (test bodies may reference
    // VIR-monomorphized functions via resolved GenericCall → VirDirect).
    for test in tests {
        let mut test_targets = BTreeSet::new();
        collect_vir_direct_in_body(&test.body, &mut test_targets);
        for target_idx in test_targets {
            if targets.insert(target_idx) {
                worklist.push(target_idx);
            }
        }
    }

    while let Some(func_idx) = worklist.pop() {
        if func_idx >= functions.len() || !visited.insert(func_idx) {
            continue;
        }

        let mut direct_targets = BTreeSet::new();
        collect_vir_direct_in_body(&functions[func_idx].body, &mut direct_targets);
        for target_idx in direct_targets {
            if targets.insert(target_idx) {
                worklist.push(target_idx);
            }
        }
    }

    targets.into_iter().collect()
}

fn collect_vir_direct_in_body(body: &VirBody, out: &mut BTreeSet<usize>) {
    for stmt in &body.stmts {
        collect_vir_direct_in_stmt(stmt, out);
    }
    if let Some(trailing) = &body.trailing {
        collect_vir_direct_in_ref(trailing, out);
    }
}

fn collect_vir_direct_in_ref(r: &VirRef, out: &mut BTreeSet<usize>) {
    collect_vir_direct_in_expr(r, out);
}

fn collect_vir_direct_in_stmt(stmt: &VirStmt, out: &mut BTreeSet<usize>) {
    match stmt {
        VirStmt::Let { value, .. } => collect_vir_direct_in_ref(value, out),
        VirStmt::LetTuple { value, .. } => collect_vir_direct_in_ref(value, out),
        VirStmt::Assign { target, value } => {
            match target {
                vole_vir::stmt::AssignTarget::Local(_) => {}
                vole_vir::stmt::AssignTarget::Field { object, .. } => {
                    collect_vir_direct_in_ref(object, out)
                }
                vole_vir::stmt::AssignTarget::Index { array, index } => {
                    collect_vir_direct_in_ref(array, out);
                    collect_vir_direct_in_ref(index, out);
                }
            }
            collect_vir_direct_in_ref(value, out);
        }
        VirStmt::Expr { value } => collect_vir_direct_in_ref(value, out),
        VirStmt::While { cond, body } => {
            collect_vir_direct_in_ref(cond, out);
            collect_vir_direct_in_body(body, out);
        }
        VirStmt::For(vir_for) => {
            collect_vir_direct_in_ref(&vir_for.iterable, out);
            collect_vir_direct_in_body(&vir_for.body, out);
        }
        VirStmt::Return { value, .. } => {
            if let Some(v) = value {
                collect_vir_direct_in_ref(v, out);
            }
        }
        VirStmt::Raise { fields, .. } => {
            for (_, val) in fields {
                collect_vir_direct_in_ref(val, out);
            }
        }
        VirStmt::RcInc { value, .. } | VirStmt::RcDec { value, .. } => {
            collect_vir_direct_in_ref(value, out)
        }
        VirStmt::Break | VirStmt::Continue | VirStmt::Noop => {}
    }
}

fn collect_vir_direct_in_expr(expr: &VirExpr, out: &mut BTreeSet<usize>) {
    match expr {
        VirExpr::Call { target, args, .. } => {
            if let CallTarget::VirDirect { function_index } = target {
                out.insert(*function_index);
            }
            for arg in args {
                collect_vir_direct_in_ref(arg, out);
            }
        }
        VirExpr::Range { start, end, .. } => {
            collect_vir_direct_in_ref(start, out);
            collect_vir_direct_in_ref(end, out);
        }
        VirExpr::ArrayLiteral { elements, .. } => {
            for e in elements {
                collect_vir_direct_in_ref(e, out);
            }
        }
        VirExpr::RepeatLiteral { element, .. } => collect_vir_direct_in_ref(element, out),
        VirExpr::StructLiteral { fields, .. } | VirExpr::ClassInstance { fields, .. } => {
            for (_, val) in fields {
                collect_vir_direct_in_ref(val, out);
            }
        }
        VirExpr::BinaryOp { lhs, rhs, .. } => {
            collect_vir_direct_in_ref(lhs, out);
            collect_vir_direct_in_ref(rhs, out);
        }
        VirExpr::UnaryOp { operand, .. } => collect_vir_direct_in_ref(operand, out),
        VirExpr::StringConcat { parts } => {
            for p in parts {
                collect_vir_direct_in_ref(p, out);
            }
        }
        VirExpr::InterpolatedString { parts } => {
            for part in parts {
                if let VirStringPart::Expr { value, .. } = part {
                    collect_vir_direct_in_ref(value, out);
                }
            }
        }
        VirExpr::MethodCall { receiver, args, .. } => {
            collect_vir_direct_in_ref(receiver, out);
            for arg in args {
                collect_vir_direct_in_ref(arg, out);
            }
        }
        VirExpr::ArrayFilled { count, value, .. } => {
            collect_vir_direct_in_ref(count, out);
            collect_vir_direct_in_ref(value, out);
        }
        VirExpr::FieldLoad { object, .. } => collect_vir_direct_in_ref(object, out),
        VirExpr::FieldStore { object, value, .. } => {
            collect_vir_direct_in_ref(object, out);
            collect_vir_direct_in_ref(value, out);
        }
        VirExpr::Index { object, index, .. } => {
            collect_vir_direct_in_ref(object, out);
            collect_vir_direct_in_ref(index, out);
        }
        VirExpr::IndexStore {
            object,
            index,
            value,
            ..
        } => {
            collect_vir_direct_in_ref(object, out);
            collect_vir_direct_in_ref(index, out);
            collect_vir_direct_in_ref(value, out);
        }
        VirExpr::RcInc { value, .. } | VirExpr::RcDec { value, .. } | VirExpr::RcMove { value } => {
            collect_vir_direct_in_ref(value, out);
        }
        VirExpr::Coerce { value, .. } => collect_vir_direct_in_ref(value, out),
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_vir_direct_in_ref(cond, out);
            collect_vir_direct_in_body(then_body, out);
            if let Some(else_body) = else_body {
                collect_vir_direct_in_body(else_body, out);
            }
        }
        VirExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_vir_direct_in_ref(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_vir_direct_in_ref(guard, out);
                }
                collect_vir_direct_in_body(&arm.body, out);
                collect_vir_direct_in_pattern(&arm.pattern, out);
            }
        }
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            for stmt in stmts {
                collect_vir_direct_in_stmt(stmt, out);
            }
            if let Some(trailing) = trailing {
                collect_vir_direct_in_ref(trailing, out);
            }
        }
        VirExpr::IsCheck { value, .. } | VirExpr::AsCast { value, .. } => {
            collect_vir_direct_in_ref(value, out);
        }
        VirExpr::MetaAccess { kind, .. } => match kind {
            VirMetaKind::Static { object, .. } => {
                if let Some(obj) = object {
                    collect_vir_direct_in_ref(obj, out);
                }
            }
            VirMetaKind::Dynamic { value } | VirMetaKind::TypeParam { value, .. } => {
                collect_vir_direct_in_ref(value, out);
            }
        },
        VirExpr::LocalStore { value, .. } => collect_vir_direct_in_ref(value, out),
        VirExpr::Lambda { body, .. } => collect_vir_direct_in_body(body, out),
        VirExpr::NullCoalesce { value, default, .. } => {
            collect_vir_direct_in_ref(value, out);
            collect_vir_direct_in_ref(default, out);
        }
        VirExpr::OptionalChain { object, .. } => collect_vir_direct_in_ref(object, out),
        VirExpr::OptionalMethodCall {
            object,
            method_args,
            ..
        } => {
            collect_vir_direct_in_ref(object, out);
            for arg in method_args {
                collect_vir_direct_in_ref(arg, out);
            }
        }
        VirExpr::Try { value, .. } | VirExpr::Yield { value } => {
            collect_vir_direct_in_ref(value, out);
        }
        VirExpr::IntLiteral { .. }
        | VirExpr::WideLiteral { .. }
        | VirExpr::FloatLiteral { .. }
        | VirExpr::BoolLiteral(_)
        | VirExpr::StringLiteral(_)
        | VirExpr::NilLiteral
        | VirExpr::Unreachable { .. }
        | VirExpr::Import { .. }
        | VirExpr::TypeLiteral
        | VirExpr::LocalLoad { .. } => {}
    }
}

fn collect_vir_direct_in_pattern(pattern: &VirPattern, out: &mut BTreeSet<usize>) {
    match pattern {
        VirPattern::Literal { value, .. } => collect_vir_direct_in_ref(value, out),
        VirPattern::Success { inner, .. } => {
            if let Some(inner) = inner {
                collect_vir_direct_in_pattern(inner, out);
            }
        }
        VirPattern::Tuple { bindings } => {
            for binding in bindings {
                collect_vir_direct_in_pattern(&binding.pattern, out);
            }
        }
        VirPattern::Wildcard
        | VirPattern::Binding { .. }
        | VirPattern::Val { .. }
        | VirPattern::Error { .. }
        | VirPattern::Record { .. }
        | VirPattern::TypeCheck { .. } => {}
    }
}
