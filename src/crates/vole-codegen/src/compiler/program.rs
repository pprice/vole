use std::collections::{BTreeSet, HashSet};

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::{Compiler, DeclareMode};

use crate::FunctionKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CodegenCtx;
use vole_identity::{Interner, NameId, Symbol, TypeId, VirTypeId};
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
        let vir = self.analyzed.vir_program();
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
        let vir = self.analyzed.vir_program();
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
        if !self.analyzed.modules_with_errors().is_empty() {
            let module_list: Vec<_> = self
                .analyzed
                .modules_with_errors()
                .iter()
                .cloned()
                .collect();
            return Err(CodegenError::internal_with_context(
                "module(s) with type errors",
                module_list.join(", "),
            ));
        }
        // Compile module functions first (before main program)
        self.compile_module_functions()?;
        self.compile_program_body()
    }

    /// Compile only module functions (prelude, imports).
    /// Call this once before compile_program_only for batched compilation.
    pub fn compile_modules_only(&mut self) -> CodegenResult<()> {
        // Bail early if any modules had sema errors - their expression data may
        // contain INVALID type IDs that would cause panics in codegen.
        if !self.analyzed.modules_with_errors().is_empty() {
            let module_list: Vec<_> = self
                .analyzed
                .modules_with_errors()
                .iter()
                .cloned()
                .collect();
            return Err(CodegenError::internal_with_context(
                "module(s) with type errors",
                module_list.join(", "),
            ));
        }
        self.compile_module_functions()
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
            .vir_program()
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
            .vir_program()
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
            .vir_program()
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
                    .vir_program()
                    .entity_metadata
                    .module_type_defs_by_kind(vm_id, VirTypeDefKind::Class)
                    .into_iter()
                    .map(|td| td.id)
                    .collect();
                for type_def_id in class_ids {
                    self.finalize_module_type_by_id(type_def_id)?;
                }
            }
        }

        // Register implement block methods from VIR metadata (pass 1).
        let impl_blocks = self
            .analyzed
            .vir_program()
            .entity_metadata
            .implement_blocks();
        for entry in impl_blocks {
            self.register_implement_block(entry)?;
        }

        // Declare all test functions from VirProgram's flat test list.
        // This uses VirProgram.tests order (outer tests first, then nested),
        // matching the order used during compilation in compile_all_tests.
        if !self.skip_tests {
            let num_tests = self.analyzed.vir_program().tests.len();
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
            .vir_program()
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
            .vir_program()
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
            .vir_program()
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
                    .vir_program()
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
        for entry in self
            .analyzed
            .vir_program()
            .entity_metadata
            .implement_blocks()
            .to_vec()
        {
            self.compile_implement_block(&entry)?;
        }

        // Compile all test bodies from VirProgram's flat test list.
        // This must happen after scoped declarations are compiled above,
        // since test bodies may reference scoped functions/classes/impls.
        if !self.skip_tests {
            let vir_tests = &self.analyzed.vir_program().tests;
            // Clone the tests slice to avoid borrowing self.analyzed during compilation.
            let vir_tests: Vec<_> = vir_tests.clone();
            self.compile_all_tests(&vir_tests)?;
        }

        Ok(())
    }

    /// Compile the main program body (functions, tests, classes, etc.)
    fn compile_program_body(&mut self) -> CodegenResult<()> {
        use vole_vir::entity_metadata::VirTypeDefKind;

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
                .vir_program()
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
        self.declare_program_declarations()?;

        // Declare monomorphized function instances before second pass
        self.declare_all_monomorphized_instances()?;

        // Declare VIR-monomorphized functions (produced by run_vir_monomorphize).
        self.declare_vir_monomorphized_functions()?;

        // Expand abstract class method templates for program-level generics.
        // MUST run after declarations (which provide concrete substitutions) but
        // before any body compilation (which may call expanded methods).
        self.expand_abstract_class_method_monomorphs()?;

        // Compile array Iterable default methods for program-level element types.
        // Module-level types already have methods from the module cache (imported
        // via import_array_iterable_default_methods); the sentinel check inside
        // compile_array_iterable_default_methods skips those.
        self.compile_array_iterable_default_methods()?;

        // Build monomorph name index for O(1) lookup during body compilation.
        // Must run after declare_all + expand_abstract so all instances are visible.
        self.build_monomorph_index();

        // Second pass: compile function bodies and tests
        self.compile_program_declarations()?;

        // Compile monomorphized instances
        self.compile_all_monomorphized_instances(true)?;

        // Compile VIR-monomorphized function bodies.
        self.compile_vir_monomorphized_functions()?;

        // Compile any monomorphs that were lazily declared during expression compilation.
        // This fixpoint loop handles transitive demand-declarations: compiling one pending
        // monomorph body may trigger demand-declaration of another.
        self.compile_pending_monomorphs()?;

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
                .vir_program()
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
                .vir_program()
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in class_ids {
                self.finalize_module_type_by_id(type_def_id)?;
            }

            // Finalize module structs (register type metadata, declare methods)
            let struct_ids: Vec<_> = self
                .analyzed
                .vir_program()
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in struct_ids {
                self.finalize_module_type_by_id(type_def_id)?;
            }

            // Register module sentinels (zero-field struct types like Done, nil)
            let sentinel_ids: Vec<_> = self
                .analyzed
                .vir_program()
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
                .vir_program()
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

    pub(super) fn compile_module_functions(&mut self) -> CodegenResult<()> {
        // Collect module paths first to avoid borrow issues
        let module_paths = self.analyzed.module_paths();
        tracing::debug!(
            ?module_paths,
            "compile_module_functions: processing module paths"
        );

        // Pass 1: Declare all functions and finalize types across all modules
        self.declare_module_types_and_functions(&module_paths)?;

        // Pass 1.5a: Declare and compile array Iterable default methods for each concrete
        // element type (e.g. count/map/filter on [i64], [string], etc.).
        self.compile_array_iterable_default_methods()?;

        // Pass 1.5: Declare all monomorphized instances (functions, class methods,
        // static methods). This pre-declares known monomorphs so they have FuncIds
        // before any body compilation begins. Instances whose ASTs live in the main
        // program are declared but not compiled here — the program phase or the
        // demand-driven fixpoint loop handles them.
        self.declare_all_monomorphized_instances()?;

        // Pass 1.6: Expand abstract class method templates into concrete instances.
        // Abstract templates are created by sema when generic code (e.g. Task.stream<T>)
        // calls instance methods on generic classes (e.g. Channel<T>.close()).
        // This MUST run before monomorph body compilation because compiled bodies
        // (e.g. Task.stream<i64>) may call these expanded methods (e.g. ch.close()).
        self.expand_abstract_class_method_monomorphs()?;

        // Build monomorph name index for O(1) lookup during body compilation.
        // Must run after declare_all + expand_abstract so all instances are visible.
        self.build_monomorph_index();

        // Pass 1.7: Compile monomorphized instances whose ASTs live in modules.
        // Passes false for is_program_phase — instances from the main program are
        // silently skipped and compiled later in compile_program_body.
        self.compile_all_monomorphized_instances(false)?;

        // Pass 2: Compile all function bodies (cross-module calls now resolved)
        // When lazy_modules is enabled, skip body compilation — functions are declared
        // with signatures but compiled on demand later.
        if !self.jit.lazy_modules {
            for module_path in &module_paths {
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

        tracing::debug!("generate_lazy_stubs: building dispatch table");

        // Build the dispatch table by iterating module functions that were
        // declared (in func_ids) but not defined (not in defined_functions).
        let mut table = Box::new(LazyDispatchTable::new());

        // Collect (module_path, func_id, display_name) for each undeclared module function.
        let mut stub_entries: Vec<(usize, cranelift_module::FuncId, String)> = Vec::new();

        for module_path in module_paths {
            let module_id = self.analyzed.module_id_or_main(module_path);
            let module_idx = table.register_module(module_path);

            // Find non-generic, non-external functions in this module
            let func_defs: Vec<_> = self
                .analyzed
                .vir_program()
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
                if self.defined_functions.contains(&func_id) {
                    continue;
                }

                let func_idx = table.register_function(func_id, module_idx);
                stub_entries.push((func_idx, func_id, display_name));
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

        // Store the dispatch table for later use by compile_trigger
        self.dispatch_table = Some(table);

        Ok(())
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
            .vir_program()
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
            .vir_program()
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
            .vir_program()
            .entity_metadata
            .module_implement_blocks(module_path)
            .to_vec();
        for entry in &impl_entries {
            self.compile_module_implement_block(entry, &module_interner, module_id)?;
        }

        // Compile module class methods (both instance and static) from VirEntityMetadata
        let class_ids: Vec<_> = self
            .analyzed
            .vir_program()
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
            .vir_program()
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
                .vir_program()
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
                .vir_program()
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Class)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in class_ids {
                self.finalize_module_type_by_id(type_def_id)?;
            }

            // Finalize module structs (register type metadata, import methods)
            let struct_ids: Vec<_> = self
                .analyzed
                .vir_program()
                .entity_metadata
                .module_type_defs_by_kind(module_id, VirTypeDefKind::Struct)
                .into_iter()
                .map(|td| td.id)
                .collect();
            for type_def_id in struct_ids {
                self.finalize_module_type_by_id(type_def_id)?;
            }

            // Import implement block methods from VIR metadata (using Linkage::Import)
            // MUST happen after class finalization so type_metadata is populated
            let impl_entries = self
                .analyzed
                .vir_program()
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
        let vir_func = self.analyzed.get_vir_function(semantic_func_id);

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
        let vir_func = self.analyzed.get_vir_function(semantic_func_id);

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
        collect_reachable_vir_direct_targets(&self.analyzed.vir_program().functions)
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
            let vir_func = &self.analyzed.vir_program().functions[idx];
            let sig = self.build_signature_for_vir_func(vir_func);
            let jit_name = format!("__vir_monomorph_{}", vir_func.name);
            let func_id = self.jit.declare_function(&jit_name, &sig);
            self.state.vir_direct_func_ids.insert(idx, func_id);
        }
        Ok(())
    }

    /// Compile VIR-monomorphized function bodies.
    ///
    /// Must be called after [`declare_vir_monomorphized_functions`] so that
    /// all VirDirect targets have FuncIds for cross-referencing.
    fn compile_vir_monomorphized_functions(&mut self) -> CodegenResult<()> {
        let indices = self.vir_monomorph_indices();
        if indices.is_empty() {
            return Ok(());
        }
        for idx in indices {
            let Some(&func_id) = self.state.vir_direct_func_ids.get(&idx) else {
                continue;
            };
            if self.defined_functions.contains(&func_id) {
                continue;
            }
            let vir_func = &self.analyzed.vir_program().functions[idx];
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

fn collect_reachable_vir_direct_targets(functions: &[vole_vir::func::VirFunction]) -> Vec<usize> {
    let mut worklist: Vec<usize> = Vec::new();
    for (idx, func) in functions.iter().enumerate() {
        let is_early_vir_monomorph = func.name.contains("<VirTypeId(");
        if func.mangled_name_id.is_some() || !is_early_vir_monomorph {
            worklist.push(idx);
        }
    }

    let mut visited = BTreeSet::new();
    let mut targets = BTreeSet::new();

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
