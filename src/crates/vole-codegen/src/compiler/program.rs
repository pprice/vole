use std::collections::BTreeSet;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};

use super::common::{FunctionCompileConfig, compile_function_inner_with_vir};
use super::{Compiler, DeclareMode};

use crate::FunctionKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, function_name_id_with_interner, type_id_to_cranelift};
use vole_frontend::ast::TestsDecl;
use vole_frontend::{Decl, FuncDecl, Interner, Program, Symbol};
use vole_identity::{ModuleId, NameId, TypeId};
use vole_vir::calls::CallTarget;
use vole_vir::expr::{VirExpr, VirMetaKind, VirPattern, VirStringPart};
use vole_vir::func::VirBody;
use vole_vir::refs::VirRef;
use vole_vir::stmt::VirStmt;

impl Compiler<'_> {
    fn main_function_key_and_name(&mut self, sym: Symbol) -> CodegenResult<(FunctionKey, String)> {
        // Collect info using query (immutable borrow)
        let (name_id, display_name) = {
            let module_id = self.program_module();
            (
                self.analyzed.try_function_name_id(module_id, sym),
                self.analyzed.resolve_symbol(sym).to_string(),
            )
        };
        // Mutable operations on func_registry
        let name_id = name_id.ok_or_else(|| {
            CodegenError::internal_with_context(
                "function not found in NameTable",
                display_name.clone(),
            )
        })?;
        let key = self.func_registry.intern_name_id(name_id);
        Ok((key, display_name))
    }

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
        let type_table = &vir.type_table;
        let type_arena = self.analyzed.type_arena();
        for (&binding_sym, &(module_id, export_name, vir_export_ty)) in &vir.module_bindings {
            let export_type_id = crate::types::vir_conversions::vir_to_sema_type_id(
                vir_export_ty,
                type_table,
                type_arena,
            );
            self.global_module_bindings
                .insert(binding_sym, (module_id, export_name, export_type_id));
        }
    }

    /// Extract destructured import bindings for a module from VirProgram.
    ///
    /// Reads pre-resolved bindings from `module_module_bindings` in VirProgram
    /// (populated during VIR lowering). Returns a list of `(local_symbol, binding)`
    /// pairs that should be inserted into `global_module_bindings` before compiling
    /// the module's function bodies.
    fn extract_module_destructured_bindings(
        analyzed: &crate::AnalyzedProgram,
        module_path: &str,
    ) -> Vec<(Symbol, super::ModuleExportBinding)> {
        let vir = analyzed.vir_program();
        let type_table = &vir.type_table;
        let type_arena = analyzed.type_arena();
        let Some(module_bindings) = vir.module_module_bindings.get(module_path) else {
            return Vec::new();
        };
        module_bindings
            .iter()
            .map(|(&binding_sym, &(module_id, export_name, vir_export_ty))| {
                let export_type_id = crate::types::vir_conversions::vir_to_sema_type_id(
                    vir_export_ty,
                    type_table,
                    type_arena,
                );
                (binding_sym, (module_id, export_name, export_type_id))
            })
            .collect()
    }

    /// Compile a complete program
    pub fn compile_program(&mut self, program: &Program) -> CodegenResult<()> {
        // Compile module functions first (before main program)
        self.compile_module_functions()?;
        self.compile_program_body(program)
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
    pub fn compile_program_only(&mut self, program: &Program) -> CodegenResult<()> {
        self.compile_program_body(program)
    }

    /// First pass: declare all functions and tests, collect globals, finalize type metadata.
    fn declare_program_declarations(&mut self, program: &Program) -> CodegenResult<()> {
        // Bulk-register top-level module import bindings from VirProgram.
        self.register_global_module_bindings();

        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Skip generic functions - they're templates, not actual functions
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    // Declare function using helper (skips if not registered)
                    let func_key = self.declare_main_function(func.name);
                    // If this is a generator, override the return type to
                    // RuntimeIterator(T) so callers compiled before the
                    // generator itself use the correct (non-interface) type.
                    if let Some(func_key) = func_key {
                        let module_id = self.program_module();
                        if let Some(name_id) =
                            self.analyzed.try_function_name_id(module_id, func.name)
                        {
                            self.override_generator_return_type(name_id, func_key);
                        }
                    }
                }
                Decl::Tests(_) if self.skip_tests => {}
                Decl::Tests(tests_decl) => {
                    // Declare scoped type/function declarations within the tests block
                    self.declare_tests_scoped_types(tests_decl)?;
                }
                Decl::LetTuple(_) => {
                    // Module bindings are bulk-registered from VirProgram at the
                    // start of declare_program_declarations.
                }
                Decl::Let(_) => {
                    // Global initializer presence is resolved via ProgramQuery lookups.
                }
                Decl::Class(class) => {
                    self.finalize_class(class.name)?;
                }
                Decl::Interface(_) => {
                    // Interface declarations don't generate code directly
                }
                Decl::Implement(_) => {
                    // Implement blocks are registered via VirImplementBlockEntry below.
                }
                Decl::Struct(s) => {
                    self.finalize_struct(s.name)?;
                }
                Decl::Error(_) => {
                    // Error declarations don't generate code in pass 1
                }
                Decl::Sentinel(_) => {
                    // Sentinel declarations don't generate code in pass 1
                }
                Decl::External(_) => {
                    // External blocks don't generate code in pass 1
                }
            }
        }

        // Register implement block methods from VIR metadata (pass 1).
        // This replaces the old AST-based Decl::Implement loop above.
        for entry in self
            .analyzed
            .vir_program()
            .entity_metadata
            .implement_blocks()
        {
            self.register_implement_block(entry)?;
        }

        // Declare all test functions from VirProgram's flat test list.
        // This uses VirProgram.tests order (outer tests first, then nested),
        // matching the order used during compilation in compile_all_tests.
        if !self.skip_tests {
            let num_tests = self.analyzed.vir_program().tests.len();
            let i64_type_id = self.vir_query_primitives().i64;
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
    /// Note: Decl::Let globals are handled by inlining their initializers
    /// when referenced (see compile_expr for ExprKind::Identifier).
    fn compile_program_declarations(&mut self, program: &Program) -> CodegenResult<()> {
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Skip generic functions - they're compiled via monomorphized instances
                    // This includes both explicit generics (type_params in AST) and implicit
                    // generics (structural type params that create generic_info in entity registry)
                    if !func.type_params.is_empty() {
                        continue;
                    }

                    // Check for implicit generics (structural type params)
                    let program_module = self.program_module();
                    let name_id = self.analyzed.function_name_id(program_module, func.name);
                    let has_implicit_generic_info = self
                        .analyzed
                        .function_id_by_name_id(name_id)
                        .map(|func_id| self.analyzed.function_def(func_id).is_generic)
                        .unwrap_or(false);
                    if has_implicit_generic_info {
                        continue;
                    }

                    self.compile_function(func)?;
                }
                Decl::Tests(_) if self.skip_tests => {}
                Decl::Tests(tests_decl) => {
                    // Compile scoped function/class/implement bodies (recursive into nested tests)
                    self.compile_tests_scoped_bodies(tests_decl)?;
                }
                Decl::Let(_) | Decl::LetTuple(_) => {
                    // Globals are handled during identifier lookup
                    // LetTuple (destructuring imports) don't generate code
                }
                Decl::Class(class) => {
                    self.compile_class_methods(class.name)?;
                }
                Decl::Interface(_) => {
                    // Interface methods are compiled when used via implement blocks
                }
                Decl::Implement(_) => {
                    // Implement blocks are compiled via VirImplementBlockEntry below.
                }
                Decl::Struct(struct_decl) => {
                    if !struct_decl.methods.is_empty() || struct_decl.statics.is_some() {
                        self.compile_struct_methods(
                            struct_decl.name,
                            !struct_decl.type_params.is_empty(),
                        )?;
                    }
                }
                Decl::Error(_) => {
                    // Error declarations don't generate code in pass 2
                }
                Decl::Sentinel(_) => {
                    // Sentinel declarations don't generate code in pass 2
                }
                Decl::External(_) => {
                    // External blocks don't generate code in pass 2
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
    fn compile_program_body(&mut self, program: &Program) -> CodegenResult<()> {
        // Pre-pass: Register all class names first so they're available for field type resolution
        // This allows classes to reference each other (e.g., Company.ceo: Person?)
        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    self.pre_register_class(class.name)?;
                }
                Decl::Struct(s) => {
                    self.pre_register_struct(s.name)?;
                }
                Decl::Sentinel(s) => {
                    self.pre_register_sentinel(s.name)?;
                }
                Decl::Tests(_) if self.skip_tests => {}
                Decl::Tests(_) => {
                    // Scoped types use finalize_module_class in pass 1
                }
                _ => {}
            }
        }

        // First pass: declare all functions and tests, collect globals, finalize type metadata
        self.declare_program_declarations(program)?;

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
        self.compile_program_declarations(program)?;

        // Compile monomorphized instances
        self.compile_all_monomorphized_instances(Some(program))?;

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
    fn declare_module_types_and_functions(&mut self, module_paths: &[String]) -> CodegenResult<()> {
        for module_path in module_paths {
            tracing::debug!(module_path, "compile_module_functions: declaring functions");
            let (program, module_interner) = &self.analyzed.module_programs()[module_path];

            // Declare pure Vole functions
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    // Skip generic functions - they're declared via monomorphized instances
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    let module_id = self.analyzed.module_id_or_main(module_path);
                    let name_id = function_name_id_with_interner(
                        self.analyzed,
                        module_interner,
                        module_id,
                        func.name,
                    )
                    .ok_or_else(|| {
                        CodegenError::internal("module function: name_id not registered")
                    })?;

                    // Check for implicit generics (structural type params)
                    if self.has_implicit_generic_info(name_id) {
                        continue;
                    }

                    let display_name = self.analyzed.display_name(name_id);
                    self.declare_function_by_name_id(name_id, &display_name, DeclareMode::Declare);
                }
            }

            let module_id = self.analyzed.module_id_or_main(module_path);

            // Finalize module classes (register type metadata, declare methods)
            // MUST happen before implement block registration, which needs type_metadata
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.finalize_module_class(class.name, module_interner, module_id)?;
                }
            }

            // Finalize module structs (register type metadata, declare methods)
            for decl in &program.declarations {
                if let Decl::Struct(struct_decl) = decl {
                    self.finalize_module_struct(struct_decl.name, module_interner, module_id)?;
                }
            }

            // Register module sentinels (zero-field struct types like Done, nil)
            for decl in &program.declarations {
                if let Decl::Sentinel(sentinel_decl) = decl {
                    self.finalize_module_sentinel(sentinel_decl.name, module_interner, module_id)?;
                }
            }

            // Register implement block methods from VIR metadata
            // MUST happen after class finalization so type_metadata is populated
            let interner_rc = module_interner.clone();
            let entries = self
                .analyzed
                .vir_program()
                .entity_metadata
                .module_implement_blocks(module_path)
                .to_vec();
            for entry in &entries {
                self.register_implement_block_with_module_interner(entry, &interner_rc)?;
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
        // Passes None for program — instances from the main program are silently
        // skipped and compiled later in compile_program_body.
        self.compile_all_monomorphized_instances(None)?;

        // Pass 2: Compile all function bodies (cross-module calls now resolved)
        for module_path in &module_paths {
            self.compile_module_function_bodies(module_path)?;
        }

        // Compile any monomorphs that were lazily declared during module body compilation.
        // No main-program AST is available here; all pending monomorphs should originate
        // from module code.
        self.compile_pending_monomorphs()?;

        tracing::debug!("compile_module_functions complete");
        Ok(())
    }

    /// Compile all function bodies for a single module.
    fn compile_module_function_bodies(&mut self, module_path: &str) -> CodegenResult<()> {
        tracing::debug!(module_path, "compile_module_functions: compiling bodies");
        let (program, module_interner) = &self.analyzed.module_programs()[module_path];

        // Register destructured import bindings for this module from VirProgram.
        // When a module uses `let { add } = import "./other"`, the binding must
        // be available during compilation of the module's function bodies.
        let module_bindings =
            Self::extract_module_destructured_bindings(self.analyzed, module_path);
        let module_binding_keys: Vec<Symbol> = module_bindings.iter().map(|(k, _)| *k).collect();
        for (key, binding) in module_bindings {
            self.global_module_bindings.insert(key, binding);
        }

        // Compile pure Vole function bodies
        for decl in &program.declarations {
            if let Decl::Function(func) = decl {
                // Skip generic functions - they're compiled via monomorphized instances
                if !func.type_params.is_empty() {
                    continue;
                }
                let module_id = self.analyzed.module_id_or_main(module_path);
                let name_id = function_name_id_with_interner(
                    self.analyzed,
                    module_interner,
                    module_id,
                    func.name,
                )
                .ok_or_else(|| CodegenError::internal("module function: name_id not registered"))?;

                // Check for implicit generics (structural type params)
                let has_implicit_generic_info = self
                    .analyzed
                    .function_id_by_name_id(name_id)
                    .map(|func_id| self.analyzed.function_def(func_id).is_generic)
                    .unwrap_or(false);
                if has_implicit_generic_info {
                    continue;
                }

                self.compile_module_function(module_path, name_id, func, module_interner)?;
            }
        }

        // Compile implement block methods from VIR metadata (both instance and static)
        let module_id = self.analyzed.module_id_or_main(module_path);
        let impl_entries = self
            .analyzed
            .vir_program()
            .entity_metadata
            .module_implement_blocks(module_path)
            .to_vec();
        for entry in &impl_entries {
            self.compile_module_implement_block(entry, module_interner, module_id)?;
        }

        // Compile module class methods (both instance and static)
        for decl in &program.declarations {
            if let Decl::Class(class) = decl {
                tracing::debug!(class_name = %module_interner.resolve(class.name), "Compiling module class methods");
                self.compile_module_class_methods(class.name, module_interner, module_path)?;
            }
        }

        // Compile module struct methods (both instance and static)
        for decl in &program.declarations {
            if let Decl::Struct(struct_decl) = decl
                && (!struct_decl.methods.is_empty() || struct_decl.statics.is_some())
            {
                tracing::debug!(struct_name = %module_interner.resolve(struct_decl.name), "Compiling module struct methods");
                let has_methods = !struct_decl.methods.is_empty() || struct_decl.statics.is_some();
                self.compile_module_struct_methods(
                    struct_decl.name,
                    has_methods,
                    module_interner,
                    module_path,
                )?;
            }
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
        let module_paths = self.analyzed.module_paths();

        for module_path in &module_paths {
            let (program, module_interner) = &self.analyzed.module_programs()[module_path];

            // Import pure Vole functions (they're already compiled, just need declarations)
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    let module_id = self.analyzed.module_id_or_main(module_path);
                    let name_id = function_name_id_with_interner(
                        self.analyzed,
                        module_interner,
                        module_id,
                        func.name,
                    )
                    .ok_or_else(|| {
                        CodegenError::internal("module function: name_id not registered")
                    })?;

                    let display_name = self.analyzed.display_name(name_id);
                    let func_key = self.declare_function_by_name_id(
                        name_id,
                        &display_name,
                        DeclareMode::Import,
                    );
                    // Override generator return types for imported module functions
                    if let Some(func_key) = func_key {
                        self.override_generator_return_type(name_id, func_key);
                    }
                }
            }

            // Finalize module classes (register type metadata, import methods)
            // MUST happen before implement block import, which needs type_metadata
            let module_id = self.analyzed.module_id_or_main(module_path);
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.import_module_class(class, module_interner, module_id)?;
                }
            }

            // Finalize module structs (register type metadata, import methods)
            for decl in &program.declarations {
                if let Decl::Struct(struct_decl) = decl {
                    self.import_module_struct(struct_decl, module_interner, module_id)?;
                }
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

    /// Import a module class - register metadata and import methods.
    /// Used when modules are already compiled in a shared cache.
    fn import_module_class(
        &mut self,
        class: &vole_frontend::ast::ClassDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // First finalize to get type metadata registered
        self.finalize_module_class(class.name, module_interner, module_id)?;

        // The methods are already compiled - they'll be linked via external symbols
        // No additional work needed here since method calls go through func_registry
        // which will find the imported function IDs
        Ok(())
    }

    /// Import a module struct - register metadata and import methods.
    /// Used when modules are already compiled in a shared cache.
    fn import_module_struct(
        &mut self,
        struct_decl: &vole_frontend::ast::StructDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        self.finalize_module_struct(struct_decl.name, module_interner, module_id)
    }

    /// Compile a single module function with its own interner
    fn compile_module_function(
        &mut self,
        module_path: &str,
        name_id: NameId,
        func: &FuncDecl,
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
            let gen_params = crate::generator::GeneratorParams {
                func,
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
            self.jit.clear();
            return Ok(());
        }

        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Combine AST param names with pre-resolved TypeIds from FunctionDef
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.arena();
            func.params
                .iter()
                .zip(param_type_ids.iter())
                .map(|(p, &type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, arena_ref, self.pointer_type);
                    (p.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get function return type id from pre-resolved signature
        let return_type_id = Some(return_type_id).filter(|id| !id.is_void());

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

            let config = FunctionCompileConfig::top_level(params, return_type_id);
            let vir = vir_func.expect("VIR must be available for module function");
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

    pub(super) fn compile_function(&mut self, func: &FuncDecl) -> CodegenResult<()> {
        let program_module = self.program_module();
        let (func_key, display_name) = self.main_function_key_and_name(func.name)?;
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("function", &display_name))?;

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .analyzed
            .try_function_name_id(program_module, func.name)
            .and_then(|name_id| self.analyzed.function_id_by_name_id(name_id))
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
            let gen_params = crate::generator::GeneratorParams {
                func,
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
            self.jit.clear();
            return Ok(());
        }

        // Create function signature from pre-resolved types
        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Combine AST param names with pre-resolved TypeIds from FunctionDef
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.arena();
            func.params
                .iter()
                .zip(param_type_ids.iter())
                .map(|(p, &type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, arena_ref, self.pointer_type);
                    (p.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
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

            // Use pre-resolved return type (None for void)
            let return_type_opt = Some(return_type_id).filter(|id| !id.is_void());
            let config = FunctionCompileConfig::top_level(params, return_type_opt);
            let vir = vir_func.unwrap_or_else(|| {
                panic!(
                    "VIR must be available for non-generic, non-generator function '{}'",
                    display_name,
                )
            });
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

    // =====================================================================
    // Test-scoped declaration helpers
    //
    // These walk AST `TestsDecl` blocks to declare and compile scoped
    // functions, classes, and implement blocks.  Test *bodies* are compiled
    // separately via `compile_all_tests` which iterates VirProgram.tests.
    // =====================================================================

    /// Declare scoped type/function declarations within a tests block (pass 1).
    /// Handles scoped functions, classes, and implement blocks so they're available
    /// during test compilation. Does NOT declare test functions (those are declared
    /// from VirProgram.tests in declare_program_declarations).
    fn declare_tests_scoped_types(&mut self, tests_decl: &TestsDecl) -> CodegenResult<()> {
        let interner = self.analyzed.interner();

        // Look up the virtual module ID for scoped type declarations
        let virtual_module_id = self.analyzed.tests_virtual_module(tests_decl.span);

        for inner_decl in &tests_decl.decls {
            match inner_decl {
                Decl::Function(func) => {
                    // Skip generic functions
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    // Scoped functions are registered under the program module by sema
                    self.declare_main_function(func.name);
                }
                Decl::Class(class) => {
                    // Scoped classes are registered under the virtual module
                    if let Some(vm_id) = virtual_module_id {
                        self.finalize_module_class(class.name, interner, vm_id)?;
                    }
                }
                Decl::Implement(_) => {
                    // Scoped implement blocks are registered via VirImplementBlockEntry
                    // in the main implement_blocks() iteration.
                }
                Decl::Tests(nested_tests) => {
                    // Recursively declare nested tests block scoped types
                    self.declare_tests_scoped_types(nested_tests)?;
                }
                _ => {
                    // Let declarations, interfaces, etc. don't need pass 1 handling
                }
            }
        }

        Ok(())
    }

    /// Compile scoped function and method bodies within a tests block (pass 2).
    /// Does NOT compile test bodies (those are compiled via compile_all_tests).
    fn compile_tests_scoped_bodies(&mut self, tests_decl: &TestsDecl) -> CodegenResult<()> {
        let program_module = self.program_module();
        // Scoped types are registered under the virtual module in sema
        let virtual_module_id = self
            .analyzed
            .tests_virtual_module(tests_decl.span)
            .unwrap_or(program_module);

        for inner_decl in &tests_decl.decls {
            match inner_decl {
                Decl::Function(func) => {
                    // Skip generic functions
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    // Check for implicit generics
                    let name_id = self.analyzed.function_name_id(program_module, func.name);
                    let has_implicit_generic_info = self
                        .analyzed
                        .function_id_by_name_id(name_id)
                        .map(|func_id| self.analyzed.function_def(func_id).is_generic)
                        .unwrap_or(false);
                    if has_implicit_generic_info {
                        continue;
                    }
                    // Compile as a regular function
                    self.compile_function(func)?;
                }
                Decl::Class(class) => {
                    self.compile_class_methods_in_module(class.name, virtual_module_id)?;
                }
                Decl::Implement(_) => {
                    // Compiled via VirImplementBlockEntry in the main compile pass.
                }
                Decl::Tests(nested_tests) => {
                    // Recursively compile nested tests block scoped bodies
                    self.compile_tests_scoped_bodies(nested_tests)?;
                }
                _ => {
                    // Let declarations are handled during test body compilation
                }
            }
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
