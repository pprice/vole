use std::rc::Rc;

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};

use super::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::{Compiler, DeclareMode};

use crate::FunctionKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, function_name_id_with_interner, type_id_to_cranelift};
use vole_frontend::ast::LetTupleStmt;
use vole_frontend::{
    Decl, Expr, ExprKind, FuncDecl, Interner, LetInit, PatternKind, Program, Symbol,
};
use vole_identity::{ModuleId, NameId};
use vole_sema::type_arena::TypeId;

impl Compiler<'_> {
    fn main_function_key_and_name(&mut self, sym: Symbol) -> (FunctionKey, String) {
        // Collect info using query (immutable borrow)
        let (name_id, display_name) = {
            let query = self.query();
            let module_id = self.program_module();
            (
                query.try_function_name_id(module_id, sym),
                query.resolve_symbol(sym).to_string(),
            )
        };
        // Mutable operations on func_registry
        let key = self
            .func_registry
            .intern_name_id(name_id.unwrap_or_else(|| {
            panic!(
                "function '{}' not found in NameTable - all functions should be interned by sema",
                display_name
            )
        }));
        (key, display_name)
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

    /// Register global module bindings from a top-level destructuring import.
    /// This extracts module exports from the pattern and stores them in global_module_bindings.
    pub(super) fn register_global_module_bindings(&mut self, let_tuple: &LetTupleStmt) {
        // Get the module type from semantic analysis
        let module_type_id = self.analyzed.expression_data.get_type(let_tuple.init.id);
        let module_type_id = match module_type_id {
            Some(id) => id,
            None => return, // No type info available
        };

        // Get module info from the type arena
        let module_info = self
            .analyzed
            .type_arena()
            .unwrap_module(module_type_id)
            .cloned();
        let module_info = match module_info {
            Some(info) => info,
            None => return, // Not a module type
        };

        // Extract bindings from the destructure pattern
        if let PatternKind::Record { fields, .. } = &let_tuple.pattern.kind {
            for field_pattern in fields {
                let export_name = field_pattern.field_name;
                let export_name_str = self.analyzed.interner.resolve(export_name);

                // Find the export type in the module
                let export_type_id = module_info
                    .exports
                    .iter()
                    .find(|(name_id, _)| {
                        self.analyzed
                            .name_table()
                            .last_segment_str(*name_id)
                            .as_deref()
                            == Some(export_name_str)
                    })
                    .map(|(_, ty)| *ty);

                if let Some(export_type_id) = export_type_id {
                    // Register the module binding: local_name -> (module_id, export_name, type_id)
                    self.global_module_bindings.insert(
                        field_pattern.binding,
                        (module_info.module_id, export_name, export_type_id),
                    );
                }
            }
        }
    }

    /// Extract destructured import bindings from a module's declarations.
    ///
    /// When a module uses `let { add } = import "./other"`, this creates bindings
    /// that map the local name (`add`) to the source module's function. These bindings
    /// must be available during compilation of the module's function bodies so that
    /// calls to `add()` can be resolved.
    ///
    /// Returns a list of `(local_symbol, binding)` pairs that should be inserted into
    /// `global_module_bindings` before compiling the module's function bodies.
    fn extract_module_destructured_bindings(
        analyzed: &crate::AnalyzedProgram,
        program: &Program,
        module_interner: &Interner,
        module_path: &str,
    ) -> Vec<(Symbol, super::ModuleExportBinding)> {
        let mut bindings = Vec::new();
        // Get the module-specific type map (module NodeIds are separate from main program)
        let module_types = analyzed.expression_data.module_types(module_path);
        for decl in &program.declarations {
            if let Decl::LetTuple(let_tuple) = decl
                && let ExprKind::Import(_) = &let_tuple.init.kind
            {
                // Look up the import expression's type in the module-specific type map
                let module_type_id =
                    module_types.and_then(|types| types.get(&let_tuple.init.id).copied());
                let Some(module_type_id) = module_type_id else {
                    continue;
                };
                let Some(module_info) =
                    analyzed.type_arena().unwrap_module(module_type_id).cloned()
                else {
                    continue;
                };

                if let PatternKind::Record { fields, .. } = &let_tuple.pattern.kind {
                    for field_pattern in fields {
                        let export_name = field_pattern.field_name;
                        let export_name_str = module_interner.resolve(export_name);

                        let export_type_id = module_info
                            .exports
                            .iter()
                            .find(|(name_id, _)| {
                                analyzed.name_table().last_segment_str(*name_id).as_deref()
                                    == Some(export_name_str)
                            })
                            .map(|(_, ty)| *ty);

                        if let Some(export_type_id) = export_type_id {
                            bindings.push((
                                field_pattern.binding,
                                (module_info.module_id, export_name, export_type_id),
                            ));
                        }
                    }
                }
            }
        }
        bindings
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
        let mut test_count = 0usize;
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
                        self.override_generator_return_type(func, func_key);
                    }
                }
                Decl::Tests(_) if self.skip_tests => {}
                Decl::Tests(tests_decl) => {
                    // Declare scoped declarations within the tests block
                    self.declare_tests_scoped_decls(tests_decl, &mut test_count);

                    // Declare each test with a generated name and signature () -> i64
                    let i64_type_id = self.arena().primitives.i64;
                    for _ in &tests_decl.tests {
                        let func_key = self.test_function_key(test_count);
                        let func_name = self.test_display_name(func_key);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        let func_id = self.jit.declare_function(&func_name, &sig);
                        self.func_registry.set_return_type(func_key, i64_type_id);
                        self.func_registry.set_func_id(func_key, func_id);
                        test_count += 1;
                    }
                }
                Decl::Let(let_stmt) => {
                    // Store global initializer expressions (skip type aliases)
                    if let LetInit::Expr(expr) = &let_stmt.init {
                        self.global_inits
                            .insert(let_stmt.name, Rc::new(expr.clone()));
                    }
                }
                Decl::LetTuple(let_tuple) => {
                    // Handle top-level destructuring imports
                    // Populate global_module_bindings for each destructured name
                    if matches!(&let_tuple.init.kind, ExprKind::Import(_)) {
                        self.register_global_module_bindings(let_tuple);
                    }
                }
                Decl::Class(class) => {
                    self.finalize_class(class, program)?;
                }
                Decl::Interface(_) => {
                    // Interface declarations don't generate code directly
                }
                Decl::Implement(impl_block) => {
                    self.register_implement_block(impl_block);
                }
                Decl::Struct(s) => {
                    self.finalize_struct(s)?;
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
        Ok(())
    }

    /// If `func` is a generator (body contains `yield`, returns `Iterator<T>`),
    /// override its declared return type to `RuntimeIterator(T)`.
    ///
    /// Called during pass 1 so that any function compiled in pass 2 that calls
    /// this generator sees the correct (non-interface) return type.
    fn override_generator_return_type(&mut self, func: &FuncDecl, func_key: FunctionKey) {
        use crate::generator::body_contains_yield;

        let return_type_id = match self.func_registry.return_type(func_key) {
            Some(rt) => rt,
            None => return,
        };

        // Check if the return type is Iterator<T> and extract the element type
        let arena = self.arena();
        let name_table = self.analyzed.name_table();
        let elem_type_id = match arena.unwrap_interface(return_type_id) {
            Some((type_def_id, type_args))
                if name_table.well_known.is_iterator_type_def(type_def_id) =>
            {
                match type_args.first().copied() {
                    Some(e) => e,
                    None => return,
                }
            }
            _ => return,
        };

        if !body_contains_yield(&func.body) {
            return;
        }

        if let Some(runtime_iter_type_id) = arena.lookup_runtime_iterator(elem_type_id) {
            self.func_registry
                .set_return_type(func_key, runtime_iter_type_id);
        }
    }

    /// Second pass: compile function bodies and tests.
    /// Note: Decl::Let globals are handled by inlining their initializers
    /// when referenced (see compile_expr for ExprKind::Identifier).
    fn compile_program_declarations(&mut self, program: &Program) -> CodegenResult<()> {
        let mut test_count = 0usize;
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
                    let query = self.query();
                    let program_module = self.program_module();
                    let name_id = query.function_name_id(program_module, func.name);
                    let has_implicit_generic_info = self
                        .analyzed
                        .entity_registry()
                        .function_by_name(name_id)
                        .map(|func_id| {
                            self.analyzed
                                .entity_registry()
                                .get_function(func_id)
                                .generic_info
                                .is_some()
                        })
                        .unwrap_or(false);
                    if has_implicit_generic_info {
                        continue;
                    }

                    self.compile_function(func)?;
                }
                Decl::Tests(_) if self.skip_tests => {}
                Decl::Tests(tests_decl) => {
                    self.compile_tests(tests_decl, program, &mut test_count)?;
                }
                Decl::Let(_) | Decl::LetTuple(_) => {
                    // Globals are handled during identifier lookup
                    // LetTuple (destructuring imports) don't generate code
                }
                Decl::Class(class) => {
                    self.compile_class_methods(class, program)?;
                }
                Decl::Interface(_) => {
                    // Interface methods are compiled when used via implement blocks
                }
                Decl::Implement(impl_block) => {
                    self.compile_implement_block(impl_block)?;
                }
                Decl::Struct(struct_decl) => {
                    if !struct_decl.methods.is_empty() || struct_decl.statics.is_some() {
                        self.compile_struct_methods(struct_decl, program)?;
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
        Ok(())
    }

    /// Compile the main program body (functions, tests, classes, etc.)
    fn compile_program_body(&mut self, program: &Program) -> CodegenResult<()> {
        // Pre-pass: Register all class names first so they're available for field type resolution
        // This allows classes to reference each other (e.g., Company.ceo: Person?)
        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    self.pre_register_class(class);
                }
                Decl::Struct(s) => {
                    self.pre_register_struct(s);
                }
                Decl::Sentinel(s) => {
                    self.pre_register_sentinel(s);
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

        // Second pass: compile function bodies and tests
        self.compile_program_declarations(program)?;

        // Compile monomorphized instances
        self.compile_all_monomorphized_instances(program)?;

        Ok(())
    }

    /// Compile pure Vole functions from imported modules.
    /// These are functions defined in module files (not external FFI functions).
    /// Declare all module functions, finalize types, and register implement blocks.
    /// Must run before compiling function bodies so cross-module calls can be resolved.
    fn declare_module_types_and_functions(&mut self, module_paths: &[String]) {
        for module_path in module_paths {
            tracing::debug!(module_path, "compile_module_functions: declaring functions");
            let (program, module_interner) = &self.analyzed.module_programs[module_path];

            // Declare pure Vole functions
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    // Skip generic functions - they're declared via monomorphized instances
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    let module_id = self.query().module_id_or_main(module_path);
                    let name_id = function_name_id_with_interner(
                        self.analyzed,
                        module_interner,
                        module_id,
                        func.name,
                    )
                    .expect("INTERNAL: module function: name_id not registered");

                    // Check for implicit generics (structural type params)
                    if self.has_implicit_generic_info(name_id) {
                        continue;
                    }

                    let display_name = self.query().display_name(name_id);
                    self.declare_function_by_name_id(name_id, &display_name, DeclareMode::Declare);
                }
            }

            let module_id = self.query().module_id_or_main(module_path);

            // Finalize module classes (register type metadata, declare methods)
            // MUST happen before implement block registration, which needs type_metadata
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.finalize_module_class(class, module_interner, module_id);
                }
            }

            // Finalize module structs (register type metadata, declare methods)
            for decl in &program.declarations {
                if let Decl::Struct(struct_decl) = decl {
                    self.finalize_module_struct(struct_decl, module_interner, module_id);
                }
            }

            // Register module sentinels (zero-field struct types like Done, nil)
            for decl in &program.declarations {
                if let Decl::Sentinel(sentinel_decl) = decl {
                    self.finalize_module_sentinel(sentinel_decl, module_interner, module_id);
                }
            }

            // Register implement block methods (both instance and static declarations)
            // MUST happen after class finalization so type_metadata is populated
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl {
                    self.register_implement_block_with_interner(
                        impl_block,
                        module_interner,
                        module_id,
                    );
                }
            }
        }
    }

    pub(super) fn compile_module_functions(&mut self) -> CodegenResult<()> {
        // Collect module paths first to avoid borrow issues
        let module_paths: Vec<_> = self.query().module_paths().map(String::from).collect();
        tracing::debug!(
            ?module_paths,
            "compile_module_functions: processing module paths"
        );

        // Pass 1: Declare all functions and finalize types across all modules
        self.declare_module_types_and_functions(&module_paths);

        // Pass 1.5: Declare and compile monomorphized generic instances used by modules.
        self.declare_monomorphized_instances(true)?;
        self.compile_module_monomorphized_instances()?;
        self.compile_module_class_method_monomorphized_instances()?;
        self.compile_module_static_method_monomorphized_instances()?;

        // Pass 2: Compile all function bodies (cross-module calls now resolved)
        for module_path in &module_paths {
            self.compile_module_function_bodies(module_path)?;
        }

        tracing::debug!("compile_module_functions complete");
        Ok(())
    }

    /// Compile all function bodies for a single module.
    fn compile_module_function_bodies(&mut self, module_path: &str) -> CodegenResult<()> {
        tracing::debug!(module_path, "compile_module_functions: compiling bodies");
        let (program, module_interner) = &self.analyzed.module_programs[module_path];

        // Extract module global initializer expressions
        let module_global_inits: FxHashMap<Symbol, Rc<Expr>> = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Let(let_stmt) = decl
                    && let LetInit::Expr(expr) = &let_stmt.init
                {
                    Some((let_stmt.name, Rc::new(expr.clone())))
                } else {
                    None
                }
            })
            .collect();

        // Register destructured import bindings for this module.
        // When a module uses `let { add } = import "./other"`, the binding must
        // be available during compilation of the module's function bodies.
        let module_bindings = Self::extract_module_destructured_bindings(
            self.analyzed,
            program,
            module_interner,
            module_path,
        );
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
                let module_id = self.query().module_id_or_main(module_path);
                let name_id = function_name_id_with_interner(
                    self.analyzed,
                    module_interner,
                    module_id,
                    func.name,
                )
                .expect("INTERNAL: module function: name_id not registered");

                // Check for implicit generics (structural type params)
                let has_implicit_generic_info = self
                    .analyzed
                    .entity_registry()
                    .function_by_name(name_id)
                    .map(|func_id| {
                        self.analyzed
                            .entity_registry()
                            .get_function(func_id)
                            .generic_info
                            .is_some()
                    })
                    .unwrap_or(false);
                if has_implicit_generic_info {
                    continue;
                }

                self.compile_module_function(
                    module_path,
                    name_id,
                    func,
                    module_interner,
                    &module_global_inits,
                )?;
            }
        }

        // Compile implement block methods (both instance and static)
        let module_id = self.query().module_id_or_main(module_path);
        for decl in &program.declarations {
            if let Decl::Implement(impl_block) = decl {
                self.compile_module_implement_block(impl_block, module_interner, module_id)?;
            }
        }

        // Compile module class methods (both instance and static)
        for decl in &program.declarations {
            if let Decl::Class(class) = decl {
                tracing::debug!(class_name = %module_interner.resolve(class.name), "Compiling module class methods");
                self.compile_module_class_methods(
                    class,
                    module_interner,
                    module_path,
                    &module_global_inits,
                )?;
            }
        }

        // Compile module struct methods (both instance and static)
        for decl in &program.declarations {
            if let Decl::Struct(struct_decl) = decl
                && (!struct_decl.methods.is_empty() || struct_decl.statics.is_some())
            {
                tracing::debug!(struct_name = %module_interner.resolve(struct_decl.name), "Compiling module struct methods");
                self.compile_module_struct_methods(
                    struct_decl,
                    module_interner,
                    module_path,
                    &module_global_inits,
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
        let module_paths: Vec<_> = self.query().module_paths().map(String::from).collect();

        for module_path in &module_paths {
            let (program, module_interner) = &self.analyzed.module_programs[module_path];

            // Import pure Vole functions (they're already compiled, just need declarations)
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    let module_id = self.query().module_id_or_main(module_path);
                    let name_id = function_name_id_with_interner(
                        self.analyzed,
                        module_interner,
                        module_id,
                        func.name,
                    )
                    .expect("INTERNAL: module function: name_id not registered");

                    let display_name = self.query().display_name(name_id);
                    let func_key = self.declare_function_by_name_id(
                        name_id,
                        &display_name,
                        DeclareMode::Import,
                    );
                    // Override generator return types for imported module functions
                    if let Some(func_key) = func_key {
                        self.override_generator_return_type(func, func_key);
                    }
                }
            }

            // Finalize module classes (register type metadata, import methods)
            // MUST happen before implement block import, which needs type_metadata
            let module_id = self.query().module_id_or_main(module_path);
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.import_module_class(class, module_interner, module_id);
                }
            }

            // Finalize module structs (register type metadata, import methods)
            for decl in &program.declarations {
                if let Decl::Struct(struct_decl) = decl {
                    self.import_module_struct(struct_decl, module_interner, module_id);
                }
            }

            // Import implement block methods (both instance and static, using Linkage::Import)
            // MUST happen after class finalization so type_metadata is populated
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl {
                    self.import_module_implement_block(impl_block, module_interner, module_id);
                }
            }
        }

        Ok(())
    }

    /// Import a module class - register metadata and import methods.
    /// Used when modules are already compiled in a shared cache.
    fn import_module_class(
        &mut self,
        class: &vole_frontend::ast::ClassDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        // First finalize to get type metadata registered
        self.finalize_module_class(class, module_interner, module_id);

        // The methods are already compiled - they'll be linked via external symbols
        // No additional work needed here since method calls go through func_registry
        // which will find the imported function IDs
    }

    /// Import a module struct - register metadata and import methods.
    /// Used when modules are already compiled in a shared cache.
    fn import_module_struct(
        &mut self,
        struct_decl: &vole_frontend::ast::StructDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        self.finalize_module_struct(struct_decl, module_interner, module_id);
    }

    /// Compile a single module function with its own interner
    fn compile_module_function(
        &mut self,
        module_path: &str,
        name_id: NameId,
        func: &FuncDecl,
        module_interner: &Interner,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        let func_key = self.func_registry.intern_name_id(name_id);
        let display_name = self.query().display_name(name_id);
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("module function", &display_name))?;
        let module_id = self.query().module_id_or_main(module_path);

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .registry()
            .function_by_name(name_id)
            .ok_or_else(|| CodegenError::not_found("function in registry", &display_name))?;
        let (param_type_ids, return_type_id) = {
            let func_def = self.registry().get_function(semantic_func_id);
            (
                func_def.signature.params_id.clone(),
                func_def.signature.return_type_id,
            )
        };

        // Check if this is a generator function (returns Iterator<T> and body contains yield)
        let source_file_ptr = self.source_file_ptr();
        let env = compile_env!(
            self,
            module_interner,
            module_global_inits,
            source_file_ptr,
            module_id
        );
        if let Some(elem_type_id) =
            crate::generator::extract_iterator_element_type(return_type_id, &env)
            && crate::generator::body_contains_yield(&func.body)
        {
            let gen_params = crate::generator::GeneratorParams {
                func,
                jit_func_id,
                wrapper_func_key: func_key,
                param_type_ids: &param_type_ids,
                elem_type_id,
                module_id: Some(module_id),
            };
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
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
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(
                self,
                module_interner,
                module_global_inits,
                source_file_ptr,
                module_id
            );
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let config = FunctionCompileConfig::top_level(&func.body, params, return_type_id);
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
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
        let (func_key, display_name) = self.main_function_key_and_name(func.name);
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("function", &display_name))?;

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .function_id(program_module, func.name)
            .ok_or_else(|| CodegenError::not_found("function in registry", &display_name))?;
        let (param_type_ids, return_type_id) = {
            let func_def = self.registry().get_function(semantic_func_id);
            (
                func_def.signature.params_id.clone(),
                func_def.signature.return_type_id,
            )
        };

        // Check if this is a generator function (returns Iterator<T> and body contains yield)
        let source_file_ptr = self.source_file_ptr();
        let env = compile_env!(self, source_file_ptr);
        if let Some(elem_type_id) =
            crate::generator::extract_iterator_element_type(return_type_id, &env)
            && crate::generator::body_contains_yield(&func.body)
        {
            let gen_params = crate::generator::GeneratorParams {
                func,
                jit_func_id,
                wrapper_func_key: func_key,
                param_type_ids: &param_type_ids,
                elem_type_id,
                module_id: None,
            };
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
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
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            // Use pre-resolved return type (None for void)
            let return_type_opt = Some(return_type_id).filter(|id| !id.is_void());
            let config = FunctionCompileConfig::top_level(&func.body, params, return_type_opt);
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        // Define the function
        self.finalize_function(jit_func_id)?;

        Ok(())
    }
}
