use std::io::Write;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};

use super::common::{
    DefaultReturn, FunctionCompileConfig, compile_function_inner_with_params,
    finalize_function_body,
};
use super::{Compiler, TestInfo};

use crate::FunctionKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, CompileEnv, function_name_id_with_interner, type_id_to_cranelift};
use vole_frontend::{
    Block, Decl, Expr, ExprKind, FuncDecl, InterfaceMethod, Interner, LetInit, LetTupleStmt,
    PatternKind, Program, Span, Stmt, Symbol, TestCase, TestsDecl, TypeExpr,
};
use vole_identity::{ModuleId, NameId};
use vole_sema::generic::{
    ClassMethodMonomorphInstance, MonomorphInstance, MonomorphInstanceTrait,
    StaticMethodMonomorphInstance,
};
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

    fn test_function_key(&mut self, test_index: usize) -> FunctionKey {
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

    fn test_display_name(&self, func_key: FunctionKey) -> String {
        self.func_registry.display(func_key)
    }

    /// Register global module bindings from a top-level destructuring import.
    /// This extracts module exports from the pattern and stores them in global_module_bindings.
    fn register_global_module_bindings(&mut self, let_tuple: &LetTupleStmt, _import_path: &str) {
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

    /// Compile the main program body (functions, tests, classes, etc.)
    fn compile_program_body(&mut self, program: &Program) -> CodegenResult<()> {
        // Count total tests to assign unique IDs
        let mut test_count = 0usize;

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
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Skip generic functions - they're templates, not actual functions
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    // Get FunctionId and build signature from pre-resolved types
                    let program_module = self.program_module();
                    let Some(semantic_func_id) =
                        self.query().function_id(program_module, func.name)
                    else {
                        continue; // Skip if function not registered (shouldn't happen)
                    };
                    let sig = self.build_signature_for_function(semantic_func_id);
                    let (func_key, display_name) = self.main_function_key_and_name(func.name);
                    let jit_func_id = self.jit.declare_function(&display_name, &sig);
                    self.func_registry.set_func_id(func_key, jit_func_id);
                    // Record return type for use in call expressions (TypeId-native)
                    let return_type_id = self
                        .query()
                        .registry()
                        .get_function(semantic_func_id)
                        .signature
                        .return_type_id;
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
                Decl::Tests(_) if self.skip_tests => {}
                Decl::Tests(tests_decl) => {
                    // Declare scoped declarations within the tests block
                    self.declare_tests_scoped_decls(tests_decl, program, &mut test_count);

                    // Declare each test with a generated name and signature () -> i64
                    let i64_type_id = self.analyzed.type_arena().primitives.i64;
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
                    if let ExprKind::Import(import_path) = &let_tuple.init.kind {
                        self.register_global_module_bindings(let_tuple, import_path);
                    }
                }
                Decl::Class(class) => {
                    self.finalize_class(class, program);
                }
                Decl::Interface(_) => {
                    // Interface declarations don't generate code directly
                }
                Decl::Implement(impl_block) => {
                    self.register_implement_block(impl_block);
                }
                Decl::Struct(s) => {
                    self.finalize_struct(s);
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

        // Reset counter for second pass
        test_count = 0;

        // Initialize monomorphized type_id counter from pass 1's next_type_id.
        // This ensures dynamically allocated type_ids for generic instantiations
        // don't collide with statically registered type_ids from pass 1.
        self.state.mono_type_id_counter.set(self.next_type_id);

        // Declare monomorphized function instances before second pass
        self.declare_all_monomorphized_instances(program)?;

        // Second pass: compile function bodies and tests
        // Note: Decl::Let globals are handled by inlining their initializers
        // when referenced (see compile_expr for ExprKind::Identifier)
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

        // Compile monomorphized instances
        self.compile_all_monomorphized_instances(program)?;

        Ok(())
    }

    /// Compile pure Vole functions from imported modules.
    /// These are functions defined in module files (not external FFI functions).
    fn compile_module_functions(&mut self) -> CodegenResult<()> {
        // Collect module paths first to avoid borrow issues
        let module_paths: Vec<_> = self.query().module_paths().map(String::from).collect();
        tracing::debug!(
            ?module_paths,
            "compile_module_functions: processing module paths"
        );

        // ============================================
        // PASS 1: Declare ALL functions across ALL modules
        // This ensures cross-module calls can be resolved
        // ============================================
        for module_path in &module_paths {
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
                    .expect("module function name_id should be registered");

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

                    let display_name = self.query().display_name(name_id);

                    // Get FunctionId and build signature from pre-resolved types
                    let Some(semantic_func_id) = self.query().registry().function_by_name(name_id)
                    else {
                        continue; // Skip if function not registered
                    };
                    let sig = self.build_signature_for_function(semantic_func_id);
                    let jit_func_id = self.jit.declare_function(&display_name, &sig);
                    let func_key = self.func_registry.intern_name_id(name_id);
                    self.func_registry.set_func_id(func_key, jit_func_id);

                    // Record return type from pre-resolved signature
                    let return_type_id = self
                        .query()
                        .registry()
                        .get_function(semantic_func_id)
                        .signature
                        .return_type_id;
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
            }

            // Register implement block methods (both instance and static declarations)
            {
                let module_id = self.query().module_id_or_main(module_path);
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

            // Get module ID for type resolution
            let module_id = self.query().module_id_or_main(module_path);

            // Finalize module classes (register type metadata, declare methods)
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
        }

        // ============================================
        // PASS 2: Compile ALL function bodies across ALL modules
        // Now all functions are declared, so cross-module calls work
        // ============================================
        for module_path in &module_paths {
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
                    .expect("module function name_id should be registered");

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
                    self.compile_module_implement_block(
                        impl_block,
                        module_interner,
                        module_id,
                        Some(module_path),
                    )?;
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
        }

        tracing::debug!("compile_module_functions complete");
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
                    .expect("module function name_id should be registered");
                    let display_name = self.query().display_name(name_id);

                    // Get FunctionId and build signature from pre-resolved types
                    let Some(semantic_func_id) = self.query().registry().function_by_name(name_id)
                    else {
                        continue; // Skip if function not registered
                    };
                    // Create signature and IMPORT (not declare) the function
                    let sig = self.build_signature_for_function(semantic_func_id);
                    let jit_func_id = self.jit.import_function(&display_name, &sig);
                    let func_key = self.func_registry.intern_name_id(name_id);
                    self.func_registry.set_func_id(func_key, jit_func_id);

                    // Record return type from pre-resolved signature
                    let return_type_id = self
                        .query()
                        .registry()
                        .get_function(semantic_func_id)
                        .signature
                        .return_type_id;
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
            }

            // Import implement block methods (both instance and static, using Linkage::Import)
            let module_id_for_impl = self.query().module_id_or_main(module_path);
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl {
                    self.import_module_implement_block(
                        impl_block,
                        module_interner,
                        module_id_for_impl,
                    );
                }
            }

            // Finalize module classes (register type metadata, import methods)
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
        }

        Ok(())
    }

    /// Import a module class - register metadata and import methods.
    /// Used when modules are already compiled in a shared cache.
    fn import_module_class(
        &mut self,
        class: &vole_frontend::ClassDecl,
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
        struct_decl: &vole_frontend::StructDecl,
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
            .ok_or_else(|| format!("Module function {} not declared", display_name))?;
        let module_id = self.query().module_id_or_main(module_path);

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .registry()
            .function_by_name(name_id)
            .ok_or_else(|| format!("Function {} not found in registry", display_name))?;
        let (param_type_ids, return_type_id) = {
            let func_def = self.query().registry().get_function(semantic_func_id);
            (
                func_def.signature.params_id.clone(),
                func_def.signature.return_type_id,
            )
        };
        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Combine AST param names with pre-resolved TypeIds from FunctionDef
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
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

        // Get source file pointer
        let source_file_ptr = self.source_file_ptr();

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

    fn compile_function(&mut self, func: &FuncDecl) -> CodegenResult<()> {
        let program_module = self.program_module();
        let (func_key, display_name) = self.main_function_key_and_name(func.name);
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Function {} not declared", display_name))?;

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .function_id(program_module, func.name)
            .ok_or_else(|| format!("Function {} not found in registry", display_name))?;
        let (param_type_ids, return_type_id) = {
            let func_def = self.query().registry().get_function(semantic_func_id);
            (
                func_def.signature.params_id.clone(),
                func_def.signature.return_type_id,
            )
        };

        // Create function signature from pre-resolved types
        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Combine AST param names with pre-resolved TypeIds from FunctionDef
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
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

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

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

    /// Compile all tests in a tests block
    fn compile_tests(
        &mut self,
        tests_decl: &TestsDecl,
        program: &Program,
        test_count: &mut usize,
    ) -> CodegenResult<()> {
        // Phase 1: Compile scoped function/class bodies (and nested tests)
        self.compile_tests_scoped_bodies(tests_decl, program, test_count)?;

        // Collect scoped let declarations (Let and LetTuple) for compiling in each test
        let scoped_let_stmts: Vec<Stmt> = tests_decl
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::Let(let_stmt) => Some(Stmt::Let(let_stmt.clone())),
                Decl::LetTuple(let_tuple) => Some(Stmt::LetTuple(let_tuple.clone())),
                _ => None,
            })
            .collect();

        // Phase 2: Compile each test
        for test in &tests_decl.tests {
            let func_key = self.test_function_key(*test_count);
            let func_name = self.test_display_name(func_key);
            let func_id = self
                .func_registry
                .func_id(func_key)
                .ok_or_else(|| format!("Test {} not declared", func_name))?;

            // Create function signature: () -> i64
            let sig = self.jit.create_signature(&[], Some(types::I64));
            self.jit.ctx.func.signature = sig;

            // Get source file pointer before borrowing ctx.func
            let source_file_ptr = self.source_file_ptr();

            // Create function builder
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

                let entry_block = builder.create_block();
                builder.switch_to_block(entry_block);

                // Create split contexts
                let env = compile_env!(self, source_file_ptr);
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                // Compile scoped let declarations and test body
                let mut cg = Cg::new(&mut builder, &mut codegen_ctx, &env);

                // Push function-level RC scope for test body
                cg.push_rc_scope();

                if !scoped_let_stmts.is_empty() {
                    // Create a synthetic block with the let statements
                    let let_block = Block {
                        stmts: scoped_let_stmts.clone(),
                        span: Span::default(),
                    };
                    cg.block(&let_block)?;
                }

                // Compile test body
                // Note: For FuncBody::Expr, terminated=true but the block isn't actually
                // terminated (no return instruction). For FuncBody::Block, terminated=true
                // only if there's an explicit return/break. So we check both.
                let (block_terminated, expr_value) = cg.compile_body(&test.body)?;

                // Tests always return 0. Add return if block didn't explicitly terminate
                // or if it's an expression body.
                let terminated = block_terminated && expr_value.is_none();

                // Emit RC cleanup for test-level scope
                if !terminated {
                    cg.pop_rc_scope_with_cleanup(None)?;
                } else {
                    cg.rc_scopes.pop_scope();
                }

                finalize_function_body(builder, None, terminated, DefaultReturn::ZeroI64);
            }

            // Define the function
            self.finalize_function(func_id)?;

            // Record test metadata
            let line = test.span.line;
            self.tests.push(TestInfo {
                name: test.name.clone(),
                func_key,
                func_id,
                file: self.source_file_str(),
                line,
            });

            *test_count += 1;
        }

        Ok(())
    }

    /// Declare scoped declarations within a tests block (pass 1).
    /// Handles scoped functions, records, and classes so they're available
    /// during test compilation.
    fn declare_tests_scoped_decls(
        &mut self,
        tests_decl: &TestsDecl,
        _program: &Program,
        test_count: &mut usize,
    ) {
        let program_module = self.program_module();
        let interner = &self.analyzed.interner;

        // Look up the virtual module ID for scoped type declarations
        let virtual_module_id = self.query().tests_virtual_module(tests_decl.span);

        for inner_decl in &tests_decl.decls {
            match inner_decl {
                Decl::Function(func) => {
                    // Skip generic functions
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    // Scoped functions are registered under the program module by sema
                    let Some(semantic_func_id) =
                        self.query().function_id(program_module, func.name)
                    else {
                        continue;
                    };
                    let sig = self.build_signature_for_function(semantic_func_id);
                    let (func_key, display_name) = self.main_function_key_and_name(func.name);
                    let jit_func_id = self.jit.declare_function(&display_name, &sig);
                    self.func_registry.set_func_id(func_key, jit_func_id);
                    let return_type_id = self
                        .query()
                        .registry()
                        .get_function(semantic_func_id)
                        .signature
                        .return_type_id;
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
                Decl::Class(class) => {
                    // Scoped classes are registered under the virtual module
                    if let Some(vm_id) = virtual_module_id {
                        self.finalize_module_class(class, interner, vm_id);
                    }
                }
                Decl::Implement(impl_block) => {
                    // Scoped implement blocks target types under the virtual module
                    if let Some(vm_id) = virtual_module_id {
                        self.register_implement_block_in_module(impl_block, vm_id);
                    } else {
                        self.register_implement_block(impl_block);
                    }
                }
                Decl::Tests(nested_tests) => {
                    // Recursively declare nested tests block scoped decls
                    self.declare_tests_scoped_decls(nested_tests, _program, test_count);

                    // Declare each nested test with a generated name and signature () -> i64
                    let i64_type_id = self.analyzed.type_arena().primitives.i64;
                    for _ in &nested_tests.tests {
                        let func_key = self.test_function_key(*test_count);
                        let func_name = self.test_display_name(func_key);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        let func_id = self.jit.declare_function(&func_name, &sig);
                        self.func_registry.set_return_type(func_key, i64_type_id);
                        self.func_registry.set_func_id(func_key, func_id);
                        *test_count += 1;
                    }
                }
                _ => {
                    // Let declarations, interfaces, etc. don't need pass 1 handling
                }
            }
        }
    }

    /// Compile scoped function and method bodies within a tests block (pass 2).
    fn compile_tests_scoped_bodies(
        &mut self,
        tests_decl: &TestsDecl,
        program: &Program,
        test_count: &mut usize,
    ) -> CodegenResult<()> {
        let program_module = self.program_module();
        // Scoped types are registered under the virtual module in sema
        let virtual_module_id = self
            .query()
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
                    let query = self.query();
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
                    // Compile as a regular function
                    self.compile_function(func)?;
                }
                Decl::Class(class) => {
                    self.compile_class_methods_in_module(class, program, virtual_module_id)?;
                }
                Decl::Implement(impl_block) => {
                    self.compile_implement_block_in_module(impl_block, virtual_module_id)?;
                }
                Decl::Tests(nested_tests) => {
                    // Recursively compile nested tests blocks
                    self.compile_tests(nested_tests, program, test_count)?;
                }
                _ => {
                    // Let declarations are handled during test body compilation
                }
            }
        }
        Ok(())
    }

    /// Compile program to CLIF IR and write to the given writer.
    /// Does not finalize for execution - just generates IR for inspection.
    pub fn compile_to_ir<W: Write>(
        &mut self,
        program: &Program,
        writer: &mut W,
        include_tests: bool,
    ) -> CodegenResult<()> {
        // Compile module functions first (prelude, imports) so module variables are available
        self.compile_module_functions()?;

        let program_module = self.program_module();
        // First pass: declare all functions so they can reference each other
        let mut test_count = 0usize;
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Get FunctionId and build signature from pre-resolved types
                    let Some(semantic_func_id) =
                        self.query().function_id(program_module, func.name)
                    else {
                        continue; // Skip if function not registered
                    };
                    let sig = self.build_signature_for_function(semantic_func_id);
                    let (func_key, display_name) = self.main_function_key_and_name(func.name);
                    let jit_func_id = self.jit.declare_function(&display_name, &sig);
                    self.func_registry.set_func_id(func_key, jit_func_id);
                    // Record return type from pre-resolved signature
                    let return_type_id = self
                        .query()
                        .registry()
                        .get_function(semantic_func_id)
                        .signature
                        .return_type_id;
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
                Decl::Tests(tests_decl) if include_tests => {
                    let i64_type_id = self.analyzed.type_arena().primitives.i64;
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
                    // Store global initializer expressions so module variables are available
                    if let LetInit::Expr(expr) = &let_stmt.init {
                        self.global_inits
                            .insert(let_stmt.name, Rc::new(expr.clone()));
                    }
                }
                Decl::LetTuple(let_tuple) => {
                    // Handle top-level destructuring imports
                    if let ExprKind::Import(import_path) = &let_tuple.init.kind {
                        self.register_global_module_bindings(let_tuple, import_path);
                    }
                }
                _ => {}
            }
        }

        // Second pass: build and emit IR for each function
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let name = self.analyzed.interner.resolve(func.name);
                    self.build_function_ir(func)?;
                    writeln!(writer, "// func {}", name).map_err(|e| {
                        CodegenError::internal_with_context("io error", e.to_string())
                    })?;
                    writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| {
                        CodegenError::internal_with_context("io error", e.to_string())
                    })?;
                    self.jit.clear();
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for test in &tests_decl.tests {
                        self.build_test_ir(test)?;
                        writeln!(writer, "// test \"{}\"", test.name).map_err(|e| {
                            CodegenError::internal_with_context("io error", e.to_string())
                        })?;
                        writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| {
                            CodegenError::internal_with_context("io error", e.to_string())
                        })?;
                        self.jit.clear();
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Build IR for a single function without defining it.
    /// Similar to compile_function but doesn't call define_function.
    fn build_function_ir(&mut self, func: &FuncDecl) -> CodegenResult<()> {
        let program_module = self.program_module();

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .function_id(program_module, func.name)
            .ok_or_else(|| {
                format!(
                    "Function '{}' not found in registry",
                    self.analyzed.interner.resolve(func.name)
                )
            })?;
        let (param_type_ids, return_type_id) = {
            let func_def = self.query().registry().get_function(semantic_func_id);
            (
                func_def.signature.params_id.clone(),
                func_def.signature.return_type_id,
            )
        };

        // Create function signature from pre-resolved types
        let sig = self.build_signature_for_function(semantic_func_id);
        self.jit.ctx.func.signature = sig;

        // Combine AST param names with pre-resolved TypeIds
        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = func
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Get function return type id from pre-resolved signature
        let return_type_id = Some(return_type_id).filter(|id| !id.is_void());

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &self.global_inits,
                source_file_ptr,
                current_module: None,
                global_module_bindings: &self.global_module_bindings,
            };
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let config = FunctionCompileConfig::top_level(&func.body, params, return_type_id);
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        // NOTE: We intentionally do NOT call define_function here.
        // This method is for IR inspection only.

        // Run CFG cleanup to show optimized IR
        crate::cfg_cleanup::cleanup_cfg(&mut self.jit.ctx.func);

        // Run loop parameter optimization if enabled
        if self.jit.loop_param_opt_enabled() {
            crate::loop_param_opt::optimize_loop_params(&mut self.jit.ctx.func);
        }

        Ok(())
    }

    /// Build IR for a single test case without defining it.
    /// Similar to test compilation in compile_tests but doesn't call define_function.
    fn build_test_ir(&mut self, test: &TestCase) -> CodegenResult<()> {
        // Create function signature: () -> i64
        let sig = self.jit.create_signature(&[], Some(types::I64));
        self.jit.ctx.func.signature = sig;

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.switch_to_block(entry_block);

            // Compile test body (no parameters, no return type)
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &self.global_inits,
                source_file_ptr,
                current_module: None,
                global_module_bindings: &self.global_module_bindings,
            };
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
            let (terminated, _) =
                Cg::new(&mut builder, &mut codegen_ctx, &env).compile_body(&test.body)?;

            finalize_function_body(builder, None, terminated, DefaultReturn::ZeroI64);
        }

        // NOTE: We intentionally do NOT call define_function here.
        // This method is for IR inspection only.

        // Run CFG cleanup to show optimized IR
        crate::cfg_cleanup::cleanup_cfg(&mut self.jit.ctx.func);

        // Run loop parameter optimization if enabled
        if self.jit.loop_param_opt_enabled() {
            crate::loop_param_opt::optimize_loop_params(&mut self.jit.ctx.func);
        }

        Ok(())
    }

    /// Declare a single monomorphized instance using the common trait interface.
    /// `has_self_param` indicates if a self pointer should be prepended to parameters.
    fn declare_monomorph_instance<T: MonomorphInstanceTrait>(
        &mut self,
        instance: &T,
        has_self_param: bool,
    ) {
        let mangled_name = self.query().display_name(instance.mangled_name());
        let func_type = instance.func_type();

        // Get TypeId versions of params and return type
        let param_type_ids: Vec<TypeId> = func_type.params_id.to_vec();
        let return_type_id = func_type.return_type_id;

        // Create signature from the concrete function type (TypeId-native)
        let mut params = if has_self_param {
            vec![self.pointer_type]
        } else {
            Vec::new()
        };
        params.extend(self.type_ids_to_cranelift(&param_type_ids));
        let ret = self.return_type_to_cranelift(return_type_id);

        let sig = self.jit.create_signature(&params, ret);
        let func_id = self.jit.declare_function(&mangled_name, &sig);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name());
        self.func_registry.set_func_id(func_key, func_id);

        // Record return type for call expressions
        self.func_registry.set_return_type(func_key, return_type_id);
    }

    /// Declare all monomorphized function instances
    fn declare_monomorphized_instances(&mut self) -> CodegenResult<()> {
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

            self.declare_monomorph_instance(&instance, false);
        }

        Ok(())
    }

    /// Compile all monomorphized function instances
    fn compile_monomorphized_instances(&mut self, program: &Program) -> CodegenResult<()> {
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

        // Compile with the module's interner and context
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Monomorphized function {} not declared", mangled_name))?;

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

        let ret = self.return_type_to_cranelift(return_type_id);
        let sig = self.jit.create_signature(&param_cranelift_types, ret);
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
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let config = FunctionCompileConfig::top_level(&func.body, params, Some(return_type_id));
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
            .ok_or_else(|| format!("Monomorphized function {} not declared", mangled_name))?;

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

        // Create function signature from concrete types
        let ret = self.return_type_to_cranelift(return_type_id);
        let sig = self.jit.create_signature(&param_cranelift_types, ret);
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

    /// Declare all monomorphized class method instances
    fn declare_class_method_monomorphized_instances(&mut self) -> CodegenResult<()> {
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

            // Class methods have self parameter
            self.declare_monomorph_instance(&instance, true);
        }

        Ok(())
    }

    /// Compile all monomorphized class method instances
    fn compile_class_method_monomorphized_instances(
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
                    self.compile_monomorphized_class_method(method, &instance)?;
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
                self.compile_monomorphized_class_method(method, &instance)?;
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

    /// Compile a single monomorphized class method instance
    fn compile_monomorphized_class_method(
        &mut self,
        method: &FuncDecl,
        instance: &ClassMethodMonomorphInstance,
    ) -> CodegenResult<()> {
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Monomorphized class method {} not declared", mangled_name))?;

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

        // Create method signature (self + params) with concrete types
        let mut sig_params = vec![self.pointer_type]; // self
        sig_params.extend_from_slice(&param_cranelift_types);
        let ret = self.return_type_to_cranelift(return_type_id);
        let sig = self.jit.create_signature(&sig_params, ret);
        self.jit.ctx.func.signature = sig;

        // Use pre-computed self type from sema
        let self_type_id = instance.self_type;
        let self_sym = self.self_symbol();
        let self_binding = (self_sym, self_type_id, self.pointer_type);

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

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
                None,
                Some(&instance.substitutions),
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Declare all monomorphized static method instances
    fn declare_static_method_monomorphized_instances(&mut self) -> CodegenResult<()> {
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
            // Static methods don't have self parameter
            self.declare_monomorph_instance(&instance, false);
        }

        Ok(())
    }

    /// Compile all monomorphized static method instances
    fn compile_static_method_monomorphized_instances(
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
            let class_name_str = self.query().display_name(instance.class_name);
            tracing::debug!(
                class_name = %class_name_str,
                class_name_id = ?instance.class_name,
                method_name = ?instance.method_name,
                "looking for static method to compile"
            );

            // Try to find the static method in a class
            if let Some(class) = class_asts.get(&instance.class_name)
                && let Some(ref statics) = class.statics
            {
                let method_name_str = self.query().display_name(instance.method_name);
                let method = statics
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_static_method(method, &instance)?;
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

    /// Compile a single monomorphized static method instance
    fn compile_monomorphized_static_method(
        &mut self,
        method: &InterfaceMethod,
        instance: &StaticMethodMonomorphInstance,
    ) -> CodegenResult<()> {
        let mangled_name = self.query().display_name(instance.mangled_name);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Monomorphized static method {} not declared", mangled_name))?;

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

        // Create signature (no self parameter) with concrete types
        let ret = self.return_type_to_cranelift(return_type_id);
        let sig = self.jit.create_signature(&param_cranelift_types, ret);
        self.jit.ctx.func.signature = sig;

        // Get method body
        let body = method
            .body
            .as_ref()
            .ok_or_else(|| format!("Internal error: static method {} has no body", mangled_name))?;

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let config = FunctionCompileConfig::top_level(body, params, Some(return_type_id));
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

    /// Build maps of generic class NameIds to their AST declarations.
    /// Used by both class method and static method monomorphization.
    /// Recursively walks into tests blocks to find generic classes declared there.
    fn build_generic_type_asts<'a>(
        &self,
        program: &'a Program,
    ) -> FxHashMap<NameId, &'a vole_frontend::ClassDecl> {
        let mut result = FxHashMap::default();
        let program_module = self.program_module();
        self.collect_generic_class_asts(&program.declarations, program_module, &mut result);
        result
    }

    /// Recursively collect generic class ASTs from declarations, including tests blocks.
    fn collect_generic_class_asts<'a>(
        &self,
        decls: &'a [Decl],
        module_id: ModuleId,
        result: &mut FxHashMap<NameId, &'a vole_frontend::ClassDecl>,
    ) {
        for decl in decls {
            match decl {
                Decl::Class(class) if !class.type_params.is_empty() => {
                    let query = self.query();
                    if let Some(name_id) = query.try_name_id(module_id, &[class.name]) {
                        result.insert(name_id, class);
                    }
                }
                Decl::Tests(tests_decl) => {
                    // Use the virtual module for tests-block-scoped types
                    let vm_id = self
                        .query()
                        .tests_virtual_module(tests_decl.span)
                        .unwrap_or(module_id);
                    self.collect_generic_class_asts(&tests_decl.decls, vm_id, result);
                }
                _ => {}
            }
        }
    }

    /// Find a method in implement blocks targeting a generic class.
    /// Searches through all declarations (including tests blocks) for implement blocks
    /// whose target type matches the given class NameId and returns the matching method.
    fn find_implement_block_method<'a>(
        &self,
        decls: &'a [Decl],
        class_name_id: NameId,
        method_name_str: &str,
        module_id: ModuleId,
    ) -> Option<&'a FuncDecl> {
        for decl in decls {
            match decl {
                Decl::Implement(impl_block) => {
                    // Get the base type name from the target type
                    let target_sym = match &impl_block.target_type {
                        TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => Some(*sym),
                        _ => None,
                    };
                    if let Some(sym) = target_sym {
                        let query = self.query();
                        if let Some(name_id) = query.try_name_id(module_id, &[sym])
                            && name_id == class_name_id
                        {
                            // Found matching implement block - search its methods
                            if let Some(method) = impl_block
                                .methods
                                .iter()
                                .find(|m| self.query().resolve_symbol(m.name) == method_name_str)
                            {
                                return Some(method);
                            }
                        }
                    }
                }
                Decl::Tests(tests_decl) => {
                    let vm_id = self
                        .query()
                        .tests_virtual_module(tests_decl.span)
                        .unwrap_or(module_id);
                    // Search both the parent module and virtual module for implement blocks
                    if let Some(method) = self.find_implement_block_method(
                        &tests_decl.decls,
                        class_name_id,
                        method_name_str,
                        vm_id,
                    ) {
                        return Some(method);
                    }
                    // Also try with the parent module_id (implement blocks may target
                    // types from the parent module)
                    if vm_id != module_id
                        && let Some(method) = self.find_implement_block_method(
                            &tests_decl.decls,
                            class_name_id,
                            method_name_str,
                            module_id,
                        )
                    {
                        return Some(method);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Recursively collect generic function ASTs from declarations, including tests blocks.
    /// Generic functions inside tests blocks are registered under the program module
    /// (not the virtual module), but their ASTs are only reachable by walking into tests blocks.
    fn collect_generic_func_asts<'a>(
        &self,
        decls: &'a [Decl],
        module_id: ModuleId,
        result: &mut FxHashMap<NameId, &'a FuncDecl>,
    ) {
        for decl in decls {
            match decl {
                Decl::Function(func) => {
                    let query = self.query();
                    let name_id = query.function_name_id(module_id, func.name);

                    // Check if function has explicit type params OR implicit generic_info
                    let has_explicit_type_params = !func.type_params.is_empty();
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

                    if has_explicit_type_params || has_implicit_generic_info {
                        result.insert(name_id, func);
                    }
                }
                Decl::Tests(tests_decl) => {
                    // Functions in tests blocks are registered under the program module
                    // (not the virtual module), so keep using the same module_id.
                    self.collect_generic_func_asts(&tests_decl.decls, module_id, result);
                }
                _ => {}
            }
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Unified monomorphization entry points
    // ═══════════════════════════════════════════════════════════════════════

    /// Declare all monomorphized instances (functions, class methods, static methods)
    fn declare_all_monomorphized_instances(&mut self, _program: &Program) -> CodegenResult<()> {
        // Note: Nested generic calls are now discovered during sema analysis,
        // so we don't need to expand instances here.
        self.declare_monomorphized_instances()?;
        self.declare_class_method_monomorphized_instances()?;
        self.declare_static_method_monomorphized_instances()?;
        Ok(())
    }

    /// Compile all monomorphized instances (functions, class methods, static methods)
    fn compile_all_monomorphized_instances(&mut self, program: &Program) -> CodegenResult<()> {
        self.compile_monomorphized_instances(program)?;
        self.compile_class_method_monomorphized_instances(program)?;
        self.compile_static_method_monomorphized_instances(program)?;
        Ok(())
    }
}
