use rustc_hash::FxHashMap;
use std::io::Write;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};
use cranelift_module::{FuncId, Module};

use super::common::{
    DefaultReturn, FunctionCompileConfig, compile_function_inner_with_params,
    finalize_function_body,
};
use super::{Compiler, TestInfo};

use crate::FunctionKey;
use crate::RuntimeFn;
use crate::context::Cg;
use crate::types::{CodegenCtx, CompileEnv, function_name_id_with_interner, type_id_to_cranelift};
use vole_frontend::{
    Block, Decl, Expr, ExprKind, FuncDecl, InterfaceMethod, Interner, LetInit, LetStmt,
    LetTupleStmt, PatternKind, Program, Span, Stmt, Symbol, TestCase, TestsDecl,
};
use vole_identity::{ModuleId, NameId};
use vole_sema::generic::{
    ClassMethodMonomorphInstance, MonomorphInstance, MonomorphInstanceTrait,
    StaticMethodMonomorphInstance,
};
use vole_sema::type_arena::TypeId;

/// Information about a compiled scoped function, used to make it available in tests
struct ScopedFuncInfo {
    /// The function's name (Symbol) for looking up in variables
    name: Symbol,
    /// The compiled function ID
    func_id: FuncId,
    /// The closure function type (pre-computed by sema)
    func_type_id: TypeId,
}

impl Compiler<'_> {
    fn main_function_key_and_name(&mut self, sym: Symbol) -> (FunctionKey, String) {
        // Collect info using query (immutable borrow)
        let (name_id, display_name) = {
            let query = self.query();
            (
                query.try_function_name_id(query.main_module(), sym),
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

        // Extract bindings from the record pattern
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
    pub fn compile_program(&mut self, program: &Program) -> Result<(), String> {
        // Compile module functions first (before main program)
        self.compile_module_functions()?;
        self.compile_program_body(program)
    }

    /// Compile only module functions (prelude, imports).
    /// Call this once before compile_program_only for batched compilation.
    pub fn compile_modules_only(&mut self) -> Result<(), String> {
        self.compile_module_functions()
    }

    /// Import pre-compiled module functions without compiling them.
    /// Use this when modules were already compiled in a shared CompiledModules cache.
    pub fn import_modules(&mut self) -> Result<(), String> {
        self.import_module_functions()
    }

    /// Compile a program without recompiling module functions.
    /// Use with compile_modules_only for batched compilation.
    pub fn compile_program_only(&mut self, program: &Program) -> Result<(), String> {
        self.compile_program_body(program)
    }

    /// Compile the main program body (functions, tests, classes, etc.)
    fn compile_program_body(&mut self, program: &Program) -> Result<(), String> {
        // Count total tests to assign unique IDs
        let mut test_count = 0usize;

        // Pre-pass: Register all record/class names first so they're available for field type resolution
        // This allows records to reference each other (e.g., Company.ceo: Person?)
        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    self.pre_register_class(class);
                }
                Decl::Record(record) => {
                    self.pre_register_record(record);
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
                    let main_module = self.query().main_module();
                    let Some(semantic_func_id) = self.query().function_id(main_module, func.name)
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
                Decl::Tests(tests_decl) => {
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
                        self.global_inits.insert(let_stmt.name, expr.clone());
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
                Decl::Record(record) => {
                    self.finalize_record(record, program);
                }
                Decl::Interface(_) => {
                    // Interface declarations don't generate code directly
                }
                Decl::Implement(impl_block) => {
                    self.register_implement_block(impl_block);
                }
                Decl::Error(_) => {
                    // Error declarations don't generate code in pass 1
                }
                Decl::External(_) => {
                    // External blocks don't generate code in pass 1
                }
            }
        }

        // Reset counter for second pass
        test_count = 0;

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
                    let name_id = query.function_name_id(query.main_module(), func.name);
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
                Decl::Tests(tests_decl) => {
                    self.compile_tests(tests_decl, &mut test_count)?;
                }
                Decl::Let(_) | Decl::LetTuple(_) => {
                    // Globals are handled during identifier lookup
                    // LetTuple (destructuring imports) don't generate code
                }
                Decl::Class(class) => {
                    self.compile_class_methods(class, program)?;
                }
                Decl::Record(record) => {
                    self.compile_record_methods(record, program)?;
                }
                Decl::Interface(_) => {
                    // Interface methods are compiled when used via implement blocks
                }
                Decl::Implement(impl_block) => {
                    self.compile_implement_block(impl_block)?;
                }
                Decl::Error(_) => {
                    // Error declarations don't generate code in pass 2
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
    fn compile_module_functions(&mut self) -> Result<(), String> {
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

            // Register static methods from implement blocks (declarations only)
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl
                    && impl_block.statics.is_some()
                {
                    self.register_implement_statics_only_with_interner(impl_block, module_interner);
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

            // Finalize module records (register type metadata, declare methods)
            for decl in &program.declarations {
                if let Decl::Record(record) = decl {
                    self.finalize_module_record(record, module_interner, module_id);
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
            let module_global_inits: FxHashMap<Symbol, Expr> = program
                .declarations
                .iter()
                .filter_map(|decl| {
                    if let Decl::Let(let_stmt) = decl
                        && let LetInit::Expr(expr) = &let_stmt.init
                    {
                        Some((let_stmt.name, expr.clone()))
                    } else {
                        None
                    }
                })
                .collect();

            // Compile pure Vole function bodies
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
                    self.compile_module_function(
                        module_path,
                        name_id,
                        func,
                        module_interner,
                        &module_global_inits,
                    )?;
                }
            }

            // Compile implement block static methods
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl
                    && impl_block.statics.is_some()
                {
                    self.compile_implement_statics_only(
                        impl_block,
                        Some(module_path),
                        module_interner,
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

            // Compile module record methods (both instance and static)
            for decl in &program.declarations {
                if let Decl::Record(record) = decl {
                    tracing::debug!(record_name = %module_interner.resolve(record.name), "Compiling module record methods");
                    self.compile_module_record_methods(
                        record,
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
    fn import_module_functions(&mut self) -> Result<(), String> {
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

            // Import implement block statics (using Linkage::Import for pre-compiled modules)
            // Note: Instance methods are handled through external dispatch, only statics need importing
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl
                    && impl_block.statics.is_some()
                {
                    self.import_implement_statics_only_with_interner(impl_block, module_interner);
                }
            }

            // Finalize module classes (register type metadata, import methods)
            let module_id = self.query().module_id_or_main(module_path);
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.import_module_class(class, module_interner, module_id);
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

    /// Compile a single module function with its own interner
    fn compile_module_function(
        &mut self,
        module_path: &str,
        name_id: NameId,
        func: &FuncDecl,
        module_interner: &Interner,
        module_global_inits: &FxHashMap<Symbol, Expr>,
    ) -> Result<(), String> {
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

    fn compile_function(&mut self, func: &FuncDecl) -> Result<(), String> {
        let main_module = self.query().main_module();
        let (func_key, display_name) = self.main_function_key_and_name(func.name);
        let jit_func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Function {} not declared", display_name))?;

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .function_id(main_module, func.name)
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

    /// Compile a scoped function declaration (like a pure lambda).
    /// Returns the FuncId and type information needed to make it callable in tests.
    fn compile_scoped_function(&mut self, func: &FuncDecl) -> Result<ScopedFuncInfo, String> {
        self.state
            .lambda_counter
            .set(self.state.lambda_counter.get() + 1);

        // Look up the closure function type from sema (pre-computed during analysis)
        let func_type_id = self
            .query()
            .scoped_function_type(func.span)
            .ok_or_else(|| {
                format!(
                    "Scoped function type not found for '{}'",
                    self.analyzed.interner.resolve(func.name)
                )
            })?;

        // Extract param and return types from the function type
        let (param_type_ids, return_type_id) = {
            let arena = self.analyzed.type_arena();
            let (params, ret, _) = arena.unwrap_function(func_type_id).ok_or_else(|| {
                format!(
                    "Scoped function has non-function type for '{}'",
                    self.analyzed.interner.resolve(func.name)
                )
            })?;
            (params.to_vec(), ret)
        };

        // Convert to Cranelift types
        let param_types = self.type_ids_to_cranelift(&param_type_ids);

        let return_type = type_id_to_cranelift(
            return_type_id,
            self.analyzed.type_arena(),
            self.pointer_type,
        );

        // Create closure calling convention signature (first param is closure ptr)
        let mut sig = self.jit.module.make_signature();
        sig.params
            .push(cranelift::prelude::AbiParam::new(self.pointer_type)); // closure ptr
        for &param_ty in &param_types {
            sig.params.push(cranelift::prelude::AbiParam::new(param_ty));
        }
        sig.returns
            .push(cranelift::prelude::AbiParam::new(return_type));

        // Create unique function name
        let scoped_func_name = format!("__scoped_{}_{}", self.state.lambda_counter.get(), {
            self.analyzed.interner.resolve(func.name)
        });
        let func_id = self
            .jit
            .module
            .declare_function(&scoped_func_name, cranelift_module::Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;

        // Compile the function body
        let mut func_ctx = self.jit.module.make_context();
        func_ctx.func.signature = sig.clone();

        // Build params: Vec<(Symbol, TypeId, Type)>
        let params: Vec<(Symbol, TypeId, cranelift::prelude::Type)> = func
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| (p.name, param_type_ids[i], param_types[i]))
            .collect();

        // Get source file pointer
        let source_file_ptr = self.source_file_ptr();

        {
            let mut builder_ctx = FunctionBuilderContext::new();
            let builder = FunctionBuilder::new(&mut func_ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            // Use pure lambda config (skip_block_params=1 for closure ptr)
            let config = FunctionCompileConfig::pure_lambda(&func.body, params, return_type_id);
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        self.jit
            .module
            .define_function(func_id, &mut func_ctx)
            .map_err(|e| format!("Failed to define scoped function: {:?}", e))?;

        Ok(ScopedFuncInfo {
            name: func.name,
            func_id,
            func_type_id,
        })
    }

    /// Compile all tests in a tests block
    fn compile_tests(
        &mut self,
        tests_decl: &TestsDecl,
        test_count: &mut usize,
    ) -> Result<(), String> {
        // Phase 1: Compile all scoped function declarations (once, before test loop)
        let mut scoped_funcs: Vec<ScopedFuncInfo> = Vec::new();
        for decl in &tests_decl.decls {
            if let Decl::Function(func) = decl {
                let info = self.compile_scoped_function(func)?;
                scoped_funcs.push(info);
            }
        }

        // Collect scoped let declarations for compiling in each test
        let scoped_lets: Vec<&LetStmt> = tests_decl
            .decls
            .iter()
            .filter_map(|d| {
                if let Decl::Let(let_stmt) = d {
                    Some(let_stmt)
                } else {
                    None
                }
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

                // Build pre-seeded variables map with scoped functions
                let mut variables = FxHashMap::default();
                for scoped_func in &scoped_funcs {
                    // Get func_ref for this function in the current test's context
                    let func_ref = codegen_ctx
                        .module
                        .declare_func_in_func(scoped_func.func_id, builder.func);
                    let func_addr = builder.ins().func_addr(self.pointer_type, func_ref);

                    // Wrap in Closure struct via vole_closure_alloc
                    let alloc_id = codegen_ctx
                        .func_registry
                        .runtime_key(RuntimeFn::ClosureAlloc)
                        .and_then(|key| codegen_ctx.func_registry.func_id(key))
                        .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
                    let alloc_ref = codegen_ctx
                        .module
                        .declare_func_in_func(alloc_id, builder.func);
                    let zero_captures = builder.ins().iconst(types::I64, 0);
                    let alloc_call = builder.ins().call(alloc_ref, &[func_addr, zero_captures]);
                    let closure_ptr = builder.inst_results(alloc_call)[0];

                    // Declare Cranelift variable and add to map
                    // Use the pre-computed closure function type from sema
                    let var = builder.declare_var(self.pointer_type);
                    builder.def_var(var, closure_ptr);
                    variables.insert(scoped_func.name, (var, scoped_func.func_type_id));
                }

                // Compile scoped let declarations and test body
                let mut cg = Cg::new(&mut builder, &mut codegen_ctx, &env).with_vars(variables);

                if !scoped_lets.is_empty() {
                    // Create a synthetic block with the let statements
                    let let_block = Block {
                        stmts: scoped_lets
                            .iter()
                            .map(|s| Stmt::Let((*s).clone()))
                            .collect(),
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

    /// Compile program to CLIF IR and write to the given writer.
    /// Does not finalize for execution - just generates IR for inspection.
    pub fn compile_to_ir<W: Write>(
        &mut self,
        program: &Program,
        writer: &mut W,
        include_tests: bool,
    ) -> Result<(), String> {
        let _module_id = self.query().main_module();
        // First pass: declare all functions so they can reference each other
        let mut test_count = 0usize;
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Get FunctionId and build signature from pre-resolved types
                    let main_module = self.query().main_module();
                    let Some(semantic_func_id) = self.query().function_id(main_module, func.name)
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
                _ => {}
            }
        }

        // Second pass: build and emit IR for each function
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let name = self.analyzed.interner.resolve(func.name);
                    self.build_function_ir(func)?;
                    writeln!(writer, "// func {}", name).map_err(|e| e.to_string())?;
                    writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| e.to_string())?;
                    self.jit.clear();
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for test in &tests_decl.tests {
                        self.build_test_ir(test)?;
                        writeln!(writer, "// test \"{}\"", test.name).map_err(|e| e.to_string())?;
                        writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| e.to_string())?;
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
    fn build_function_ir(&mut self, func: &FuncDecl) -> Result<(), String> {
        let main_module = self.query().main_module();

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .function_id(main_module, func.name)
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
            let empty_global_inits = FxHashMap::default();
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &empty_global_inits,
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

        Ok(())
    }

    /// Build IR for a single test case without defining it.
    /// Similar to test compilation in compile_tests but doesn't call define_function.
    fn build_test_ir(&mut self, test: &TestCase) -> Result<(), String> {
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
            let empty_global_inits = FxHashMap::default();
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &empty_global_inits,
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
    fn declare_monomorphized_instances(&mut self) -> Result<(), String> {
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
    fn compile_monomorphized_instances(&mut self, program: &Program) -> Result<(), String> {
        // Build a map of generic function names to their ASTs
        // Include both explicit generics (type_params in AST) and implicit generics
        // (structural type params that create generic_info in entity registry)
        let generic_func_asts: FxHashMap<NameId, &FuncDecl> = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Function(func) = decl {
                    let query = self.query();
                    let name_id = query.function_name_id(query.main_module(), func.name);

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
                        return Some((name_id, func));
                    }
                }
                None
            })
            .collect();

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

            let func = generic_func_asts
                .get(&instance.original_name)
                .ok_or_else(|| {
                    let func_name = self.query().display_name(instance.original_name);
                    format!(
                        "Internal error: generic function AST not found for {}",
                        func_name
                    )
                })?;

            self.compile_monomorphized_function(func, &instance)?;
        }

        Ok(())
    }

    /// Compile a single monomorphized function instance
    fn compile_monomorphized_function(
        &mut self,
        func: &FuncDecl,
        instance: &MonomorphInstance,
    ) -> Result<(), String> {
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
    fn declare_class_method_monomorphized_instances(&mut self) -> Result<(), String> {
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
    ) -> Result<(), String> {
        let (class_asts, record_asts) = self.build_generic_type_asts(program);

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

            // Try to find the method in a class first
            if let Some(class) = class_asts.get(&instance.class_name) {
                let method_name_str = self.query().display_name(instance.method_name);
                let method = class
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_class_method(method, &instance)?;
                    continue;
                }
            }

            // Try records
            if let Some(record) = record_asts.get(&instance.class_name) {
                let method_name_str = self.query().display_name(instance.method_name);
                let method = record
                    .methods
                    .iter()
                    .find(|m| self.query().resolve_symbol(m.name) == method_name_str);
                if let Some(method) = method {
                    self.compile_monomorphized_class_method(method, &instance)?;
                    continue;
                }
            }

            // Method not found - this shouldn't happen if sema was correct
            let class_name = self.query().display_name(instance.class_name);
            let method_name = self.query().display_name(instance.method_name);
            return Err(format!(
                "Internal error: method {} not found in class/record {}",
                method_name, class_name
            ));
        }

        Ok(())
    }

    /// Compile a single monomorphized class method instance
    fn compile_monomorphized_class_method(
        &mut self,
        method: &FuncDecl,
        instance: &ClassMethodMonomorphInstance,
    ) -> Result<(), String> {
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
    fn declare_static_method_monomorphized_instances(&mut self) -> Result<(), String> {
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
    ) -> Result<(), String> {
        let (class_asts, record_asts) = self.build_generic_type_asts(program);

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

            // Try to find the static method in a class first
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

            // Try records
            if let Some(record) = record_asts.get(&instance.class_name)
                && let Some(ref statics) = record.statics
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
            return Err(format!(
                "Internal error: static method {} not found in class/record {}",
                method_name, class_name
            ));
        }

        Ok(())
    }

    /// Compile a single monomorphized static method instance
    fn compile_monomorphized_static_method(
        &mut self,
        method: &InterfaceMethod,
        instance: &StaticMethodMonomorphInstance,
    ) -> Result<(), String> {
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

    /// Build maps of generic class/record NameIds to their AST declarations.
    /// Used by both class method and static method monomorphization.
    fn build_generic_type_asts<'a>(
        &self,
        program: &'a Program,
    ) -> (
        FxHashMap<NameId, &'a vole_frontend::ClassDecl>,
        FxHashMap<NameId, &'a vole_frontend::RecordDecl>,
    ) {
        let class_asts = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Class(class) = decl
                    && !class.type_params.is_empty()
                {
                    let query = self.query();
                    let name_id = query.try_name_id(query.main_module(), &[class.name])?;
                    return Some((name_id, class));
                }
                None
            })
            .collect();

        let record_asts = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Record(record) = decl
                    && !record.type_params.is_empty()
                {
                    let query = self.query();
                    let name_id = query.try_name_id(query.main_module(), &[record.name])?;
                    return Some((name_id, record));
                }
                None
            })
            .collect();

        (class_asts, record_asts)
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Unified monomorphization entry points
    // ═══════════════════════════════════════════════════════════════════════

    /// Declare all monomorphized instances (functions, class methods, static methods)
    fn declare_all_monomorphized_instances(&mut self, _program: &Program) -> Result<(), String> {
        // Note: Nested generic calls are now discovered during sema analysis,
        // so we don't need to expand instances here.
        self.declare_monomorphized_instances()?;
        self.declare_class_method_monomorphized_instances()?;
        self.declare_static_method_monomorphized_instances()?;
        Ok(())
    }

    /// Compile all monomorphized instances (functions, class methods, static methods)
    fn compile_all_monomorphized_instances(&mut self, program: &Program) -> Result<(), String> {
        self.compile_monomorphized_instances(program)?;
        self.compile_class_method_monomorphized_instances(program)?;
        self.compile_static_method_monomorphized_instances(program)?;
        Ok(())
    }
}
