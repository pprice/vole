use std::collections::HashMap;
use std::io::Write;

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};
use cranelift_module::{FuncId, Module};

use super::common::{
    DefaultReturn, FunctionCompileConfig, compile_function_inner_with_params,
    finalize_function_body,
};
use super::{Compiler, SelfParam, TestInfo, TypeResolver};

use crate::FunctionKey;
use crate::RuntimeFn;
use crate::context::Cg;
use crate::types::{
    CodegenCtx, CompileEnv, function_name_id_with_interner, resolve_type_expr_to_id,
    type_id_to_cranelift,
};
use vole_frontend::{
    Block, Decl, Expr, FuncBody, FuncDecl, InterfaceMethod, Interner, LetInit, LetStmt, Program,
    Span, Stmt, Symbol, TestCase, TestsDecl,
};
use vole_identity::NameId;
use vole_sema::entity_defs::TypeDefKind;
use vole_sema::generic::{
    ClassMethodMonomorphInstance, MonomorphInstance, MonomorphInstanceTrait,
    StaticMethodMonomorphInstance,
};
use vole_sema::type_arena::{TypeId, TypeIdVec};

/// Information about a compiled scoped function, used to make it available in tests
struct ScopedFuncInfo {
    /// The function's name (Symbol) for looking up in variables
    name: Symbol,
    /// The compiled function ID
    func_id: FuncId,
    /// The function's return type
    return_type_id: TypeId,
    /// The function's parameter types
    param_type_ids: Vec<TypeId>,
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
        let func_module = self.func_registry.main_module();
        let key = if let Some(name_id) = name_id {
            self.func_registry.intern_name_id(name_id)
        } else {
            self.intern_func(func_module, &[sym])
        };
        (key, display_name)
    }

    fn test_function_key(&mut self, test_index: usize) -> (NameId, FunctionKey) {
        if let Some(name_id) = self.test_name_ids.get(test_index).copied() {
            let key = self.func_registry.intern_name_id(name_id);
            return (name_id, key);
        }

        let (name_id, key) = self.func_registry.intern_test_name(test_index);
        if self.test_name_ids.len() == test_index {
            self.test_name_ids.push(name_id);
        } else if self.test_name_ids.len() < test_index {
            self.test_name_ids.resize(test_index + 1, name_id);
        } else {
            self.test_name_ids[test_index] = name_id;
        }
        (name_id, key)
    }

    fn test_display_name(&self, name_id: NameId) -> String {
        self.func_registry.name_table_rc().borrow().display(name_id)
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
                    // Get return type from entity_registry (supports inferred types)
                    let return_type_id = self
                        .query()
                        .function_return_type(self.query().main_module(), func.name);
                    let sig = self.build_signature_with_return_type_id(
                        &func.params,
                        return_type_id,
                        SelfParam::None,
                        TypeResolver::Query,
                    );
                    let (func_key, display_name) = self.main_function_key_and_name(func.name);
                    let func_id = self.jit.declare_function(&display_name, &sig);
                    self.func_registry.set_func_id(func_key, func_id);
                    // Record return type for use in call expressions (TypeId-native)
                    self.func_registry
                        .set_return_type(func_key, return_type_id.unwrap_or(TypeId::VOID));
                }
                Decl::Tests(tests_decl) => {
                    // Declare each test with a generated name and signature () -> i64
                    let i64_type_id = self.analyzed.type_arena().primitives.i64;
                    for _ in &tests_decl.tests {
                        let (name_id, func_key) = self.test_function_key(test_count);
                        let func_name = self.test_display_name(name_id);
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
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    self.compile_function(func)?;
                }
                Decl::Tests(tests_decl) => {
                    self.compile_tests(tests_decl, &mut test_count)?;
                }
                Decl::Let(_) => {
                    // Globals are handled during identifier lookup
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

        for module_path in &module_paths {
            tracing::debug!(module_path, "compile_module_functions: processing module");
            // Access module_programs directly to avoid borrow conflict with mutable self operations
            let (program, module_interner) = &self.analyzed.module_programs[module_path];
            // Extract module global initializer expressions
            let module_global_inits: HashMap<Symbol, Expr> = program
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

            // First pass: declare pure Vole functions
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

                    // Create signature and declare function
                    let sig = self.build_signature(
                        &func.params,
                        func.return_type.as_ref(),
                        SelfParam::None,
                        TypeResolver::Query,
                    );
                    let func_id = self.jit.declare_function(&display_name, &sig);
                    let func_key = self.func_registry.intern_name_id(name_id);
                    self.func_registry.set_func_id(func_key, func_id);

                    // Record return type
                    let return_type_id = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_to_id(t))
                        .unwrap_or(TypeId::VOID);
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
            }

            // Register static methods from implement blocks (first pass - declarations only)
            // Instance methods are skipped - they're handled through the main program path.
            // External methods are resolved via the native registry.
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl
                    && impl_block.statics.is_some()
                {
                    self.register_implement_statics_only_with_interner(impl_block, module_interner);
                }
            }

            // Finalize module classes (register type metadata, declare methods)
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.finalize_module_class(class, module_interner);
                }
            }

            // Second pass: compile pure Vole function bodies
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

            // Compile implement block static methods from module programs
            // Note: Instance methods for primitives (like to_string, index_of) are compiled
            // through the main program path, not here. This avoids cross-interner issues.
            for decl in &program.declarations {
                if let Decl::Implement(impl_block) = decl {
                    // Compile static methods only
                    if impl_block.statics.is_some() {
                        self.compile_implement_statics_only(
                            impl_block,
                            Some(module_path),
                            module_interner,
                        )?;
                    }
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

                    // Create signature and IMPORT (not declare) the function
                    let sig = self.build_signature(
                        &func.params,
                        func.return_type.as_ref(),
                        SelfParam::None,
                        TypeResolver::Query,
                    );
                    let func_id = self.jit.import_function(&display_name, &sig);
                    let func_key = self.func_registry.intern_name_id(name_id);
                    self.func_registry.set_func_id(func_key, func_id);

                    // Record return type
                    let return_type_id = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_to_id(t))
                        .unwrap_or(TypeId::VOID);
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
            for decl in &program.declarations {
                if let Decl::Class(class) = decl {
                    self.import_module_class(class, module_interner);
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
    ) {
        // First finalize to get type metadata registered
        self.finalize_module_class(class, module_interner);

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
        module_global_inits: &HashMap<Symbol, Expr>,
    ) -> Result<(), String> {
        let func_key = self.func_registry.intern_name_id(name_id);
        let display_name = self.query().display_name(name_id);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Module function {} not declared", display_name))?;
        let module_id = self.query().module_id_or_main(module_path);

        // Create function signature
        let sig = self.build_signature(
            &func.params,
            func.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // First collect type IDs (which may access arena internally)
        // Note: Use module_interner since the TypeExpr Symbols come from the module's AST
        let param_info: Vec<(Symbol, TypeId)> = {
            let query = self.query();
            let type_metadata = &self.state.type_metadata;
            let name_table = self.analyzed.name_table();
            func.params
                .iter()
                .map(|p| {
                    let type_id = resolve_type_expr_to_id(
                        &p.ty,
                        query.registry(),
                        type_metadata,
                        module_interner,
                        &name_table,
                        module_id,
                        self.analyzed.type_arena_ref(),
                    );
                    (p.name, type_id)
                })
                .collect()
        };
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
            param_info
                .into_iter()
                .map(|(name, type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, &arena_ref, self.pointer_type);
                    (name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get function return type id (TypeId-native)
        let return_type_id = func
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_to_id(t));

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
        self.finalize_function(func_id)?;

        Ok(())
    }

    fn compile_function(&mut self, func: &FuncDecl) -> Result<(), String> {
        let main_module = self.query().main_module();
        let (func_key, display_name) = self.main_function_key_and_name(func.name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Function {} not declared", display_name))?;

        // Get return type from entity_registry (supports inferred types)
        let return_type_id = self.query().function_return_type(main_module, func.name);

        // Create function signature
        let sig = self.build_signature_with_return_type_id(
            &func.params,
            return_type_id,
            SelfParam::None,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        // First collect type IDs (may borrow arena internally), then convert to cranelift types
        let param_info: Vec<(Symbol, TypeId)> = func
            .params
            .iter()
            .map(|p| (p.name, self.resolve_type_to_id(&p.ty)))
            .collect();
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
            param_info
                .into_iter()
                .map(|(name, type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, &arena_ref, self.pointer_type);
                    (name, type_id, cranelift_type)
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

        // Define the function
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile a scoped function declaration (like a pure lambda).
    /// Returns the FuncId and type information needed to make it callable in tests.
    fn compile_scoped_function(&mut self, func: &FuncDecl) -> Result<ScopedFuncInfo, String> {
        self.state
            .lambda_counter
            .set(self.state.lambda_counter.get() + 1);

        // Get param types using the compiler's type resolution
        let param_type_ids: Vec<TypeId> = func
            .params
            .iter()
            .map(|p| self.resolve_type_to_id(&p.ty))
            .collect();

        // Get return type:
        // 1. If declared, use the declared type
        // 2. If expression body, get the type from sema (stored in expr_types)
        // 3. Fall back to void
        let return_type_id = if let Some(t) = &func.return_type {
            self.resolve_type_to_id(t)
        } else {
            // For expression bodies, get the type from the body expression
            match &func.body {
                FuncBody::Expr(expr) => self.query().type_of(expr.id).unwrap_or(TypeId::VOID),
                FuncBody::Block(_) => TypeId::VOID,
            }
        };

        // Convert to Cranelift types
        let param_types = self.type_ids_to_cranelift(&param_type_ids);

        let return_type = type_id_to_cranelift(
            return_type_id,
            &self.analyzed.type_arena(),
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
            return_type_id,
            param_type_ids,
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
            let (name_id, func_key) = self.test_function_key(*test_count);
            let func_name = self.test_display_name(name_id);
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
                let mut variables = HashMap::new();
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

                    // Create function type for the variable
                    let func_type_id = {
                        let param_ids: TypeIdVec =
                            scoped_func.param_type_ids.iter().copied().collect();
                        vole_sema::ProgramUpdate::new(env.analyzed.type_arena_ref()).function(
                            param_ids,
                            scoped_func.return_type_id,
                            true,
                        ) // is_closure=true
                    };

                    // Declare Cranelift variable and add to map
                    let var = builder.declare_var(self.pointer_type);
                    builder.def_var(var, closure_ptr);
                    variables.insert(scoped_func.name, (var, func_type_id));
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
                func_name_id: name_id,
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
                    let sig = self.build_signature(
                        &func.params,
                        func.return_type.as_ref(),
                        SelfParam::None,
                        TypeResolver::Query,
                    );
                    let (func_key, display_name) = self.main_function_key_and_name(func.name);
                    let func_id = self.jit.declare_function(&display_name, &sig);
                    self.func_registry.set_func_id(func_key, func_id);
                    // Record return type for use in call expressions
                    let return_type_id = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_to_id(t))
                        .unwrap_or(TypeId::VOID);
                    self.func_registry.set_return_type(func_key, return_type_id);
                }
                Decl::Tests(tests_decl) if include_tests => {
                    let i64_type_id = self.analyzed.type_arena().primitives.i64;
                    for _ in &tests_decl.tests {
                        let (name_id, func_key) = self.test_function_key(test_count);
                        let func_name = self.test_display_name(name_id);
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
        let _module_id = self.query().main_module();
        // Create function signature
        let sig = self.build_signature(
            &func.params,
            func.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Collect param types and build config
        let param_type_ids: Vec<TypeId> = func
            .params
            .iter()
            .map(|p| self.resolve_type_to_id(&p.ty))
            .collect();
        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = func
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Get function return type id
        let return_type_id = func
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_to_id(t));

        // Create function builder and compile
        let source_file_ptr = self.source_file_ptr();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let empty_global_inits = HashMap::new();
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &empty_global_inits,
                source_file_ptr,
                current_module: None,
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
            let empty_global_inits = HashMap::new();
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &empty_global_inits,
                source_file_ptr,
                current_module: None,
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
        let generic_func_asts: HashMap<NameId, &FuncDecl> = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Function(func) = decl
                    && !func.type_params.is_empty()
                {
                    let query = self.query();
                    let name_id = query.function_name_id(query.main_module(), func.name);
                    return Some((name_id, func));
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
                    self.compile_monomorphized_class_method(method, &instance, class.name)?;
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
                    self.compile_monomorphized_class_method(method, &instance, record.name)?;
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
        type_name: Symbol,
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

        // Build self binding with concrete type args
        let self_type_id = self.build_concrete_self_type_id(type_name, &instance.substitutions);
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

    /// Build the concrete self type with type arguments substituted
    /// Build a concrete self type for monomorphized class methods (TypeId-native)
    fn build_concrete_self_type_id(
        &self,
        type_name: Symbol,
        substitutions: &HashMap<NameId, TypeId>,
    ) -> TypeId {
        let query = self.query();
        let module_id = query.main_module();
        let type_name_str = self.analyzed.interner.resolve(type_name);

        tracing::debug!(
            type_name = %type_name_str,
            substitutions = ?substitutions,
            "build_concrete_self_type_id"
        );

        // Try to get NameId and TypeDefId for this type
        let type_def_id = query
            .try_name_id(module_id, &[type_name])
            .and_then(|name_id| {
                tracing::debug!(name_id = ?name_id, "found name_id");
                query.try_type_def_id(name_id)
            });

        if let Some(type_def_id) = type_def_id {
            let type_def = query.get_type(type_def_id);
            tracing::debug!(
                type_def_id = ?type_def_id,
                has_generic_info = type_def.generic_info.is_some(),
                "found type_def"
            );

            // If it has generic_info, use it to build the type with proper TypeParam substitution
            if let Some(generic_info) = &type_def.generic_info {
                tracing::debug!(
                    field_types = ?generic_info.field_types,
                    "using generic_info"
                );

                // Build type_args from substituted type params (TypeId-native)
                let type_args_id: TypeIdVec = generic_info
                    .type_params
                    .iter()
                    .map(|param| {
                        substitutions
                            .get(&param.name_id)
                            .copied()
                            .unwrap_or_else(|| {
                                self.analyzed.type_arena_mut().type_param(param.name_id)
                            })
                    })
                    .collect();

                // Determine if it's a class or record based on TypeDefKind
                let update = vole_sema::ProgramUpdate::new(self.analyzed.type_arena_ref());
                return match &type_def.kind {
                    TypeDefKind::Record => update.record(type_def_id, type_args_id),
                    TypeDefKind::Class => update.class(type_def_id, type_args_id),
                    _ => update.record(type_def_id, type_args_id), // Fallback
                };
            }

            // Non-generic type: use type_metadata
            if let Some(metadata) = self.state.type_metadata.get(&type_def_id) {
                // Apply substitutions to the stored vole_type
                let subs: FxHashMap<NameId, TypeId> =
                    substitutions.iter().map(|(&k, &v)| (k, v)).collect();
                return vole_sema::ProgramUpdate::new(self.analyzed.type_arena_ref())
                    .substitute(metadata.vole_type, &subs);
            }
        }

        // Final fallback (type not in entity registry or type_metadata)
        self.analyzed.type_arena().primitives.i64
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
        HashMap<NameId, &'a vole_frontend::ClassDecl>,
        HashMap<NameId, &'a vole_frontend::RecordDecl>,
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
