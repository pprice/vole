use std::collections::HashMap;
use std::io::Write;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};

use super::{Compiler, ControlFlowCtx, SelfParam, TestInfo, TypeResolver};
use crate::codegen::FunctionKey;
use crate::codegen::stmt::compile_block;
use crate::codegen::types::{
    CompileCtx, function_name_id_with_interner, resolve_type_expr_with_metadata, type_to_cranelift,
};
use crate::frontend::{
    Decl, FuncDecl, InterfaceMethod, Interner, LetStmt, Program, Symbol, TestCase, TestsDecl,
};
use crate::identity::NameId;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{
    ClassMethodMonomorphInstance, MonomorphInstance, MonomorphInstanceTrait,
    StaticMethodMonomorphInstance, substitute_type,
};
use crate::sema::types::{ClassType, NominalType, RecordType};
use crate::sema::{PrimitiveType, Type};

/// Compilation phase for monomorphization pipeline.
/// Allows separating function declaration from body compilation for forward references.
/// Currently infrastructure for potential future unified API.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MonomorphPhase {
    /// Only declare function signatures (for forward reference support)
    Declare,
    /// Only compile function bodies (assumes already declared)
    Compile,
    /// Both declare and compile (original behavior)
    All,
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
        self.func_registry.name_table().display(name_id)
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
                    // Note: Use resolve_type_with_metadata so that record types (like
                    // generated generator records) are properly resolved from type_metadata
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_with_metadata(t))
                        .unwrap_or(Type::Void);
                    self.func_registry.set_return_type(func_key, return_type);
                }
                Decl::Tests(tests_decl) => {
                    // Declare each test with a generated name and signature () -> i64
                    for _ in &tests_decl.tests {
                        let (name_id, func_key) = self.test_function_key(test_count);
                        let func_name = self.test_display_name(name_id);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        let func_id = self.jit.declare_function(&func_name, &sig);
                        self.func_registry
                            .set_return_type(func_key, Type::Primitive(PrimitiveType::I64));
                        self.func_registry.set_func_id(func_key, func_id);
                        test_count += 1;
                    }
                }
                Decl::Let(let_stmt) => {
                    // Collect global variable declarations
                    self.globals.push(let_stmt.clone());
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
        self.declare_all_monomorphized_instances()?;

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
            // Extract module globals (let statements)
            let module_globals: Vec<LetStmt> = program
                .declarations
                .iter()
                .filter_map(|decl| {
                    if let Decl::Let(let_stmt) = decl {
                        Some(let_stmt.clone())
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
                    let query = self.query();
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_with_metadata(
                                t,
                                query.registry(),
                                &self.type_metadata,
                                query.interner(),
                                query.name_table(),
                                module_id,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_registry.set_return_type(func_key, return_type);
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
                        &module_globals,
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
                    self.compile_module_class_methods(class, module_interner, module_path)?;
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
                    let query = self.query();
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_with_metadata(
                                t,
                                query.registry(),
                                &self.type_metadata,
                                query.interner(),
                                query.name_table(),
                                module_id,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_registry.set_return_type(func_key, return_type);
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
        class: &crate::frontend::ClassDecl,
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
        module_globals: &[LetStmt],
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

        // Collect param types
        let query = self.query();
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_with_metadata(
                        &p.ty,
                        query.registry(),
                        &self.type_metadata,
                        query.interner(),
                        query.name_table(),
                        module_id,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_with_metadata(
                    &p.ty,
                    query.registry(),
                    &self.type_metadata,
                    query.interner(),
                    query.name_table(),
                    module_id,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_with_metadata(
                t,
                query.registry(),
                &self.type_metadata,
                query.interner(),
                query.name_table(),
                module_id,
            )
        });

        // Get source file pointer
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types)
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty));
            }

            // Compile function body with module's interner
            let mut cf_ctx = ControlFlowCtx::default();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: module_interner, // Use module's interner
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: module_globals, // Use module's globals
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: Some(module_path), // We're compiling module code
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: None,
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    fn compile_function(&mut self, func: &FuncDecl) -> Result<(), String> {
        let module_id = self.query().main_module();
        let (func_key, display_name) = self.main_function_key_and_name(func.name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Function {} not declared", display_name))?;

        // Create function signature
        let sig = self.build_signature(
            &func.params,
            func.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Collect param types before borrowing ctx.func
        let query = self.query();
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_with_metadata(
                        &p.ty,
                        query.registry(),
                        &self.type_metadata,
                        query.interner(),
                        query.name_table(),
                        module_id,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_with_metadata(
                    &p.ty,
                    query.registry(),
                    &self.type_metadata,
                    query.interner(),
                    query.name_table(),
                    module_id,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_with_metadata(
                t,
                query.registry(),
                &self.type_metadata,
                query.interner(),
                query.name_table(),
                module_id,
            )
        });

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types)
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::default();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: None,
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile all tests in a tests block
    fn compile_tests(
        &mut self,
        tests_decl: &TestsDecl,
        test_count: &mut usize,
    ) -> Result<(), String> {
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

                // No parameters or variables for tests (they start fresh)
                let mut variables = HashMap::new();

                // Compile test body
                let mut cf_ctx = ControlFlowCtx::default();
                let mut ctx = CompileCtx {
                    analyzed: self.analyzed,
                    interner: &self.analyzed.interner,
                    arena: &self.analyzed.type_arena,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_registry: &mut self.func_registry,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
                    type_metadata: &self.type_metadata,
                    impl_method_infos: &self.impl_method_infos,
                    static_method_infos: &self.static_method_infos,
                    interface_vtables: &self.interface_vtables,
                    current_function_return_type: None, // Tests don't have a declared return type
                    native_registry: &self.native_registry,
                    current_module: None,
                    monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                    type_substitutions: None,
                };
                let terminated = compile_block(
                    &mut builder,
                    &test.body,
                    &mut variables,
                    &mut cf_ctx,
                    &mut ctx,
                )?;

                // If not already terminated, return 0 (test passed)
                if !terminated {
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().return_(&[zero]);
                }

                builder.seal_all_blocks();
                builder.finalize();
            }

            // Define the function
            self.jit.define_function(func_id)?;
            self.jit.clear();

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
        let module_id = self.query().main_module();
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
                    let query = self.query();
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_with_metadata(
                                t,
                                query.registry(),
                                &self.type_metadata,
                                query.interner(),
                                query.name_table(),
                                module_id,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_registry.set_return_type(func_key, return_type);
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for _ in &tests_decl.tests {
                        let (name_id, func_key) = self.test_function_key(test_count);
                        let func_name = self.test_display_name(name_id);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        let func_id = self.jit.declare_function(&func_name, &sig);
                        self.func_registry
                            .set_return_type(func_key, Type::Primitive(PrimitiveType::I64));
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
        let module_id = self.query().main_module();
        // Create function signature
        let sig = self.build_signature(
            &func.params,
            func.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Query,
        );
        self.jit.ctx.func.signature = sig;

        // Collect param types before borrowing ctx.func
        let query = self.query();
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_with_metadata(
                        &p.ty,
                        query.registry(),
                        &self.type_metadata,
                        query.interner(),
                        query.name_table(),
                        module_id,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_with_metadata(
                    &p.ty,
                    query.registry(),
                    &self.type_metadata,
                    query.interner(),
                    query.name_table(),
                    module_id,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_with_metadata(
                t,
                query.registry(),
                &self.type_metadata,
                query.interner(),
                query.name_table(),
                module_id,
            )
        });

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types)
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::default();
            let empty_type_metadata = HashMap::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &empty_type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: None,
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
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

            // No parameters or variables for tests (they start fresh)
            let mut variables = HashMap::new();

            // Compile test body
            let mut cf_ctx = ControlFlowCtx::default();
            let empty_type_metadata = HashMap::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &empty_type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: None, // Tests don't have a declared return type
                native_registry: &self.native_registry,
                current_module: None,
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: None,
            };
            let terminated = compile_block(
                &mut builder,
                &test.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // If not already terminated, return 0 (test passed)
            if !terminated {
                let zero = builder.ins().iconst(types::I64, 0);
                builder.ins().return_(&[zero]);
            }

            builder.seal_all_blocks();
            builder.finalize();
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

        // Create signature from the concrete function type
        let mut params = Vec::new();
        if has_self_param {
            params.push(self.pointer_type);
        }
        for param_type in func_type.params.iter() {
            params.push(type_to_cranelift(param_type, self.pointer_type));
        }
        let ret = if *func_type.return_type == Type::Void {
            None
        } else {
            Some(type_to_cranelift(&func_type.return_type, self.pointer_type))
        };

        let sig = self.jit.create_signature(&params, ret);
        let func_id = self.jit.declare_function(&mangled_name, &sig);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name());
        self.func_registry.set_func_id(func_key, func_id);

        // Record return type for call expressions
        self.func_registry
            .set_return_type(func_key, (*func_type.return_type).clone());
    }

    /// Declare all monomorphized function instances
    fn declare_monomorphized_instances(&mut self) -> Result<(), String> {
        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry
            .monomorph_cache
            .collect_instances();

        for instance in instances {
            // Skip external functions - they don't need JIT compilation
            // They're called directly via native_registry
            let func_name = self.query().display_name(instance.original_name);
            let short_name = self
                .analyzed
                .name_table
                .last_segment_str(instance.original_name)
                .unwrap_or_else(|| func_name.clone());
            if self
                .analyzed
                .implement_registry
                .get_external_func(&short_name)
                .is_some()
            {
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
            .entity_registry
            .monomorph_cache
            .collect_instances();

        for instance in instances {
            // Skip external functions - they don't have AST bodies
            // Generic externals are called directly with type erasure at call sites
            let func_name = self.query().display_name(instance.original_name);
            // External functions are registered by their short name (e.g. "_generic_map_get")
            // not the fully qualified name (e.g. "main::_generic_map_get")
            let short_name = self
                .analyzed
                .name_table
                .last_segment_str(instance.original_name)
                .unwrap_or_else(|| func_name.clone());
            if self
                .analyzed
                .implement_registry
                .get_external_func(&short_name)
                .is_some()
            {
                continue;
            }

            let func = generic_func_asts
                .get(&instance.original_name)
                .ok_or_else(|| {
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

        // Create function signature from concrete types
        let mut params = Vec::new();
        for param_type in instance.func_type.params.iter() {
            params.push(type_to_cranelift(param_type, self.pointer_type));
        }
        let ret = if *instance.func_type.return_type == Type::Void {
            None
        } else {
            Some(type_to_cranelift(
                &instance.func_type.return_type,
                self.pointer_type,
            ))
        };
        let sig = self.jit.create_signature(&params, ret);
        self.jit.ctx.func.signature = sig;

        // Get parameter names and concrete types
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();
        let param_types: Vec<types::Type> = instance
            .func_type
            .params
            .iter()
            .map(|t| type_to_cranelift(t, self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = instance.func_type.params.to_vec();

        // Get return type
        let return_type = Some((*instance.func_type.return_type).clone());

        // Get source file pointer
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types)
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::default();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: None,
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Declare all monomorphized class method instances
    fn declare_class_method_monomorphized_instances(&mut self) -> Result<(), String> {
        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry
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
        // Build a map of class name -> class decl
        let class_asts: HashMap<NameId, &crate::frontend::ClassDecl> = program
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

        // Also include record decls (they can be generic too)
        let record_asts: HashMap<NameId, &crate::frontend::RecordDecl> = program
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

        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry
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

        // Create method signature (self + params) with concrete types
        let mut params = vec![self.pointer_type]; // self
        for param_type in instance.func_type.params.iter() {
            params.push(type_to_cranelift(param_type, self.pointer_type));
        }
        let ret = if *instance.func_type.return_type == Type::Void {
            None
        } else {
            Some(type_to_cranelift(
                &instance.func_type.return_type,
                self.pointer_type,
            ))
        };
        let sig = self.jit.create_signature(&params, ret);
        self.jit.ctx.func.signature = sig;

        // Get parameter names and concrete types
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();
        let param_types: Vec<types::Type> = instance
            .func_type
            .params
            .iter()
            .map(|t| type_to_cranelift(t, self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = instance.func_type.params.to_vec();

        // Get return type
        let return_type = Some((*instance.func_type.return_type).clone());

        // Build self type with concrete type args
        let self_vole_type = self.build_concrete_self_type(type_name, &instance.substitutions);

        // Get source file pointer and self symbol
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let block_params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter
            let self_var = builder.declare_var(self.pointer_type);
            builder.def_var(self_var, block_params[0]);
            variables.insert(self_sym, (self_var, self_vole_type));

            // Bind remaining parameters with concrete types
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types)
                .zip(block_params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty));
            }

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::default();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: Some(&instance.substitutions),
            };
            let terminated = compile_block(
                &mut builder,
                &method.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Build the concrete self type with type arguments substituted
    fn build_concrete_self_type(
        &self,
        type_name: Symbol,
        substitutions: &HashMap<NameId, Type>,
    ) -> Type {
        let query = self.query();
        let module_id = query.main_module();
        let type_name_str = self.analyzed.interner.resolve(type_name);

        tracing::debug!(
            type_name = %type_name_str,
            substitutions = ?substitutions,
            "build_concrete_self_type"
        );

        // Try to get NameId for this type
        if let Some(name_id) = query.try_name_id(module_id, &[type_name]) {
            tracing::debug!(name_id = ?name_id, "found name_id");
            // Look up the TypeDef
            if let Some(type_def_id) = query.try_type_def_id(name_id) {
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

                    // Build type_args from substituted type params
                    let type_args: Vec<Type> = generic_info
                        .type_params
                        .iter()
                        .map(|param| {
                            substitutions
                                .get(&param.name_id)
                                .cloned()
                                .unwrap_or(Type::TypeParam(param.name_id))
                        })
                        .collect();

                    // Determine if it's a class or record based on TypeDefKind
                    return match &type_def.kind {
                        TypeDefKind::Record => Type::Nominal(NominalType::Record(RecordType {
                            type_def_id,
                            type_args: type_args.into(),
                        })),
                        TypeDefKind::Class => Type::Nominal(NominalType::Class(ClassType {
                            type_def_id,
                            type_args: type_args.into(),
                        })),
                        _ => {
                            // Fallback for other kinds
                            Type::Nominal(NominalType::Record(RecordType {
                                type_def_id,
                                type_args: type_args.into(),
                            }))
                        }
                    };
                }
            }
        }

        // Fallback: use type_metadata (for non-generic types)
        if let Some(metadata) = self.type_metadata.get(&type_name) {
            substitute_type(&metadata.vole_type, substitutions)
        } else {
            // Final fallback
            Type::Primitive(PrimitiveType::I64)
        }
    }

    /// Declare all monomorphized static method instances
    fn declare_static_method_monomorphized_instances(&mut self) -> Result<(), String> {
        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry
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
        // Build a map of class name -> class decl (for generic classes)
        let class_asts: HashMap<NameId, &crate::frontend::ClassDecl> = program
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

        // Also include record decls (they can be generic too)
        let record_asts: HashMap<NameId, &crate::frontend::RecordDecl> = program
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

        // Collect instances to avoid borrow issues
        let instances = self
            .analyzed
            .entity_registry
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

        // Create signature (no self parameter) with concrete types
        let mut params = Vec::new();
        for param_type in instance.func_type.params.iter() {
            params.push(type_to_cranelift(param_type, self.pointer_type));
        }
        let ret = if *instance.func_type.return_type == Type::Void {
            None
        } else {
            Some(type_to_cranelift(
                &instance.func_type.return_type,
                self.pointer_type,
            ))
        };
        let sig = self.jit.create_signature(&params, ret);
        self.jit.ctx.func.signature = sig;

        // Get parameter names and concrete types
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();
        let param_types: Vec<types::Type> = instance
            .func_type
            .params
            .iter()
            .map(|t| type_to_cranelift(t, self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = instance.func_type.params.to_vec();

        // Get return type
        let return_type = Some((*instance.func_type.return_type).clone());

        // Get source file pointer
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map (no self for static methods)
            let mut variables = HashMap::new();

            // Get entry block params (just user params, no self)
            let block_params = builder.block_params(entry_block).to_vec();

            // Bind parameters with concrete types
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types)
                .zip(block_params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty));
            }

            // Compile method body
            let body = method.body.as_ref().ok_or_else(|| {
                format!("Internal error: static method {} has no body", mangled_name)
            })?;

            let mut cf_ctx = ControlFlowCtx::default();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                arena: &self.analyzed.type_arena,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                static_method_infos: &self.static_method_infos,
                interface_vtables: &self.interface_vtables,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                monomorph_cache: &self.analyzed.entity_registry.monomorph_cache,
                type_substitutions: Some(&instance.substitutions),
            };
            let terminated =
                compile_block(&mut builder, body, &mut variables, &mut cf_ctx, &mut ctx)?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Unified monomorphization entry points
    // ═══════════════════════════════════════════════════════════════════════

    /// Declare all monomorphized instances (functions, class methods, static methods)
    fn declare_all_monomorphized_instances(&mut self) -> Result<(), String> {
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
