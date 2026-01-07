use std::collections::HashMap;
use std::io::Write;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, InstBuilder, types};

use super::{Compiler, ControlFlowCtx, TestInfo};
use crate::codegen::FunctionKey;
use crate::codegen::stmt::compile_block;
use crate::codegen::types::{CompileCtx, resolve_type_expr_full, type_to_cranelift};
use crate::frontend::{Decl, FuncDecl, Interner, LetStmt, Program, Symbol, TestCase, TestsDecl};
use crate::identity::{NameId, NamerLookup};
use crate::sema::Type;
use crate::sema::generic::MonomorphInstance;

impl Compiler<'_> {
    fn main_function_key_and_name(&mut self, sym: Symbol) -> (FunctionKey, String) {
        let namer = NamerLookup::new(&self.analyzed.name_table, &self.analyzed.interner);
        let name_id = namer.function(self.analyzed.name_table.main_module(), sym);
        let display_name = self.analyzed.interner.resolve(sym).to_string();
        let key = if let Some(name_id) = name_id {
            self.func_registry.intern_name_id(name_id)
        } else {
            self.func_registry
                .intern_qualified(self.func_registry.main_module(), &[sym])
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
        self.func_registry
            .name_table()
            .display(name_id, &self.analyzed.interner)
    }

    /// Compile a complete program
    pub fn compile_program(&mut self, program: &Program) -> Result<(), String> {
        // Compile module functions first (before main program)
        self.compile_module_functions()?;

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
                    let sig = self.create_function_signature(func);
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
                        self.func_registry.set_return_type(func_key, Type::I64);
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
        self.declare_monomorphized_instances()?;

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
        self.compile_monomorphized_instances(program)?;

        Ok(())
    }

    /// Compile pure Vole functions from imported modules.
    /// These are functions defined in module files (not external FFI functions).
    fn compile_module_functions(&mut self) -> Result<(), String> {
        // Collect module paths first to avoid borrow issues
        let module_paths: Vec<_> = self.analyzed.module_programs.keys().cloned().collect();

        for module_path in &module_paths {
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
                    let module_id = self
                        .analyzed
                        .name_table
                        .module_id_if_known(module_path)
                        .unwrap_or_else(|| self.analyzed.name_table.main_module());
                    let name_id = NamerLookup::new(&self.analyzed.name_table, module_interner)
                        .function(module_id, func.name)
                        .expect("module function name_id should be registered");
                    let display_name = self.analyzed.name_table.display(name_id, module_interner);

                    // Create signature and declare function
                    let sig = self.create_function_signature(func);
                    let func_id = self.jit.declare_function(&display_name, &sig);
                    let func_key = self.func_registry.intern_name_id(name_id);
                    self.func_registry.set_func_id(func_key, func_id);

                    // Record return type
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_full(
                                t,
                                &self.analyzed.type_aliases,
                                &self.analyzed.interface_registry,
                                &self.analyzed.interner,
                                &self.analyzed.name_table,
                                module_id,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_registry.set_return_type(func_key, return_type);
                }
            }

            // Second pass: compile pure Vole function bodies
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    let module_id = self
                        .analyzed
                        .name_table
                        .module_id_if_known(module_path)
                        .unwrap_or_else(|| self.analyzed.name_table.main_module());
                    let name_id = NamerLookup::new(&self.analyzed.name_table, module_interner)
                        .function(module_id, func.name)
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
        }

        Ok(())
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
        let display_name = self.analyzed.name_table.display(name_id, module_interner);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Module function {} not declared", display_name))?;
        let module_id = self
            .analyzed
            .name_table
            .module_id_if_known(module_path)
            .unwrap_or_else(|| self.analyzed.name_table.main_module());

        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        // Collect param types
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
                        &self.analyzed.name_table,
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
                resolve_type_expr_full(
                    &p.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_full(
                t,
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
                &self.analyzed.name_table,
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
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body with module's interner
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: module_interner, // Use module's interner
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: module_globals, // Use module's globals
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: Some(module_path), // We're compiling module code
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
        let module_id = self.analyzed.name_table.main_module();
        let (func_key, display_name) = self.main_function_key_and_name(func.name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Function {} not declared", display_name))?;

        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
                        &self.analyzed.name_table,
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
                resolve_type_expr_full(
                    &p.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_full(
                t,
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
                &self.analyzed.name_table,
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
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
                let mut cf_ctx = ControlFlowCtx::new();
                let mut ctx = CompileCtx {
                    analyzed: self.analyzed,
                    interner: &self.analyzed.interner,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_registry: &mut self.func_registry,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
                    type_metadata: &self.type_metadata,
                    impl_method_infos: &self.impl_method_infos,
                    current_function_return_type: None, // Tests don't have a declared return type
                    native_registry: &self.native_registry,
                    current_module: None,
                    generic_calls: &self.analyzed.generic_calls,
                    monomorph_cache: &self.analyzed.monomorph_cache,
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
        let module_id = self.analyzed.name_table.main_module();
        // First pass: declare all functions so they can reference each other
        let mut test_count = 0usize;
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let sig = self.create_function_signature(func);
                    let (func_key, display_name) = self.main_function_key_and_name(func.name);
                    let func_id = self.jit.declare_function(&display_name, &sig);
                    self.func_registry.set_func_id(func_key, func_id);
                    // Record return type for use in call expressions
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_full(
                                t,
                                &self.analyzed.type_aliases,
                                &self.analyzed.interface_registry,
                                &self.analyzed.interner,
                                &self.analyzed.name_table,
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
                        self.func_registry.set_return_type(func_key, Type::I64);
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
        let module_id = self.analyzed.name_table.main_module();
        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
                        &self.analyzed.name_table,
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
                resolve_type_expr_full(
                    &p.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_full(
                t,
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
                &self.analyzed.name_table,
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
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let empty_type_metadata = HashMap::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &empty_type_metadata,
                impl_method_infos: &self.impl_method_infos,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
            let mut cf_ctx = ControlFlowCtx::new();
            let empty_type_metadata = HashMap::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &empty_type_metadata,
                impl_method_infos: &self.impl_method_infos,
                current_function_return_type: None, // Tests don't have a declared return type
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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

    /// Declare all monomorphized function instances
    fn declare_monomorphized_instances(&mut self) -> Result<(), String> {
        // Collect instances to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .monomorph_cache
            .instances()
            .map(|(key, instance)| (key.clone(), instance.clone()))
            .collect();

        for (_key, instance) in instances {
            let mangled_name = self
                .analyzed
                .name_table
                .display(instance.mangled_name, &self.analyzed.interner);

            // Create signature from the concrete function type
            let mut params = Vec::new();
            for param_type in &instance.func_type.params {
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
            let func_id = self.jit.declare_function(&mangled_name, &sig);
            let func_key = self.func_registry.intern_name_id(instance.mangled_name);
            self.func_registry.set_func_id(func_key, func_id);

            // Record return type for call expressions
            self.func_registry
                .set_return_type(func_key, (*instance.func_type.return_type).clone());
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
                    let namer =
                        NamerLookup::new(&self.analyzed.name_table, &self.analyzed.interner);
                    let name_id = namer
                        .function(self.analyzed.name_table.main_module(), func.name)
                        .expect("generic function name_id should be registered");
                    return Some((name_id, func));
                }
                None
            })
            .collect();

        // Collect instances to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .monomorph_cache
            .instances()
            .map(|(key, instance)| (key.clone(), instance.clone()))
            .collect();

        for (_key, instance) in instances {
            let func = generic_func_asts
                .get(&instance.original_name)
                .ok_or_else(|| {
                    format!(
                        "Internal error: generic function AST not found for {}",
                        self.analyzed
                            .name_table
                            .display(instance.original_name, &self.analyzed.interner)
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
        let mangled_name = self
            .analyzed
            .name_table
            .display(instance.mangled_name, &self.analyzed.interner);
        let func_key = self.func_registry.intern_name_id(instance.mangled_name);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| format!("Monomorphized function {} not declared", mangled_name))?;

        // Create function signature from concrete types
        let mut params = Vec::new();
        for param_type in &instance.func_type.params {
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
        let param_vole_types: Vec<Type> = instance.func_type.params.clone();

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
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_registry: &mut self.func_registry,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                impl_method_infos: &self.impl_method_infos,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
}
