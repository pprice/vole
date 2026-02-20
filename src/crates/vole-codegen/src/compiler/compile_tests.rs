use std::io::Write;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};

use super::common::{
    DefaultReturn, FunctionCompileConfig, compile_function_inner_with_params,
    finalize_function_body,
};
use super::{Compiler, TestInfo};

use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, CompileEnv};
use vole_frontend::ast::{TestCase, TestsDecl};
use vole_frontend::{Block, Decl, ExprKind, LetInit, Program, Span, Stmt};

impl Compiler<'_> {
    /// Compile all tests in a tests block
    pub(super) fn compile_tests(
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
            self.compile_single_test(test, &scoped_let_stmts, test_count)?;
        }

        Ok(())
    }

    /// Compile a single test case into a JIT function.
    fn compile_single_test(
        &mut self,
        test: &TestCase,
        scoped_let_stmts: &[Stmt],
        test_count: &mut usize,
    ) -> CodegenResult<()> {
        let func_key = self.test_function_key(*test_count);
        let func_name = self.test_display_name(func_key);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("test function", &func_name))?;

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
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            // Compile scoped let declarations and test body
            let mut cg = Cg::new(&mut builder, &mut codegen_ctx, &env)
                .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline);

            // Push function-level RC scope for test body
            cg.push_rc_scope();

            if !scoped_let_stmts.is_empty() {
                // Create a synthetic block with the let statements
                let let_block = Block {
                    stmts: scoped_let_stmts.to_vec(),
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

            finalize_function_body(builder, None, terminated, DefaultReturn::Zero);
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

        Ok(())
    }

    /// Declare scoped declarations within a tests block (pass 1).
    /// Handles scoped functions, records, and classes so they're available
    /// during test compilation.
    pub(super) fn declare_tests_scoped_decls(
        &mut self,
        tests_decl: &TestsDecl,
        test_count: &mut usize,
    ) -> CodegenResult<()> {
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
                    self.declare_main_function(func.name);
                }
                Decl::Class(class) => {
                    // Scoped classes are registered under the virtual module
                    if let Some(vm_id) = virtual_module_id {
                        self.finalize_module_class(class, interner, vm_id)?;
                    }
                }
                Decl::Implement(impl_block) => {
                    // Scoped implement blocks target types under the virtual module
                    if let Some(vm_id) = virtual_module_id {
                        self.register_implement_block_in_module(impl_block, vm_id)?;
                    } else {
                        self.register_implement_block(impl_block)?;
                    }
                }
                Decl::Tests(nested_tests) => {
                    // Recursively declare nested tests block scoped decls
                    self.declare_tests_scoped_decls(nested_tests, test_count)?;

                    // Declare each nested test with a generated name and signature () -> i64
                    let i64_type_id = self.arena().primitives.i64;
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

        Ok(())
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

        // First pass: declare all functions so they can reference each other
        let mut test_count = 0usize;
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Declare function using helper (skips if not registered)
                    self.declare_main_function(func.name);
                }
                Decl::Tests(tests_decl) if include_tests => {
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
                    // Store global initializer expressions so module variables are available
                    if let LetInit::Expr(expr) = &let_stmt.init {
                        self.global_inits
                            .insert(let_stmt.name, std::rc::Rc::new(expr.clone()));
                    }
                }
                Decl::LetTuple(let_tuple) => {
                    // Handle top-level destructuring imports
                    if matches!(&let_tuple.init.kind, ExprKind::Import(_)) {
                        self.register_global_module_bindings(let_tuple);
                    }
                }
                _ => {}
            }
        }

        // Declare monomorphized instances (for generic function calls)
        // This is needed before building IR because function calls may reference
        // monomorphized generic functions like println<string>
        self.declare_all_monomorphized_instances()?;

        // Second pass: build and emit IR for each function
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let name = self.analyzed.interner.resolve(func.name);
                    self.build_function_ir(func)?;
                    writeln!(writer, "// func {}", name).map_err(CodegenError::io)?;
                    writeln!(writer, "{}", self.jit.ctx.func).map_err(CodegenError::io)?;
                    self.jit.clear();
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for test in &tests_decl.tests {
                        self.build_test_ir(test)?;
                        writeln!(writer, "// test \"{}\"", test.name).map_err(CodegenError::io)?;
                        writeln!(writer, "{}", self.jit.ctx.func).map_err(CodegenError::io)?;
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
    fn build_function_ir(&mut self, func: &vole_frontend::FuncDecl) -> CodegenResult<()> {
        let program_module = self.program_module();

        // Get FunctionId and extract pre-resolved signature data
        let semantic_func_id = self
            .query()
            .function_id(program_module, func.name)
            .ok_or_else(|| {
                CodegenError::not_found("function", self.analyzed.interner.resolve(func.name))
            })?;
        let func_def = self.query().get_function(semantic_func_id);
        let (param_type_ids, return_type_id) = (
            func_def.signature.params_id.clone(),
            func_def.signature.return_type_id,
        );

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
        crate::control_flow::cleanup_cfg(&mut self.jit.ctx.func);

        // Run loop parameter optimization if enabled
        if self.jit.loop_param_opt_enabled() {
            crate::control_flow::optimize_loop_params(&mut self.jit.ctx.func);
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
            // Seal entry block immediately - it has no predecessors, so SSA
            // variables defined here can be immediately available to successors.
            builder.seal_block(entry_block);

            // Compile test body (no parameters, no return type)
            let env = CompileEnv {
                analyzed: self.analyzed,
                state: &self.state,
                interner: &self.analyzed.interner,
                global_inits: &self.global_inits,
                source_file_ptr,
                global_module_bindings: &self.global_module_bindings,
            };
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
            let (terminated, _) = Cg::new(&mut builder, &mut codegen_ctx, &env)
                .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline)
                .compile_body(&test.body)?;

            finalize_function_body(builder, None, terminated, DefaultReturn::Zero);
        }

        // NOTE: We intentionally do NOT call define_function here.
        // This method is for IR inspection only.

        // Run CFG cleanup to show optimized IR
        crate::control_flow::cleanup_cfg(&mut self.jit.ctx.func);

        // Run loop parameter optimization if enabled
        if self.jit.loop_param_opt_enabled() {
            crate::control_flow::optimize_loop_params(&mut self.jit.ctx.func);
        }

        Ok(())
    }
}
