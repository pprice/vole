// src/codegen/compiler.rs

use cranelift::codegen::ir::{BlockArg, TrapCode};
use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};
use std::collections::HashMap;

use crate::codegen::JitContext;
use crate::frontend::{
    self, BinaryOp, Decl, Expr, ExprKind, FuncDecl, Interner, Program, Stmt, StringPart, Symbol,
    TestsDecl, TypeExpr, UnaryOp,
};
use crate::sema::Type;

/// Metadata about a compiled test
#[derive(Debug, Clone)]
pub struct TestInfo {
    pub name: String,      // "basic math"
    pub func_name: String, // "__test_0"
    pub file: String,      // "test/unit/test_basic.vole"
    pub line: u32,
}

/// Context for control flow during compilation
pub struct ControlFlowCtx {
    /// Stack of loop exit blocks for break statements
    loop_exits: Vec<Block>,
}

impl ControlFlowCtx {
    pub fn new() -> Self {
        Self {
            loop_exits: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, exit_block: Block) {
        self.loop_exits.push(exit_block);
    }

    pub fn pop_loop(&mut self) {
        self.loop_exits.pop();
    }

    pub fn current_loop_exit(&self) -> Option<Block> {
        self.loop_exits.last().copied()
    }
}

impl Default for ControlFlowCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// Compiled value with its type
#[derive(Clone, Copy)]
pub struct CompiledValue {
    pub value: Value,
    pub ty: types::Type,
    /// True if this value is a string pointer (needed since pointer_type == I64 on 64-bit)
    pub is_string: bool,
}

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    interner: &'a Interner,
    pointer_type: types::Type,
    tests: Vec<TestInfo>,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, interner: &'a Interner) -> Self {
        let pointer_type = jit.pointer_type();
        Self {
            jit,
            interner,
            pointer_type,
            tests: Vec::new(),
        }
    }

    /// Set the source file path for error reporting.
    /// The string is stored in the JitContext so it lives as long as the JIT code.
    pub fn set_source_file(&mut self, file: &str) {
        self.jit.set_source_file(file);
    }

    /// Get the source file pointer and length from the JitContext.
    fn source_file_ptr(&self) -> (*const u8, usize) {
        self.jit.source_file_ptr()
    }

    /// Get the source file as a string for TestInfo metadata.
    fn source_file_str(&self) -> String {
        let (ptr, len) = self.jit.source_file_ptr();
        if ptr.is_null() || len == 0 {
            String::new()
        } else {
            unsafe {
                std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len)).to_string()
            }
        }
    }

    /// Take the compiled test metadata, leaving an empty vec
    pub fn take_tests(&mut self) -> Vec<TestInfo> {
        std::mem::take(&mut self.tests)
    }

    /// Compile a complete program
    pub fn compile_program(&mut self, program: &Program) -> Result<(), String> {
        // Count total tests to assign unique IDs
        let mut test_count = 0usize;

        // First pass: declare all functions and tests
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let sig = self.create_function_signature(func);
                    let name = self.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                }
                Decl::Tests(tests_decl) => {
                    // Declare each test as __test_N with signature () -> i64
                    for _ in &tests_decl.tests {
                        let func_name = format!("__test_{}", test_count);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        self.jit.declare_function(&func_name, &sig);
                        test_count += 1;
                    }
                }
            }
        }

        // Reset counter for second pass
        test_count = 0;

        // Second pass: compile function bodies and tests
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.compile_function(func)?;
                }
                Decl::Tests(tests_decl) => {
                    self.compile_tests(tests_decl, &mut test_count)?;
                }
            }
        }

        Ok(())
    }

    fn create_function_signature(&self, func: &FuncDecl) -> Signature {
        let mut params = Vec::new();
        for param in &func.params {
            params.push(type_to_cranelift(
                &resolve_type_expr(&param.ty),
                self.pointer_type,
            ));
        }

        let ret = func
            .return_type
            .as_ref()
            .map(|t| type_to_cranelift(&resolve_type_expr(t), self.pointer_type));

        self.jit.create_signature(&params, ret)
    }

    fn compile_function(&mut self, func: &FuncDecl) -> Result<(), String> {
        let name = self.interner.resolve(func.name);
        let func_id = *self.jit.func_ids.get(name).unwrap();

        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig.clone();

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| type_to_cranelift(&resolve_type_expr(&p.ty), self.pointer_type))
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

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
            for ((name, ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, var);
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &self.jit.func_ids,
                source_file_ptr,
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
            let func_name = format!("__test_{}", *test_count);
            let func_id = *self.jit.func_ids.get(&func_name).unwrap();

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
                    interner: self.interner,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_ids: &self.jit.func_ids,
                    source_file_ptr,
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
                func_name: func_name.clone(),
                file: self.source_file_str(),
                line,
            });

            *test_count += 1;
        }

        Ok(())
    }
}

fn resolve_type_expr(ty: &TypeExpr) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(_) => Type::Error,
    }
}

fn type_to_cranelift(ty: &Type, pointer_type: types::Type) -> types::Type {
    match ty {
        Type::I32 => types::I32,
        Type::I64 => types::I64,
        Type::F64 => types::F64,
        Type::Bool => types::I8,
        Type::String => pointer_type,
        _ => types::I64, // Default
    }
}

/// Context for compiling expressions and statements
/// Bundles common parameters to reduce function argument count
struct CompileCtx<'a> {
    interner: &'a Interner,
    pointer_type: types::Type,
    module: &'a mut JITModule,
    func_ids: &'a HashMap<String, FuncId>,
    source_file_ptr: (*const u8, usize),
}

/// Returns true if a terminating statement (return/break) was compiled
fn compile_block(
    builder: &mut FunctionBuilder,
    block: &frontend::Block,
    variables: &mut HashMap<Symbol, Variable>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    let mut terminated = false;
    for stmt in &block.stmts {
        if terminated {
            break; // Don't compile unreachable code
        }
        terminated = compile_stmt(builder, stmt, variables, cf_ctx, ctx)?;
    }
    Ok(terminated)
}

/// Returns true if this statement terminates (return/break)
fn compile_stmt(
    builder: &mut FunctionBuilder,
    stmt: &Stmt,
    variables: &mut HashMap<Symbol, Variable>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    match stmt {
        Stmt::Let(let_stmt) => {
            let init = compile_expr(builder, &let_stmt.init, variables, ctx)?;

            let var = builder.declare_var(init.ty);
            builder.def_var(var, init.value);
            variables.insert(let_stmt.name, var);
            Ok(false)
        }
        Stmt::Expr(expr_stmt) => {
            compile_expr(builder, &expr_stmt.expr, variables, ctx)?;
            Ok(false)
        }
        Stmt::Return(ret) => {
            if let Some(value) = &ret.value {
                let compiled = compile_expr(builder, value, variables, ctx)?;
                builder.ins().return_(&[compiled.value]);
            } else {
                builder.ins().return_(&[]);
            }
            Ok(true)
        }
        Stmt::While(while_stmt) => {
            // Create blocks
            let header_block = builder.create_block(); // Condition check
            let body_block = builder.create_block(); // Loop body
            let exit_block = builder.create_block(); // After loop

            // Jump to header
            builder.ins().jump(header_block, &[]);

            // Header block - check condition
            builder.switch_to_block(header_block);
            let cond = compile_expr(builder, &while_stmt.condition, variables, ctx)?;
            // Extend bool to i32 for comparison if needed
            let cond_i32 = builder.ins().uextend(types::I32, cond.value);
            builder
                .ins()
                .brif(cond_i32, body_block, &[], exit_block, &[]);

            // Body block
            builder.switch_to_block(body_block);
            cf_ctx.push_loop(exit_block);
            let body_terminated = compile_block(builder, &while_stmt.body, variables, cf_ctx, ctx)?;
            cf_ctx.pop_loop();

            // Jump back to header (if not already terminated by break/return)
            if !body_terminated {
                builder.ins().jump(header_block, &[]);
            }

            // Continue in exit block
            builder.switch_to_block(exit_block);

            // Seal blocks
            builder.seal_block(header_block);
            builder.seal_block(body_block);
            builder.seal_block(exit_block);

            Ok(false)
        }
        Stmt::If(if_stmt) => {
            let cond = compile_expr(builder, &if_stmt.condition, variables, ctx)?;
            let cond_i32 = builder.ins().uextend(types::I32, cond.value);

            let then_block = builder.create_block();
            let else_block = builder.create_block();
            let merge_block = builder.create_block();

            builder
                .ins()
                .brif(cond_i32, then_block, &[], else_block, &[]);

            // Then branch
            builder.switch_to_block(then_block);
            let then_terminated =
                compile_block(builder, &if_stmt.then_branch, variables, cf_ctx, ctx)?;
            if !then_terminated {
                builder.ins().jump(merge_block, &[]);
            }

            // Else branch
            builder.switch_to_block(else_block);
            let else_terminated = if let Some(else_branch) = &if_stmt.else_branch {
                compile_block(builder, else_branch, variables, cf_ctx, ctx)?
            } else {
                false
            };
            if !else_terminated {
                builder.ins().jump(merge_block, &[]);
            }

            // Continue after if
            builder.switch_to_block(merge_block);

            builder.seal_block(then_block);
            builder.seal_block(else_block);
            builder.seal_block(merge_block);

            // If both branches terminate, the if statement terminates
            Ok(then_terminated && else_terminated)
        }
        Stmt::Break(_) => {
            if let Some(exit_block) = cf_ctx.current_loop_exit() {
                builder.ins().jump(exit_block, &[]);
            }
            Ok(true)
        }
    }
}

fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::IntLiteral(n) => {
            let val = builder.ins().iconst(types::I64, *n);
            Ok(CompiledValue {
                value: val,
                ty: types::I64,
                is_string: false,
            })
        }
        ExprKind::FloatLiteral(n) => {
            let val = builder.ins().f64const(*n);
            Ok(CompiledValue {
                value: val,
                ty: types::F64,
                is_string: false,
            })
        }
        ExprKind::BoolLiteral(b) => {
            let val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
            Ok(CompiledValue {
                value: val,
                ty: types::I8,
                is_string: false,
            })
        }
        ExprKind::Identifier(sym) => {
            if let Some(&var) = variables.get(sym) {
                let val = builder.use_var(var);
                // Get the type from the variable declaration
                let ty = builder.func.dfg.value_type(val);
                // Note: We don't track is_string for variables yet - they inherit from their init
                Ok(CompiledValue {
                    value: val,
                    ty,
                    is_string: false,
                })
            } else {
                Err(format!(
                    "undefined variable: {}",
                    ctx.interner.resolve(*sym)
                ))
            }
        }
        ExprKind::Binary(bin) => {
            // Handle short-circuit evaluation for And/Or before evaluating both sides
            match bin.op {
                BinaryOp::And => {
                    // Short-circuit AND: if left is false, return false without evaluating right
                    let left = compile_expr(builder, &bin.left, variables, ctx)?;

                    let then_block = builder.create_block();
                    let else_block = builder.create_block();
                    let merge_block = builder.create_block();
                    builder.append_block_param(merge_block, types::I8);

                    builder
                        .ins()
                        .brif(left.value, then_block, &[], else_block, &[]);

                    // Then block: left was true, evaluate right side
                    builder.switch_to_block(then_block);
                    builder.seal_block(then_block);
                    let right = compile_expr(builder, &bin.right, variables, ctx)?;
                    let right_arg = BlockArg::from(right.value);
                    builder.ins().jump(merge_block, &[right_arg]);

                    // Else block: left was false, short-circuit with false
                    builder.switch_to_block(else_block);
                    builder.seal_block(else_block);
                    let false_val = builder.ins().iconst(types::I8, 0);
                    let false_arg = BlockArg::from(false_val);
                    builder.ins().jump(merge_block, &[false_arg]);

                    // Merge block
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let result = builder.block_params(merge_block)[0];

                    return Ok(CompiledValue {
                        value: result,
                        ty: types::I8,
                        is_string: false,
                    });
                }
                BinaryOp::Or => {
                    // Short-circuit OR: if left is true, return true without evaluating right
                    let left = compile_expr(builder, &bin.left, variables, ctx)?;

                    let then_block = builder.create_block();
                    let else_block = builder.create_block();
                    let merge_block = builder.create_block();
                    builder.append_block_param(merge_block, types::I8);

                    builder
                        .ins()
                        .brif(left.value, then_block, &[], else_block, &[]);

                    // Then block: left was true, short-circuit with true
                    builder.switch_to_block(then_block);
                    builder.seal_block(then_block);
                    let true_val = builder.ins().iconst(types::I8, 1);
                    let true_arg = BlockArg::from(true_val);
                    builder.ins().jump(merge_block, &[true_arg]);

                    // Else block: left was false, evaluate right side
                    builder.switch_to_block(else_block);
                    builder.seal_block(else_block);
                    let right = compile_expr(builder, &bin.right, variables, ctx)?;
                    let right_arg = BlockArg::from(right.value);
                    builder.ins().jump(merge_block, &[right_arg]);

                    // Merge block
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let result = builder.block_params(merge_block)[0];

                    return Ok(CompiledValue {
                        value: result,
                        ty: types::I8,
                        is_string: false,
                    });
                }
                _ => {} // Fall through to regular binary handling
            }

            let left = compile_expr(builder, &bin.left, variables, ctx)?;
            let right = compile_expr(builder, &bin.right, variables, ctx)?;

            // Determine result type (promote to wider type)
            let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
                types::F64
            } else {
                types::I64
            };

            // Convert operands if needed
            let left_val = convert_to_type(builder, left, result_ty);
            let right_val = convert_to_type(builder, right, result_ty);

            let result = match bin.op {
                BinaryOp::Add => {
                    if result_ty == types::F64 {
                        builder.ins().fadd(left_val, right_val)
                    } else {
                        builder.ins().iadd(left_val, right_val)
                    }
                }
                BinaryOp::Sub => {
                    if result_ty == types::F64 {
                        builder.ins().fsub(left_val, right_val)
                    } else {
                        builder.ins().isub(left_val, right_val)
                    }
                }
                BinaryOp::Mul => {
                    if result_ty == types::F64 {
                        builder.ins().fmul(left_val, right_val)
                    } else {
                        builder.ins().imul(left_val, right_val)
                    }
                }
                BinaryOp::Div => {
                    if result_ty == types::F64 {
                        builder.ins().fdiv(left_val, right_val)
                    } else {
                        builder.ins().sdiv(left_val, right_val)
                    }
                }
                BinaryOp::Mod => {
                    if result_ty == types::F64 {
                        // Floating-point modulo: a - (a/b).floor() * b
                        let div = builder.ins().fdiv(left_val, right_val);
                        let floor = builder.ins().floor(div);
                        let mul = builder.ins().fmul(floor, right_val);
                        builder.ins().fsub(left_val, mul)
                    } else {
                        builder.ins().srem(left_val, right_val)
                    }
                }
                BinaryOp::Eq => {
                    if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::Equal, left_val, right_val)
                    }
                }
                BinaryOp::Ne => {
                    if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
                    }
                }
                BinaryOp::Lt => {
                    if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::LessThan, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedLessThan, left_val, right_val)
                    }
                }
                BinaryOp::Gt => {
                    if result_ty == types::F64 {
                        builder
                            .ins()
                            .fcmp(FloatCC::GreaterThan, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThan, left_val, right_val)
                    }
                }
                BinaryOp::Le => {
                    if result_ty == types::F64 {
                        builder
                            .ins()
                            .fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
                    }
                }
                BinaryOp::Ge => {
                    if result_ty == types::F64 {
                        builder
                            .ins()
                            .fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
                    }
                }
                // And/Or are handled above with short-circuit evaluation
                BinaryOp::And | BinaryOp::Or => unreachable!(),
            };

            // Comparison operators return I8 (bool)
            let final_ty = match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => types::I8,
                // And/Or are handled above with early return
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                _ => result_ty,
            };

            Ok(CompiledValue {
                value: result,
                ty: final_ty,
                is_string: false,
            })
        }
        ExprKind::Unary(un) => {
            let operand = compile_expr(builder, &un.operand, variables, ctx)?;
            let result = match un.op {
                UnaryOp::Neg => {
                    if operand.ty == types::F64 {
                        builder.ins().fneg(operand.value)
                    } else {
                        builder.ins().ineg(operand.value)
                    }
                }
                UnaryOp::Not => {
                    // Logical not: 1 - x for boolean
                    let one = builder.ins().iconst(types::I8, 1);
                    builder.ins().isub(one, operand.value)
                }
            };
            Ok(CompiledValue {
                value: result,
                ty: operand.ty,
                is_string: false,
            })
        }
        ExprKind::Assign(assign) => {
            let value = compile_expr(builder, &assign.value, variables, ctx)?;
            if let Some(&var) = variables.get(&assign.target) {
                builder.def_var(var, value.value);
                Ok(value)
            } else {
                Err(format!(
                    "undefined variable: {}",
                    ctx.interner.resolve(assign.target)
                ))
            }
        }
        ExprKind::Grouping(inner) => compile_expr(builder, inner, variables, ctx),
        ExprKind::StringLiteral(s) => {
            compile_string_literal(builder, s, ctx.pointer_type, ctx.module, ctx.func_ids)
        }
        ExprKind::Call(call) => compile_call(builder, call, expr.span.line, variables, ctx),
        ExprKind::InterpolatedString(parts) => {
            compile_interpolated_string(builder, parts, variables, ctx)
        }
    }
}

/// Compile a string literal by calling vole_string_new
fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: types::Type,
    module: &mut JITModule,
    func_ids: &HashMap<String, FuncId>,
) -> Result<CompiledValue, String> {
    // Get the vole_string_new function
    let func_id = func_ids
        .get("vole_string_new")
        .ok_or_else(|| "vole_string_new not found".to_string())?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

    // Pass the string data pointer and length as constants
    // The string is a Rust &str, so we can get its pointer and length
    let data_ptr = s.as_ptr() as i64;
    let len = s.len() as i64;

    let data_val = builder.ins().iconst(pointer_type, data_ptr);
    let len_val = builder.ins().iconst(pointer_type, len);

    // Call vole_string_new(data, len) -> *mut RcString
    let call = builder.ins().call(func_ref, &[data_val, len_val]);
    let result = builder.inst_results(call)[0];

    Ok(CompiledValue {
        value: result,
        ty: pointer_type,
        is_string: true,
    })
}

/// Compile a function call expression
fn compile_call(
    builder: &mut FunctionBuilder,
    call: &crate::frontend::CallExpr,
    call_line: u32,
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Get the callee name - must be an identifier for now
    let callee_name = match &call.callee.kind {
        ExprKind::Identifier(sym) => ctx.interner.resolve(*sym),
        _ => return Err("only simple function calls are supported".to_string()),
    };

    // Handle builtin functions
    match callee_name {
        "println" => compile_println(builder, &call.args, variables, ctx),
        "print_char" => compile_print_char(builder, &call.args, variables, ctx),
        "assert" => compile_assert(builder, &call.args, call_line, variables, ctx),
        _ => compile_user_function_call(builder, callee_name, &call.args, variables, ctx),
    }
}

/// Compile println builtin - dispatches to correct vole_println_* based on argument type
fn compile_println(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("println expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Dispatch based on argument type
    // We use is_string flag to distinguish strings from regular I64 values
    let func_name = if arg.is_string {
        "vole_println_string"
    } else if arg.ty == types::F64 {
        "vole_println_f64"
    } else if arg.ty == types::I8 {
        "vole_println_bool"
    } else {
        "vole_println_i64"
    };

    let func_id = ctx
        .func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[arg.value]);

    // println returns void, but we need to return something
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        is_string: false,
    })
}

/// Compile print_char builtin for mandelbrot ASCII output
fn compile_print_char(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("print_char expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Convert to u8 if needed (truncate from i64)
    let char_val = if arg.ty == types::I64 {
        builder.ins().ireduce(types::I8, arg.value)
    } else if arg.ty == types::I8 {
        arg.value
    } else {
        return Err("print_char expects an integer argument".to_string());
    };

    let func_id = ctx
        .func_ids
        .get("vole_print_char")
        .ok_or_else(|| "vole_print_char not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[char_val]);

    // Return void (as i64 zero)
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        is_string: false,
    })
}

/// Compile assert builtin - checks condition and calls vole_assert_fail if false
fn compile_assert(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    call_line: u32,
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("assert expects exactly one argument".to_string());
    }

    // Compile the condition
    let cond = compile_expr(builder, &args[0], variables, ctx)?;

    // Create pass and fail blocks
    let pass_block = builder.create_block();
    let fail_block = builder.create_block();

    // Branch on condition (extend bool to i32 for brif)
    let cond_i32 = builder.ins().uextend(types::I32, cond.value);
    builder
        .ins()
        .brif(cond_i32, pass_block, &[], fail_block, &[]);

    // Fail block: call vole_assert_fail and trap
    builder.switch_to_block(fail_block);
    {
        // Get vole_assert_fail function
        let func_id = ctx
            .func_ids
            .get("vole_assert_fail")
            .ok_or_else(|| "vole_assert_fail not found".to_string())?;
        let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

        // Pass source file pointer and length from JitContext
        // The source_file_ptr points to memory in JitContext that lives as long as the JIT code
        let (file_ptr, file_len) = ctx.source_file_ptr;
        let line = call_line as i32;

        let file_ptr_val = builder.ins().iconst(ctx.pointer_type, file_ptr as i64);
        let file_len_val = builder.ins().iconst(types::I64, file_len as i64);
        let line_val = builder.ins().iconst(types::I32, line as i64);

        builder
            .ins()
            .call(func_ref, &[file_ptr_val, file_len_val, line_val]);

        // Trap after calling assert_fail (this should not be reached due to longjmp, but
        // we need to terminate the block)
        // Note: TrapCode::user(0) returns None because TrapCode uses NonZeroU8, so we use 1
        builder.ins().trap(TrapCode::unwrap_user(1));
    }

    // Seal fail block
    builder.seal_block(fail_block);

    // Pass block: continue execution
    builder.switch_to_block(pass_block);
    builder.seal_block(pass_block);

    // Assert returns void (as i64 zero)
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        is_string: false,
    })
}

/// Compile a call to a user-defined function
fn compile_user_function_call(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Expr],
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let func_id = ctx
        .func_ids
        .get(name)
        .ok_or_else(|| format!("undefined function: {}", name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    // Compile arguments
    let mut arg_values = Vec::new();
    for arg in args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        arg_values.push(compiled.value);
    }

    let call = builder.ins().call(func_ref, &arg_values);
    let results = builder.inst_results(call);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            is_string: false,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        // TODO: Track is_string for function return types properly
        Ok(CompiledValue {
            value: result,
            ty,
            is_string: false,
        })
    }
}

/// Compile an interpolated string by converting parts and concatenating
fn compile_interpolated_string(
    builder: &mut FunctionBuilder,
    parts: &[StringPart],
    variables: &mut HashMap<Symbol, Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if parts.is_empty() {
        // Empty interpolated string - return empty string
        return compile_string_literal(builder, "", ctx.pointer_type, ctx.module, ctx.func_ids);
    }

    // Convert each part to a string value
    let mut string_values: Vec<Value> = Vec::new();
    for part in parts {
        let str_val = match part {
            StringPart::Literal(s) => {
                compile_string_literal(builder, s, ctx.pointer_type, ctx.module, ctx.func_ids)?
                    .value
            }
            StringPart::Expr(expr) => {
                let compiled = compile_expr(builder, expr, variables, ctx)?;
                value_to_string(
                    builder,
                    compiled,
                    ctx.pointer_type,
                    ctx.module,
                    ctx.func_ids,
                )?
            }
        };
        string_values.push(str_val);
    }

    // Concatenate all parts
    if string_values.len() == 1 {
        return Ok(CompiledValue {
            value: string_values[0],
            ty: ctx.pointer_type,
            is_string: true,
        });
    }

    let concat_func_id = ctx
        .func_ids
        .get("vole_string_concat")
        .ok_or_else(|| "vole_string_concat not found".to_string())?;
    let concat_func_ref = ctx
        .module
        .declare_func_in_func(*concat_func_id, builder.func);

    let mut result = string_values[0];
    for &next in &string_values[1..] {
        let call = builder.ins().call(concat_func_ref, &[result, next]);
        result = builder.inst_results(call)[0];
    }

    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        is_string: true,
    })
}

/// Convert a compiled value to a string by calling the appropriate vole_*_to_string function
fn value_to_string(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    _pointer_type: types::Type,
    module: &mut JITModule,
    func_ids: &HashMap<String, FuncId>,
) -> Result<Value, String> {
    // If already a string, return as-is
    if val.is_string {
        return Ok(val.value);
    }

    let func_name = if val.ty == types::F64 {
        "vole_f64_to_string"
    } else if val.ty == types::I8 {
        "vole_bool_to_string"
    } else {
        "vole_i64_to_string"
    };

    let func_id = func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

    let call = builder.ins().call(func_ref, &[val.value]);
    Ok(builder.inst_results(call)[0])
}

fn convert_to_type(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    target: types::Type,
) -> Value {
    if val.ty == target {
        return val.value;
    }

    if target == types::F64 {
        // Convert int to float
        if val.ty == types::I64 || val.ty == types::I32 {
            return builder.ins().fcvt_from_sint(types::F64, val.value);
        }
    }

    if target == types::I64 && val.ty == types::I32 {
        return builder.ins().sextend(types::I64, val.value);
    }

    val.value
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;

    fn compile_and_run(source: &str) -> i64 {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let mut jit = JitContext::new();
        {
            let mut compiler = Compiler::new(&mut jit, &interner);
            compiler.compile_program(&program).unwrap();
        }
        jit.finalize();

        let fn_ptr = jit.get_function_ptr("main").unwrap();
        let main: extern "C" fn() -> i64 = unsafe { std::mem::transmute(fn_ptr) };
        main()
    }

    #[test]
    fn compile_return_literal() {
        let result = compile_and_run("func main() -> i64 { return 42 }");
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_arithmetic() {
        let result = compile_and_run("func main() -> i64 { return 10 + 32 }");
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_let_and_return() {
        let result = compile_and_run("func main() -> i64 { let x = 40\n return x + 2 }");
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_multiple_ops() {
        let result = compile_and_run("func main() -> i64 { return 2 + 3 * 10 }");
        assert_eq!(result, 32); // 2 + 30
    }

    #[test]
    fn compile_while_loop() {
        let source = r#"
func main() -> i64 {
    let mut x = 0
    while x < 10 {
        x = x + 1
    }
    return x
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 10);
    }

    #[test]
    fn compile_if_else() {
        let source = r#"
func main() -> i64 {
    let x = 10
    if x > 5 {
        return 1
    } else {
        return 0
    }
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 1);
    }

    #[test]
    fn compile_nested_while_with_break() {
        let source = r#"
func main() -> i64 {
    let mut sum = 0
    let mut i = 0
    while i < 100 {
        if i == 5 {
            break
        }
        sum = sum + i
        i = i + 1
    }
    return sum
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 10); // 0+1+2+3+4 = 10
    }

    #[test]
    fn compile_user_function_call() {
        let source = r#"
func add(a: i64, b: i64) -> i64 {
    return a + b
}

func main() -> i64 {
    return add(10, 32)
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_user_function_call_no_args() {
        let source = r#"
func get_answer() -> i64 {
    return 42
}

func main() -> i64 {
    return get_answer()
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_recursive_function() {
        let source = r#"
func factorial(n: i64) -> i64 {
    if n <= 1 {
        return 1
    }
    return n * factorial(n - 1)
}

func main() -> i64 {
    return factorial(5)
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 120); // 5! = 120
    }

    #[test]
    fn compile_println_i64() {
        // Test that println compiles and runs without crashing
        let source = r#"
func main() -> i64 {
    println(42)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_println_bool() {
        let source = r#"
func main() -> i64 {
    println(true)
    println(false)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_println_f64() {
        let source = r#"
func main() -> i64 {
    println(3.14)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_println_string() {
        let source = r#"
func main() -> i64 {
    println("Hello, World!")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_print_char() {
        let source = r#"
func main() -> i64 {
    print_char(65)
    print_char(10)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_string_literal_in_let() {
        let source = r#"
func main() -> i64 {
    let s = "test"
    println(s)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string() {
        let source = r#"
func main() -> i64 {
    let x = 42
    println("The answer is {x}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string_multiple() {
        let source = r#"
func main() -> i64 {
    let a = 1
    let b = 2
    println("{a} + {b} = {a + b}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string_with_bool() {
        let source = r#"
func main() -> i64 {
    let flag = true
    println("flag is {flag}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string_with_float() {
        let source = r#"
func main() -> i64 {
    let pi = 3.14159
    println("pi = {pi}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }
}
