// src/codegen/compiler.rs

use cranelift::codegen::ir::{BlockArg, TrapCode};
use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{FuncId, Module};
use std::collections::HashMap;

use crate::codegen::JitContext;
use crate::frontend::{
    self, BinaryOp, Decl, Expr, ExprKind, FuncDecl, Interner, LambdaBody, LambdaExpr, LetStmt,
    Pattern, Program, Stmt, StringPart, Symbol, TestCase, TestsDecl, TypeExpr, UnaryOp,
};
use crate::sema::{FunctionType, Type};

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
    /// Stack of loop continue blocks for continue statements
    loop_continues: Vec<Block>,
}

impl ControlFlowCtx {
    pub fn new() -> Self {
        Self {
            loop_exits: Vec::new(),
            loop_continues: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, exit_block: Block, continue_block: Block) {
        self.loop_exits.push(exit_block);
        self.loop_continues.push(continue_block);
    }

    pub fn pop_loop(&mut self) {
        self.loop_exits.pop();
        self.loop_continues.pop();
    }

    pub fn current_loop_exit(&self) -> Option<Block> {
        self.loop_exits.last().copied()
    }

    pub fn current_loop_continue(&self) -> Option<Block> {
        self.loop_continues.last().copied()
    }
}

impl Default for ControlFlowCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// Compiled value with its type
#[derive(Clone)]
pub struct CompiledValue {
    pub value: Value,
    pub ty: types::Type,
    /// The Vole type of this value (needed to distinguish strings/arrays from regular I64)
    pub vole_type: Type,
}

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    interner: &'a Interner,
    pointer_type: types::Type,
    tests: Vec<TestInfo>,
    /// Global variable declarations (let statements at module level)
    globals: Vec<LetStmt>,
    /// Counter for generating unique lambda names
    lambda_counter: usize,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, interner: &'a Interner) -> Self {
        let pointer_type = jit.pointer_type();
        Self {
            jit,
            interner,
            pointer_type,
            tests: Vec::new(),
            globals: Vec::new(),
            lambda_counter: 0,
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

        // First pass: declare all functions and tests, collect globals
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
                Decl::Let(let_stmt) => {
                    // Collect global variable declarations
                    self.globals.push(let_stmt.clone());
                }
            }
        }

        // Reset counter for second pass
        test_count = 0;

        // Second pass: compile function bodies and tests
        // Note: Decl::Let globals are handled by inlining their initializers
        // when referenced (see compile_expr for ExprKind::Identifier)
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.compile_function(func)?;
                }
                Decl::Tests(tests_decl) => {
                    self.compile_tests(tests_decl, &mut test_count)?;
                }
                Decl::Let(_) => {
                    // Globals are handled during identifier lookup
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
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| resolve_type_expr(&p.ty))
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
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
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
                    func_ids: &mut self.jit.func_ids,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
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

    /// Compile program to CLIF IR and write to the given writer.
    /// Does not finalize for execution - just generates IR for inspection.
    pub fn compile_to_ir<W: std::io::Write>(
        &mut self,
        program: &Program,
        writer: &mut W,
        include_tests: bool,
    ) -> Result<(), String> {
        // First pass: declare all functions so they can reference each other
        let mut test_count = 0usize;
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let sig = self.create_function_signature(func);
                    let name = self.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for _ in &tests_decl.tests {
                        let func_name = format!("__test_{}", test_count);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        self.jit.declare_function(&func_name, &sig);
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
                    let name = self.interner.resolve(func.name);
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
        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig.clone();

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| type_to_cranelift(&resolve_type_expr(&p.ty), self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| resolve_type_expr(&p.ty))
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
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
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
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
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
}

fn resolve_type_expr(ty: &TypeExpr) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(_) => Type::Error,
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type_expr(elem);
            Type::Array(Box::new(elem_ty))
        }
        TypeExpr::Optional(inner) => {
            // T? desugars to T | nil
            let inner_ty = resolve_type_expr(inner);
            Type::Union(vec![inner_ty, Type::Nil])
        }
        TypeExpr::Union(variants) => {
            let variant_types: Vec<Type> = variants.iter().map(resolve_type_expr).collect();
            Type::normalize_union(variant_types)
        }
        TypeExpr::Nil => Type::Nil,
        TypeExpr::Function { .. } => {
            // Function types will be handled in a later task
            Type::Error
        }
    }
}

fn type_to_cranelift(ty: &Type, pointer_type: types::Type) -> types::Type {
    match ty {
        Type::I8 | Type::U8 => types::I8,
        Type::I16 | Type::U16 => types::I16,
        Type::I32 | Type::U32 => types::I32,
        Type::I64 | Type::U64 => types::I64,
        Type::I128 => types::I128,
        Type::F32 => types::F32,
        Type::F64 => types::F64,
        Type::Bool => types::I8,
        Type::String => pointer_type,
        Type::Nil => types::I8,         // Nil uses minimal representation
        Type::Union(_) => pointer_type, // Unions are passed by pointer
        _ => types::I64,                // Default
    }
}

/// Get the size in bytes for a Vole type (used for union layout)
fn type_size(ty: &Type, pointer_type: types::Type) -> u32 {
    match ty {
        Type::I8 | Type::U8 | Type::Bool => 1,
        Type::I16 | Type::U16 => 2,
        Type::I32 | Type::U32 | Type::F32 => 4,
        Type::I64 | Type::U64 | Type::F64 => 8,
        Type::I128 => 16,
        Type::String | Type::Array(_) => pointer_type.bytes(), // pointer size
        Type::Nil | Type::Void => 0,
        Type::Union(variants) => {
            // Tag (1 byte) + padding + max payload size, aligned to 8
            let max_payload = variants
                .iter()
                .map(|t| type_size(t, pointer_type))
                .max()
                .unwrap_or(0);
            // Layout: [tag:1][padding:7][payload:max_payload] aligned to 8
            8 + max_payload.div_ceil(8) * 8
        }
        _ => 8, // default
    }
}

/// Wrap a value in a union representation (stack slot with tag + payload)
fn construct_union(
    builder: &mut FunctionBuilder,
    value: CompiledValue,
    union_type: &Type,
    pointer_type: types::Type,
) -> Result<CompiledValue, String> {
    use cranelift::prelude::StackSlotData;
    use cranelift::prelude::StackSlotKind;

    let Type::Union(variants) = union_type else {
        return Err("Expected union type".to_string());
    };

    // Find the tag for this value's type (with coercion support for integer literals)
    // First try exact match
    let (tag, actual_value, actual_type) =
        if let Some(pos) = variants.iter().position(|v| v == &value.vole_type) {
            (pos, value.value, value.vole_type.clone())
        } else {
            // Try to find a compatible integer type (for literal coercion)
            // When assigning I64 literal to i32?, we need to narrow to I32
            let compatible = variants.iter().enumerate().find(|(_, v)| {
                // Check if value type can narrow to this variant
                value.vole_type.is_integer() && v.is_integer() && value.vole_type.can_widen_to(v)
                    || v.is_integer() && value.vole_type.is_integer()
            });

            match compatible {
                Some((pos, variant_type)) => {
                    // Narrow the integer value to the variant type
                    let target_ty = type_to_cranelift(variant_type, pointer_type);
                    let narrowed = if target_ty.bytes() < value.ty.bytes() {
                        builder.ins().ireduce(target_ty, value.value)
                    } else if target_ty.bytes() > value.ty.bytes() {
                        builder.ins().sextend(target_ty, value.value)
                    } else {
                        value.value
                    };
                    (pos, narrowed, variant_type.clone())
                }
                None => {
                    return Err(format!(
                        "Type {:?} not in union {:?}",
                        value.vole_type, variants
                    ));
                }
            }
        };

    // Allocate stack slot for the union
    let union_size = type_size(union_type, pointer_type);
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        union_size,
        0,
    ));

    // Store tag at offset 0
    let tag_val = builder.ins().iconst(types::I8, tag as i64);
    builder.ins().stack_store(tag_val, slot, 0);

    // Store payload at offset 8 (after alignment padding)
    if actual_type != Type::Nil {
        builder.ins().stack_store(actual_value, slot, 8);
    }

    // Return pointer to the stack slot
    let ptr = builder.ins().stack_addr(pointer_type, slot, 0);
    Ok(CompiledValue {
        value: ptr,
        ty: pointer_type,
        vole_type: union_type.clone(),
    })
}

/// Context for compiling expressions and statements
/// Bundles common parameters to reduce function argument count
struct CompileCtx<'a> {
    interner: &'a Interner,
    pointer_type: types::Type,
    module: &'a mut JITModule,
    func_ids: &'a mut HashMap<String, FuncId>,
    source_file_ptr: (*const u8, usize),
    /// Global variable declarations for lookup when identifier not in local scope
    globals: &'a [LetStmt],
    /// Counter for generating unique lambda names
    lambda_counter: &'a mut usize,
}

/// Returns true if a terminating statement (return/break) was compiled
fn compile_block(
    builder: &mut FunctionBuilder,
    block: &frontend::Block,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
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
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    match stmt {
        Stmt::Let(let_stmt) => {
            let init = compile_expr(builder, &let_stmt.init, variables, ctx)?;

            // Check if there's a type annotation that is a union type
            let (final_value, final_type) = if let Some(ty_expr) = &let_stmt.ty {
                let declared_type = resolve_type_expr(ty_expr);
                // If declared type is a union and init is not, wrap init into the union
                if matches!(&declared_type, Type::Union(_))
                    && !matches!(&init.vole_type, Type::Union(_))
                {
                    let wrapped = construct_union(builder, init, &declared_type, ctx.pointer_type)?;
                    (wrapped.value, wrapped.vole_type)
                } else {
                    (init.value, init.vole_type)
                }
            } else {
                (init.value, init.vole_type)
            };

            let cranelift_ty = type_to_cranelift(&final_type, ctx.pointer_type);
            let var = builder.declare_var(cranelift_ty);
            builder.def_var(var, final_value);
            variables.insert(let_stmt.name, (var, final_type));
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
            // For while loops, continue jumps to the header (condition check)
            cf_ctx.push_loop(exit_block, header_block);
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
        Stmt::For(for_stmt) => {
            if let ExprKind::Range(range) = &for_stmt.iterable.kind {
                // Compile range bounds
                let start_val = compile_expr(builder, &range.start, variables, ctx)?;
                let end_val = compile_expr(builder, &range.end, variables, ctx)?;

                // Create loop variable as Cranelift variable
                let var = builder.declare_var(types::I64);
                builder.def_var(var, start_val.value);
                variables.insert(for_stmt.var_name, (var, Type::I64));

                // Create blocks
                let header = builder.create_block();
                let body_block = builder.create_block();
                let continue_block = builder.create_block();
                let exit_block = builder.create_block();

                builder.ins().jump(header, &[]);

                // Header: load current, compare to end
                builder.switch_to_block(header);
                let current = builder.use_var(var);
                let cmp = if range.inclusive {
                    builder
                        .ins()
                        .icmp(IntCC::SignedLessThanOrEqual, current, end_val.value)
                } else {
                    builder
                        .ins()
                        .icmp(IntCC::SignedLessThan, current, end_val.value)
                };
                builder.ins().brif(cmp, body_block, &[], exit_block, &[]);

                // Body
                builder.switch_to_block(body_block);
                cf_ctx.push_loop(exit_block, continue_block);
                let body_terminated =
                    compile_block(builder, &for_stmt.body, variables, cf_ctx, ctx)?;
                cf_ctx.pop_loop();

                if !body_terminated {
                    builder.ins().jump(continue_block, &[]);
                }

                // Continue: increment and jump to header
                builder.switch_to_block(continue_block);
                let current = builder.use_var(var);
                let next = builder.ins().iadd_imm(current, 1);
                builder.def_var(var, next);
                builder.ins().jump(header, &[]);

                // Exit
                builder.switch_to_block(exit_block);

                // Seal blocks
                builder.seal_block(header);
                builder.seal_block(body_block);
                builder.seal_block(continue_block);
                builder.seal_block(exit_block);

                Ok(false)
            } else {
                // Array iteration
                let arr = compile_expr(builder, &for_stmt.iterable, variables, ctx)?;

                // Get array length
                let len_id = ctx
                    .func_ids
                    .get("vole_array_len")
                    .ok_or_else(|| "vole_array_len not found".to_string())?;
                let len_ref = ctx.module.declare_func_in_func(*len_id, builder.func);
                let len_call = builder.ins().call(len_ref, &[arr.value]);
                let len_val = builder.inst_results(len_call)[0];

                // Create index variable (i = 0)
                let idx_var = builder.declare_var(types::I64);
                let zero = builder.ins().iconst(types::I64, 0);
                builder.def_var(idx_var, zero);

                // Determine element type from array type
                let elem_type = match &arr.vole_type {
                    Type::Array(elem) => elem.as_ref().clone(),
                    _ => Type::I64,
                };

                // Create element variable
                let elem_var = builder.declare_var(types::I64);
                builder.def_var(elem_var, zero); // Initial value doesn't matter
                variables.insert(for_stmt.var_name, (elem_var, elem_type));

                // Loop blocks
                let header = builder.create_block();
                let body_block = builder.create_block();
                let continue_block = builder.create_block();
                let exit_block = builder.create_block();

                builder.ins().jump(header, &[]);

                // Header: check i < len
                builder.switch_to_block(header);
                let current_idx = builder.use_var(idx_var);
                let cmp = builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, current_idx, len_val);
                builder.ins().brif(cmp, body_block, &[], exit_block, &[]);

                // Body: load element, execute body
                builder.switch_to_block(body_block);

                // Get element: arr[i]
                let get_value_id = ctx
                    .func_ids
                    .get("vole_array_get_value")
                    .ok_or_else(|| "vole_array_get_value not found".to_string())?;
                let get_value_ref = ctx.module.declare_func_in_func(*get_value_id, builder.func);
                let current_idx = builder.use_var(idx_var);
                let get_call = builder.ins().call(get_value_ref, &[arr.value, current_idx]);
                let elem_val = builder.inst_results(get_call)[0];
                builder.def_var(elem_var, elem_val);

                // Execute loop body
                cf_ctx.push_loop(exit_block, continue_block);
                let body_terminated =
                    compile_block(builder, &for_stmt.body, variables, cf_ctx, ctx)?;
                cf_ctx.pop_loop();

                // Jump to continue block if not already terminated
                if !body_terminated {
                    builder.ins().jump(continue_block, &[]);
                }

                // Continue: increment and loop
                builder.switch_to_block(continue_block);
                let current_idx = builder.use_var(idx_var);
                let next_idx = builder.ins().iadd_imm(current_idx, 1);
                builder.def_var(idx_var, next_idx);
                builder.ins().jump(header, &[]);

                // Exit
                builder.switch_to_block(exit_block);

                // Seal blocks
                builder.seal_block(header);
                builder.seal_block(body_block);
                builder.seal_block(continue_block);
                builder.seal_block(exit_block);

                Ok(false)
            }
        }
        Stmt::Break(_) => {
            if let Some(exit_block) = cf_ctx.current_loop_exit() {
                builder.ins().jump(exit_block, &[]);
            }
            Ok(true)
        }
        Stmt::Continue(_) => {
            if let Some(continue_block) = cf_ctx.current_loop_continue() {
                builder.ins().jump(continue_block, &[]);
                // Create an unreachable block to continue building
                // (the code after continue is dead but Cranelift still needs a current block)
                let unreachable = builder.create_block();
                builder.switch_to_block(unreachable);
                builder.seal_block(unreachable);
            }
            Ok(true)
        }
    }
}

fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::IntLiteral(n) => {
            let val = builder.ins().iconst(types::I64, *n);
            Ok(CompiledValue {
                value: val,
                ty: types::I64,
                vole_type: Type::I64,
            })
        }
        ExprKind::FloatLiteral(n) => {
            let val = builder.ins().f64const(*n);
            Ok(CompiledValue {
                value: val,
                ty: types::F64,
                vole_type: Type::F64,
            })
        }
        ExprKind::BoolLiteral(b) => {
            let val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
            Ok(CompiledValue {
                value: val,
                ty: types::I8,
                vole_type: Type::Bool,
            })
        }
        ExprKind::Identifier(sym) => {
            if let Some((var, vole_type)) = variables.get(sym) {
                let val = builder.use_var(*var);
                // Get the type from the variable declaration
                let ty = builder.func.dfg.value_type(val);
                Ok(CompiledValue {
                    value: val,
                    ty,
                    vole_type: vole_type.clone(),
                })
            } else {
                // Check if this is a global variable
                if let Some(global) = ctx.globals.iter().find(|g| g.name == *sym) {
                    // Compile the global's initializer expression inline
                    // This works for constant expressions; for complex expressions,
                    // a more sophisticated approach would be needed
                    compile_expr(builder, &global.init, variables, ctx)
                } else {
                    Err(format!(
                        "undefined variable: {}",
                        ctx.interner.resolve(*sym)
                    ))
                }
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
                        vole_type: Type::Bool,
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
                        vole_type: Type::Bool,
                    });
                }
                _ => {} // Fall through to regular binary handling
            }

            let left = compile_expr(builder, &bin.left, variables, ctx)?;
            let right = compile_expr(builder, &bin.right, variables, ctx)?;

            // Determine result type (promote to wider type)
            let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
                types::F64
            } else if left.ty == types::F32 || right.ty == types::F32 {
                types::F32
            } else {
                left.ty
            };

            // Save the left operand's vole_type before conversion (for signed/unsigned op selection)
            let left_vole_type = left.vole_type.clone();

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
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fdiv(left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder.ins().udiv(left_val, right_val)
                    } else {
                        builder.ins().sdiv(left_val, right_val)
                    }
                }
                BinaryOp::Mod => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        // Floating-point modulo: a - (a/b).floor() * b
                        let div = builder.ins().fdiv(left_val, right_val);
                        let floor = builder.ins().floor(div);
                        let mul = builder.ins().fmul(floor, right_val);
                        builder.ins().fsub(left_val, mul)
                    } else if left_vole_type.is_unsigned() {
                        builder.ins().urem(left_val, right_val)
                    } else {
                        builder.ins().srem(left_val, right_val)
                    }
                }
                BinaryOp::Eq => {
                    if matches!(left_vole_type, Type::String) {
                        // String comparison
                        if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                            let cmp_ref = ctx.module.declare_func_in_func(*cmp_id, builder.func);
                            let call = builder.ins().call(cmp_ref, &[left_val, right_val]);
                            builder.inst_results(call)[0]
                        } else {
                            builder.ins().icmp(IntCC::Equal, left_val, right_val)
                        }
                    } else if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::Equal, left_val, right_val)
                    }
                }
                BinaryOp::Ne => {
                    if matches!(left_vole_type, Type::String) {
                        // String comparison (negate the result of eq)
                        if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                            let cmp_ref = ctx.module.declare_func_in_func(*cmp_id, builder.func);
                            let call = builder.ins().call(cmp_ref, &[left_val, right_val]);
                            let eq_result = builder.inst_results(call)[0];
                            // Negate: 1 - eq_result (since bool is 0 or 1)
                            let one = builder.ins().iconst(types::I8, 1);
                            builder.ins().isub(one, eq_result)
                        } else {
                            builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
                        }
                    } else if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
                    }
                }
                BinaryOp::Lt => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fcmp(FloatCC::LessThan, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThan, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedLessThan, left_val, right_val)
                    }
                }
                BinaryOp::Gt => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder
                            .ins()
                            .fcmp(FloatCC::GreaterThan, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThan, left_val, right_val)
                    }
                }
                BinaryOp::Le => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder
                            .ins()
                            .fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThanOrEqual, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
                    }
                }
                BinaryOp::Ge => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder
                            .ins()
                            .fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedGreaterThanOrEqual, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
                    }
                }
                // And/Or are handled above with short-circuit evaluation
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                // Bitwise operators
                BinaryOp::BitAnd => builder.ins().band(left_val, right_val),
                BinaryOp::BitOr => builder.ins().bor(left_val, right_val),
                BinaryOp::BitXor => builder.ins().bxor(left_val, right_val),
                BinaryOp::Shl => builder.ins().ishl(left_val, right_val),
                BinaryOp::Shr => {
                    if left_vole_type.is_unsigned() {
                        builder.ins().ushr(left_val, right_val)
                    } else {
                        builder.ins().sshr(left_val, right_val)
                    }
                }
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

            // Determine vole_type for result
            let vole_type = match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => Type::Bool,
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                _ => left_vole_type,
            };

            Ok(CompiledValue {
                value: result,
                ty: final_ty,
                vole_type,
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
                UnaryOp::BitNot => builder.ins().bnot(operand.value),
            };
            Ok(CompiledValue {
                value: result,
                ty: operand.ty,
                vole_type: operand.vole_type.clone(),
            })
        }
        ExprKind::Assign(assign) => {
            let value = compile_expr(builder, &assign.value, variables, ctx)?;
            if let Some((var, var_type)) = variables.get(&assign.target) {
                // If variable is a union and value is not, wrap the value
                let final_value = if matches!(var_type, Type::Union(_))
                    && !matches!(&value.vole_type, Type::Union(_))
                {
                    let wrapped =
                        construct_union(builder, value.clone(), var_type, ctx.pointer_type)?;
                    wrapped.value
                } else {
                    value.value
                };
                builder.def_var(*var, final_value);
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
        ExprKind::Range(_) => {
            // Range expressions are only supported in for-in context
            Err("Range expressions only supported in for-in context".to_string())
        }
        ExprKind::ArrayLiteral(elements) => {
            // Call vole_array_new()
            let array_new_id = ctx
                .func_ids
                .get("vole_array_new")
                .ok_or_else(|| "vole_array_new not found".to_string())?;
            let array_new_ref = ctx.module.declare_func_in_func(*array_new_id, builder.func);

            let call = builder.ins().call(array_new_ref, &[]);
            let arr_ptr = builder.inst_results(call)[0];

            // Push each element
            let array_push_id = ctx
                .func_ids
                .get("vole_array_push")
                .ok_or_else(|| "vole_array_push not found".to_string())?;
            let array_push_ref = ctx
                .module
                .declare_func_in_func(*array_push_id, builder.func);

            // Track element type from first element
            let mut elem_type = Type::Unknown;

            for (i, elem) in elements.iter().enumerate() {
                let compiled = compile_expr(builder, elem, variables, ctx)?;

                // Track element type from first element
                if i == 0 {
                    elem_type = compiled.vole_type.clone();
                }

                // Determine tag based on type
                let tag = match &compiled.vole_type {
                    Type::I64 | Type::I32 => 2i64, // TYPE_I64
                    Type::F64 => 3i64,             // TYPE_F64
                    Type::Bool => 4i64,            // TYPE_BOOL
                    Type::String => 1i64,          // TYPE_STRING
                    Type::Array(_) => 5i64,        // TYPE_ARRAY
                    _ => 2i64,                     // default to I64
                };

                let tag_val = builder.ins().iconst(types::I64, tag);

                // Convert value to u64 bits
                let value_bits = if compiled.ty == types::F64 {
                    builder
                        .ins()
                        .bitcast(types::I64, MemFlags::new(), compiled.value)
                } else if compiled.ty == types::I8 {
                    // Bool: zero-extend to i64
                    builder.ins().uextend(types::I64, compiled.value)
                } else {
                    compiled.value
                };

                builder
                    .ins()
                    .call(array_push_ref, &[arr_ptr, tag_val, value_bits]);
            }

            Ok(CompiledValue {
                value: arr_ptr,
                ty: ctx.pointer_type,
                vole_type: Type::Array(Box::new(elem_type)),
            })
        }
        ExprKind::Index(idx) => {
            let arr = compile_expr(builder, &idx.object, variables, ctx)?;
            let index = compile_expr(builder, &idx.index, variables, ctx)?;

            // Get element type from array type
            let elem_type = match &arr.vole_type {
                Type::Array(elem) => elem.as_ref().clone(),
                _ => Type::I64, // Default to I64 if type unknown
            };

            // Call vole_array_get_value(arr, index)
            let get_value_id = ctx
                .func_ids
                .get("vole_array_get_value")
                .ok_or_else(|| "vole_array_get_value not found".to_string())?;
            let get_value_ref = ctx.module.declare_func_in_func(*get_value_id, builder.func);

            let call = builder.ins().call(get_value_ref, &[arr.value, index.value]);
            let value = builder.inst_results(call)[0];

            // Convert value based on element type
            let (result_value, result_ty) = match &elem_type {
                Type::F64 => {
                    let fval = builder.ins().bitcast(types::F64, MemFlags::new(), value);
                    (fval, types::F64)
                }
                Type::Bool => {
                    let bval = builder.ins().ireduce(types::I8, value);
                    (bval, types::I8)
                }
                _ => (value, types::I64), // i64, strings, arrays stay as i64/pointer
            };

            Ok(CompiledValue {
                value: result_value,
                ty: result_ty,
                vole_type: elem_type,
            })
        }

        ExprKind::Match(match_expr) => {
            // Compile the scrutinee (value being matched)
            let scrutinee = compile_expr(builder, &match_expr.scrutinee, variables, ctx)?;

            // Create merge block that collects results
            // Use I64 as the result type since it can hold both integers and pointers
            let merge_block = builder.create_block();
            builder.append_block_param(merge_block, types::I64);

            // Create blocks for each arm
            let arm_blocks: Vec<Block> = match_expr
                .arms
                .iter()
                .map(|_| builder.create_block())
                .collect();

            // Jump to first arm
            if !arm_blocks.is_empty() {
                builder.ins().jump(arm_blocks[0], &[]);
            } else {
                // No arms - should not happen after sema, but handle gracefully
                let default_val = builder.ins().iconst(types::I64, 0);
                let default_arg = BlockArg::from(default_val);
                builder.ins().jump(merge_block, &[default_arg]);
            }

            // Track the result type from the first arm body
            let mut result_vole_type = Type::Void;

            // Compile each arm
            for (i, arm) in match_expr.arms.iter().enumerate() {
                let arm_block = arm_blocks[i];
                let next_block = arm_blocks.get(i + 1).copied().unwrap_or(merge_block);

                builder.switch_to_block(arm_block);

                // Create a new variables scope for this arm
                let mut arm_variables = variables.clone();

                // Check pattern
                let pattern_matches = match &arm.pattern {
                    Pattern::Wildcard(_) => {
                        // Always matches
                        None
                    }
                    Pattern::Identifier { name, .. } => {
                        // Bind the scrutinee value to the identifier
                        let var = builder.declare_var(scrutinee.ty);
                        builder.def_var(var, scrutinee.value);
                        arm_variables.insert(*name, (var, scrutinee.vole_type.clone()));
                        None // Always matches
                    }
                    Pattern::Literal(lit_expr) => {
                        // Compile literal and compare
                        let lit_val = compile_expr(builder, lit_expr, &mut arm_variables, ctx)?;
                        let cmp = match scrutinee.ty {
                            types::I64 | types::I32 | types::I8 => {
                                builder
                                    .ins()
                                    .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                            }
                            types::F64 => {
                                builder
                                    .ins()
                                    .fcmp(FloatCC::Equal, scrutinee.value, lit_val.value)
                            }
                            _ => {
                                // For strings, need to call comparison function
                                if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                                    let cmp_ref =
                                        ctx.module.declare_func_in_func(*cmp_id, builder.func);
                                    let call = builder
                                        .ins()
                                        .call(cmp_ref, &[scrutinee.value, lit_val.value]);
                                    builder.inst_results(call)[0]
                                } else {
                                    builder
                                        .ins()
                                        .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                                }
                            }
                        };
                        Some(cmp)
                    }
                };

                // Check guard if present
                let guard_result = if let Some(guard) = &arm.guard {
                    let guard_val = compile_expr(builder, guard, &mut arm_variables, ctx)?;
                    // Guard must be bool (i8)
                    Some(guard_val.value)
                } else {
                    None
                };

                // Combine pattern match and guard
                let should_execute = match (pattern_matches, guard_result) {
                    (None, None) => None, // Always execute (wildcard/identifier, no guard)
                    (Some(p), None) => Some(p),
                    (None, Some(g)) => Some(g),
                    (Some(p), Some(g)) => {
                        // Both must be true: p AND g
                        // icmp returns i8 (bool), guard is also i8
                        Some(builder.ins().band(p, g))
                    }
                };

                // Create body block and skip block
                let body_block = builder.create_block();

                if let Some(cond) = should_execute {
                    // Conditional: branch to body if true, next arm if false
                    let cond_i32 = builder.ins().uextend(types::I32, cond);
                    builder
                        .ins()
                        .brif(cond_i32, body_block, &[], next_block, &[]);
                } else {
                    // Unconditional: always go to body
                    builder.ins().jump(body_block, &[]);
                }

                builder.seal_block(arm_block);

                // Compile body
                builder.switch_to_block(body_block);
                let body_val = compile_expr(builder, &arm.body, &mut arm_variables, ctx)?;

                // Track result type from first arm
                if i == 0 {
                    result_vole_type = body_val.vole_type.clone();
                }

                // Convert body value to I64 if needed (merge block uses I64)
                let result_val = if body_val.ty != types::I64 {
                    match body_val.ty {
                        types::I8 => builder.ins().sextend(types::I64, body_val.value),
                        types::I32 => builder.ins().sextend(types::I64, body_val.value),
                        _ => body_val.value, // Pointers are already I64
                    }
                } else {
                    body_val.value
                };

                let result_arg = BlockArg::from(result_val);
                builder.ins().jump(merge_block, &[result_arg]);
                builder.seal_block(body_block);
            }

            // Note: arm_blocks are sealed inside the loop after their predecessors are known

            // Switch to merge block and get result
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let result = builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: result_vole_type,
            })
        }

        ExprKind::Nil => {
            // Nil has no runtime value - return a zero constant
            // The actual type will be determined by context (union wrapping)
            let zero = builder.ins().iconst(types::I8, 0);
            Ok(CompiledValue {
                value: zero,
                ty: types::I8,
                vole_type: Type::Nil,
            })
        }

        ExprKind::Is(is_expr) => {
            let value = compile_expr(builder, &is_expr.value, variables, ctx)?;
            let tested_type = resolve_type_expr(&is_expr.type_expr);

            // If value is a union, check the tag
            if let Type::Union(variants) = &value.vole_type {
                let expected_tag = variants
                    .iter()
                    .position(|v| v == &tested_type)
                    .unwrap_or(usize::MAX);

                // Load tag from union (at offset 0)
                let tag = builder
                    .ins()
                    .load(types::I8, MemFlags::new(), value.value, 0);
                let expected = builder.ins().iconst(types::I8, expected_tag as i64);
                let result = builder.ins().icmp(IntCC::Equal, tag, expected);

                Ok(CompiledValue {
                    value: result,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            } else {
                // Not a union, always true if types match, false otherwise
                let result = if value.vole_type == tested_type {
                    1i64
                } else {
                    0i64
                };
                let result_val = builder.ins().iconst(types::I8, result);
                Ok(CompiledValue {
                    value: result_val,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            }
        }

        ExprKind::NullCoalesce(nc) => {
            let value = compile_expr(builder, &nc.value, variables, ctx)?;

            // Get nil tag for this union
            let Type::Union(variants) = &value.vole_type else {
                return Err("Expected union for ??".to_string());
            };
            let nil_tag = variants
                .iter()
                .position(|v| v == &Type::Nil)
                .unwrap_or(usize::MAX);

            // Load tag
            let tag = builder
                .ins()
                .load(types::I8, MemFlags::new(), value.value, 0);
            let nil_tag_val = builder.ins().iconst(types::I8, nil_tag as i64);
            let is_nil = builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

            // Create blocks
            let nil_block = builder.create_block();
            let not_nil_block = builder.create_block();
            let merge_block = builder.create_block();

            // Determine result type (unwrapped)
            let result_vole_type = value.vole_type.unwrap_optional().unwrap_or(Type::Error);
            let cranelift_type = type_to_cranelift(&result_vole_type, ctx.pointer_type);
            builder.append_block_param(merge_block, cranelift_type);

            builder
                .ins()
                .brif(is_nil, nil_block, &[], not_nil_block, &[]);

            // Nil block: evaluate default
            builder.switch_to_block(nil_block);
            builder.seal_block(nil_block);
            let default_val = compile_expr(builder, &nc.default, variables, ctx)?;
            // Coerce default value to the expected result type if needed
            let default_coerced = if default_val.ty != cranelift_type {
                if default_val.ty.is_int() && cranelift_type.is_int() {
                    if cranelift_type.bytes() < default_val.ty.bytes() {
                        builder.ins().ireduce(cranelift_type, default_val.value)
                    } else {
                        builder.ins().sextend(cranelift_type, default_val.value)
                    }
                } else {
                    default_val.value
                }
            } else {
                default_val.value
            };
            let default_arg = BlockArg::from(default_coerced);
            builder.ins().jump(merge_block, &[default_arg]);

            // Not nil block: extract payload
            builder.switch_to_block(not_nil_block);
            builder.seal_block(not_nil_block);
            let payload = builder
                .ins()
                .load(cranelift_type, MemFlags::new(), value.value, 8);
            let payload_arg = BlockArg::from(payload);
            builder.ins().jump(merge_block, &[payload_arg]);

            // Merge
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let result = builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: cranelift_type,
                vole_type: result_vole_type,
            })
        }

        ExprKind::Lambda(lambda) => compile_lambda(builder, lambda, variables, ctx),
    }
}

/// Compile a lambda expression to a function pointer
fn compile_lambda(
    builder: &mut FunctionBuilder,
    lambda: &LambdaExpr,
    _variables: &HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Generate unique name for the lambda
    let lambda_name = format!("__lambda_{}", *ctx.lambda_counter);
    *ctx.lambda_counter += 1;

    // Build parameter types from lambda params
    let param_types: Vec<types::Type> = lambda
        .params
        .iter()
        .map(|p| {
            p.ty.as_ref()
                .map(|t| type_to_cranelift(&resolve_type_expr(t), ctx.pointer_type))
                .unwrap_or(types::I64)
        })
        .collect();

    let param_vole_types: Vec<Type> = lambda
        .params
        .iter()
        .map(|p| p.ty.as_ref().map(resolve_type_expr).unwrap_or(Type::I64))
        .collect();

    // Determine return type
    let return_type = lambda
        .return_type
        .as_ref()
        .map(|t| type_to_cranelift(&resolve_type_expr(t), ctx.pointer_type))
        .unwrap_or(types::I64);

    let return_vole_type = lambda
        .return_type
        .as_ref()
        .map(resolve_type_expr)
        .unwrap_or(Type::I64);

    // Create signature for the lambda
    let mut sig = ctx.module.make_signature();
    for &param_ty in &param_types {
        sig.params.push(AbiParam::new(param_ty));
    }
    sig.returns.push(AbiParam::new(return_type));

    // Declare the lambda function
    let func_id = ctx
        .module
        .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
        .map_err(|e| e.to_string())?;

    // Store the func_id so it can be looked up later
    ctx.func_ids.insert(lambda_name.clone(), func_id);

    // Create a new codegen context for the lambda
    let mut lambda_ctx = ctx.module.make_context();
    lambda_ctx.func.signature = sig.clone();

    // Build the lambda function body
    {
        let mut lambda_builder_ctx = FunctionBuilderContext::new();
        let mut lambda_builder =
            FunctionBuilder::new(&mut lambda_ctx.func, &mut lambda_builder_ctx);

        let entry_block = lambda_builder.create_block();
        lambda_builder.append_block_params_for_function_params(entry_block);
        lambda_builder.switch_to_block(entry_block);

        // Map parameters to variables
        let mut lambda_variables: HashMap<Symbol, (Variable, Type)> = HashMap::new();
        let block_params = lambda_builder.block_params(entry_block).to_vec();
        for (i, param) in lambda.params.iter().enumerate() {
            let var = lambda_builder.declare_var(param_types[i]);
            lambda_builder.def_var(var, block_params[i]);
            lambda_variables.insert(param.name, (var, param_vole_types[i].clone()));
        }

        // Create a CompileCtx for the lambda body (but without module access for nested lambdas)
        // For pure lambdas (no captures), we can use a simpler approach
        let mut lambda_cf_ctx = ControlFlowCtx::new();

        // Compile the body
        let result = match &lambda.body {
            LambdaBody::Expr(expr) => {
                // For expression body, we need to compile within the lambda's context
                // This is tricky because we can't recursively call compile_expr with a different builder
                // For now, compile simple expression bodies directly
                compile_lambda_body_expr(&mut lambda_builder, expr, &mut lambda_variables, ctx)?
            }
            LambdaBody::Block(block) => {
                // For block body, compile the block and handle returns
                let terminated = compile_block(
                    &mut lambda_builder,
                    block,
                    &mut lambda_variables,
                    &mut lambda_cf_ctx,
                    ctx,
                )?;
                if terminated {
                    // Block ended with return, no need to add another
                    lambda_builder.seal_all_blocks();
                    lambda_builder.finalize();

                    // Define the lambda function
                    ctx.module
                        .define_function(func_id, &mut lambda_ctx)
                        .map_err(|e| format!("Failed to define lambda: {:?}", e))?;

                    // Get function reference and its address
                    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    let func_addr = builder.ins().func_addr(ctx.pointer_type, func_ref);

                    return Ok(CompiledValue {
                        value: func_addr,
                        ty: ctx.pointer_type,
                        vole_type: Type::Function(FunctionType {
                            params: param_vole_types,
                            return_type: Box::new(return_vole_type),
                        }),
                    });
                }
                // Block didn't terminate, need to return a default value
                // This shouldn't happen for well-formed code
                let zero = lambda_builder.ins().iconst(types::I64, 0);
                CompiledValue {
                    value: zero,
                    ty: types::I64,
                    vole_type: Type::I64,
                }
            }
        };

        // Return the result
        lambda_builder.ins().return_(&[result.value]);
        lambda_builder.seal_all_blocks();
        lambda_builder.finalize();
    }

    // Define the lambda function
    ctx.module
        .define_function(func_id, &mut lambda_ctx)
        .map_err(|e| format!("Failed to define lambda: {:?}", e))?;

    // Get function reference and its address in the parent function
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let func_addr = builder.ins().func_addr(ctx.pointer_type, func_ref);

    Ok(CompiledValue {
        value: func_addr,
        ty: ctx.pointer_type,
        vole_type: Type::Function(FunctionType {
            params: param_vole_types,
            return_type: Box::new(return_vole_type),
        }),
    })
}

/// Compile a lambda body expression
/// This is a simplified version that handles basic expression types
fn compile_lambda_body_expr(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // For pure lambdas, we can use the regular compile_expr
    // since there are no captures to worry about
    compile_expr(builder, expr, variables, ctx)
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
        vole_type: Type::String,
    })
}

/// Compile a function call expression
fn compile_call(
    builder: &mut FunctionBuilder,
    call: &crate::frontend::CallExpr,
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
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
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("println expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Dispatch based on argument type
    // We use vole_type to distinguish strings from regular I64 values
    let (func_name, call_arg) = if matches!(arg.vole_type, Type::String) {
        ("vole_println_string", arg.value)
    } else if arg.ty == types::F64 {
        ("vole_println_f64", arg.value)
    } else if arg.ty == types::I8 {
        ("vole_println_bool", arg.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if arg.ty.is_int() && arg.ty != types::I64 {
            builder.ins().sextend(types::I64, arg.value)
        } else {
            arg.value
        };
        ("vole_println_i64", extended)
    };

    let func_id = ctx
        .func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[call_arg]);

    // println returns void, but we need to return something
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile print_char builtin for mandelbrot ASCII output
fn compile_print_char(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
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
        vole_type: Type::Void,
    })
}

/// Compile assert builtin - checks condition and calls vole_assert_fail if false
fn compile_assert(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
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
        vole_type: Type::Void,
    })
}

/// Compile a call to a user-defined function
fn compile_user_function_call(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
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
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        // TODO: Track vole_type for function return types properly
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type: Type::Unknown,
        })
    }
}

/// Compile an interpolated string by converting parts and concatenating
fn compile_interpolated_string(
    builder: &mut FunctionBuilder,
    parts: &[StringPart],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
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
            vole_type: Type::String,
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
        vole_type: Type::String,
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
    if matches!(val.vole_type, Type::String) {
        return Ok(val.value);
    }

    let (func_name, call_val) = if val.ty == types::F64 {
        ("vole_f64_to_string", val.value)
    } else if val.ty == types::I8 {
        ("vole_bool_to_string", val.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if val.ty.is_int() && val.ty != types::I64 {
            builder.ins().sextend(types::I64, val.value)
        } else {
            val.value
        };
        ("vole_i64_to_string", extended)
    };

    let func_id = func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = module.declare_func_in_func(*func_id, builder.func);

    let call = builder.ins().call(func_ref, &[call_val]);
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
