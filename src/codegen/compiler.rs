// src/codegen/compiler.rs

use cranelift::prelude::*;
use std::collections::HashMap;

use crate::frontend::{
    self, Interner, Program, Decl, FuncDecl, TypeExpr,
    Stmt, Expr, ExprKind, BinaryOp, UnaryOp, Symbol,
};
use crate::sema::Type;
use crate::codegen::JitContext;

/// Compiled value with its type
#[derive(Clone, Copy)]
pub struct CompiledValue {
    pub value: Value,
    pub ty: types::Type,
}

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    interner: &'a Interner,
    pointer_type: types::Type,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, interner: &'a Interner) -> Self {
        let pointer_type = jit.pointer_type();
        Self {
            jit,
            interner,
            pointer_type,
        }
    }

    /// Compile a complete program
    pub fn compile_program(&mut self, program: &Program) -> Result<(), String> {
        // First pass: declare all functions
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let sig = self.create_function_signature(func);
                    let name = self.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                }
            }
        }

        // Second pass: compile function bodies
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.compile_function(func)?;
                }
            }
        }

        Ok(())
    }

    fn create_function_signature(&self, func: &FuncDecl) -> Signature {
        let mut params = Vec::new();
        for param in &func.params {
            params.push(type_to_cranelift(&resolve_type_expr(&param.ty), self.pointer_type));
        }

        let ret = func.return_type.as_ref().map(|t| {
            type_to_cranelift(&resolve_type_expr(t), self.pointer_type)
        });

        self.jit.create_signature(&params, ret)
    }

    fn compile_function(&mut self, func: &FuncDecl) -> Result<(), String> {
        let name = self.interner.resolve(func.name);
        let func_id = *self.jit.func_ids.get(name).unwrap();

        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig.clone();

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func.params.iter()
            .map(|p| type_to_cranelift(&resolve_type_expr(&p.ty), self.pointer_type))
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

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
            for ((name, ty), val) in param_names.iter().zip(param_types.iter()).zip(params.iter()) {
                let var = Variable::new(variables.len());
                builder.declare_var(var, *ty);
                builder.def_var(var, *val);
                variables.insert(*name, var);
            }

            // Compile function body
            let terminated = compile_block(&mut builder, &func.body, &mut variables, self.interner, self.pointer_type)?;

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

/// Returns true if a terminating statement (return) was compiled
fn compile_block(
    builder: &mut FunctionBuilder,
    block: &frontend::Block,
    variables: &mut HashMap<Symbol, Variable>,
    interner: &Interner,
    pointer_type: types::Type,
) -> Result<bool, String> {
    let mut terminated = false;
    for stmt in &block.stmts {
        if terminated {
            break; // Don't compile unreachable code
        }
        terminated = compile_stmt(builder, stmt, variables, interner, pointer_type)?;
    }
    Ok(terminated)
}

/// Returns true if this statement terminates (return)
fn compile_stmt(
    builder: &mut FunctionBuilder,
    stmt: &Stmt,
    variables: &mut HashMap<Symbol, Variable>,
    interner: &Interner,
    pointer_type: types::Type,
) -> Result<bool, String> {
    match stmt {
        Stmt::Let(let_stmt) => {
            let init = compile_expr(builder, &let_stmt.init, variables, interner, pointer_type)?;

            let var = Variable::new(variables.len());
            builder.declare_var(var, init.ty);
            builder.def_var(var, init.value);
            variables.insert(let_stmt.name, var);
            Ok(false)
        }
        Stmt::Expr(expr_stmt) => {
            compile_expr(builder, &expr_stmt.expr, variables, interner, pointer_type)?;
            Ok(false)
        }
        Stmt::Return(ret) => {
            if let Some(value) = &ret.value {
                let compiled = compile_expr(builder, value, variables, interner, pointer_type)?;
                builder.ins().return_(&[compiled.value]);
            } else {
                builder.ins().return_(&[]);
            }
            Ok(true)
        }
        Stmt::While(_) | Stmt::If(_) | Stmt::Break(_) => {
            // Will be implemented in Task 15
            Ok(false)
        }
    }
}

fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, Variable>,
    interner: &Interner,
    pointer_type: types::Type,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::IntLiteral(n) => {
            let val = builder.ins().iconst(types::I64, *n);
            Ok(CompiledValue { value: val, ty: types::I64 })
        }
        ExprKind::FloatLiteral(n) => {
            let val = builder.ins().f64const(*n);
            Ok(CompiledValue { value: val, ty: types::F64 })
        }
        ExprKind::BoolLiteral(b) => {
            let val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
            Ok(CompiledValue { value: val, ty: types::I8 })
        }
        ExprKind::Identifier(sym) => {
            if let Some(&var) = variables.get(sym) {
                let val = builder.use_var(var);
                // Get the type from the variable declaration
                let ty = builder.func.dfg.value_type(val);
                Ok(CompiledValue { value: val, ty })
            } else {
                Err(format!("undefined variable: {}", interner.resolve(*sym)))
            }
        }
        ExprKind::Binary(bin) => {
            let left = compile_expr(builder, &bin.left, variables, interner, pointer_type)?;
            let right = compile_expr(builder, &bin.right, variables, interner, pointer_type)?;

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
                        builder.ins().icmp(IntCC::SignedLessThan, left_val, right_val)
                    }
                }
                BinaryOp::Gt => {
                    if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::GreaterThan, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::SignedGreaterThan, left_val, right_val)
                    }
                }
                BinaryOp::Le => {
                    if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
                    }
                }
                BinaryOp::Ge => {
                    if result_ty == types::F64 {
                        builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
                    }
                }
            };

            // Comparison operators return I8 (bool)
            let final_ty = match bin.op {
                BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => types::I8,
                _ => result_ty,
            };

            Ok(CompiledValue { value: result, ty: final_ty })
        }
        ExprKind::Unary(un) => {
            let operand = compile_expr(builder, &un.operand, variables, interner, pointer_type)?;
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
            Ok(CompiledValue { value: result, ty: operand.ty })
        }
        ExprKind::Assign(assign) => {
            let value = compile_expr(builder, &assign.value, variables, interner, pointer_type)?;
            if let Some(&var) = variables.get(&assign.target) {
                builder.def_var(var, value.value);
                Ok(value)
            } else {
                Err(format!("undefined variable: {}", interner.resolve(assign.target)))
            }
        }
        ExprKind::Grouping(inner) => {
            compile_expr(builder, inner, variables, interner, pointer_type)
        }
        ExprKind::Call(_) | ExprKind::StringLiteral(_) | ExprKind::InterpolatedString(_) => {
            // Will be implemented in Task 16
            let zero = builder.ins().iconst(types::I64, 0);
            Ok(CompiledValue { value: zero, ty: types::I64 })
        }
    }
}

fn convert_to_type(builder: &mut FunctionBuilder, val: CompiledValue, target: types::Type) -> Value {
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
}
