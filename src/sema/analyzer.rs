// src/sema/analyzer.rs

use crate::errors::SemanticError;
use crate::frontend::*;
use crate::sema::{
    FunctionType, Type,
    scope::{Scope, Variable},
};
use std::collections::HashMap;

/// A type error wrapping a miette-enabled SemanticError
#[derive(Debug, Clone)]
pub struct TypeError {
    pub error: SemanticError,
    pub span: Span,
}

impl TypeError {
    /// Create a new type error
    pub fn new(error: SemanticError, span: Span) -> Self {
        Self { error, span }
    }
}

pub struct Analyzer {
    scope: Scope,
    functions: HashMap<Symbol, FunctionType>,
    globals: HashMap<Symbol, Type>,
    current_function_return: Option<Type>,
    errors: Vec<TypeError>,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            errors: Vec::new(),
        }
    }

    /// Helper to add a type error
    fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    pub fn analyze(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // First pass: collect function signatures
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let params: Vec<Type> = func
                        .params
                        .iter()
                        .map(|p| self.resolve_type(&p.ty))
                        .collect();
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type(t))
                        .unwrap_or(Type::Void);

                    self.functions.insert(
                        func.name,
                        FunctionType {
                            params,
                            return_type: Box::new(return_type),
                        },
                    );
                }
                Decl::Tests(_) => {
                    // Tests don't need signatures in the first pass
                }
                Decl::Let(_) => {
                    // Let declarations are processed before the second pass
                }
            }
        }

        // Process global let declarations first (type check and add to scope)
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                let declared_type = let_stmt.ty.as_ref().map(|t| self.resolve_type(t));
                let init_type = self.check_expr_expecting(
                    &let_stmt.init,
                    declared_type.as_ref(),
                    interner,
                )?;

                let var_type = declared_type.unwrap_or(init_type.clone());

                self.globals.insert(let_stmt.name, var_type.clone());
                self.scope.define(
                    let_stmt.name,
                    Variable {
                        ty: var_type,
                        mutable: let_stmt.mutable,
                    },
                );
            }
        }

        // Second pass: type check function bodies and tests
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.check_function(func, interner)?;
                }
                Decl::Tests(tests_decl) => {
                    self.check_tests(tests_decl, interner)?;
                }
                Decl::Let(_) => {
                    // Already processed above
                }
            }
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    fn resolve_type(&self, ty: &TypeExpr) -> Type {
        match ty {
            TypeExpr::Primitive(p) => Type::from_primitive(*p),
            TypeExpr::Named(_) => Type::Error, // Not handling named types in Phase 1
        }
    }

    fn check_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        let func_type = self.functions.get(&func.name).cloned().unwrap();
        self.current_function_return = Some(*func_type.return_type.clone());

        // Create new scope with parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, ty) in func.params.iter().zip(func_type.params.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty.clone(),
                    mutable: false,
                },
            );
        }

        // Check body
        self.check_block(&func.body, interner)?;

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.current_function_return = None;

        Ok(())
    }

    fn check_tests(
        &mut self,
        tests_decl: &TestsDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for test_case in &tests_decl.tests {
            // Each test gets its own scope
            let parent_scope = std::mem::take(&mut self.scope);
            self.scope = Scope::with_parent(parent_scope);

            // Tests implicitly return void
            self.current_function_return = Some(Type::Void);

            // Type check all statements in the test body
            self.check_block(&test_case.body, interner)?;

            // Restore scope
            if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                self.scope = parent;
            }
            self.current_function_return = None;
        }

        Ok(())
    }

    fn is_assert_call(&self, callee: &Expr, interner: &Interner) -> bool {
        if let ExprKind::Identifier(sym) = &callee.kind {
            interner.resolve(*sym) == "assert"
        } else {
            false
        }
    }

    fn check_block(&mut self, block: &Block, interner: &Interner) -> Result<(), Vec<TypeError>> {
        for stmt in &block.stmts {
            self.check_stmt(stmt, interner)?;
        }
        Ok(())
    }

    fn check_stmt(&mut self, stmt: &Stmt, interner: &Interner) -> Result<(), Vec<TypeError>> {
        match stmt {
            Stmt::Let(let_stmt) => {
                let declared_type = let_stmt.ty.as_ref().map(|t| self.resolve_type(t));
                let init_type = self.check_expr_expecting(
                    &let_stmt.init,
                    declared_type.as_ref(),
                    interner,
                )?;

                let var_type = declared_type.unwrap_or(init_type);

                self.scope.define(
                    let_stmt.name,
                    Variable {
                        ty: var_type,
                        mutable: let_stmt.mutable,
                    },
                );
            }
            Stmt::Expr(expr_stmt) => {
                self.check_expr(&expr_stmt.expr, interner)?;
            }
            Stmt::While(while_stmt) => {
                let cond_type = self.check_expr(&while_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found: cond_type.name().to_string(),
                            span: while_stmt.condition.span.into(),
                        },
                        while_stmt.condition.span,
                    );
                }

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.check_block(&while_stmt.body, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::If(if_stmt) => {
                let cond_type = self.check_expr(&if_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found: cond_type.name().to_string(),
                            span: if_stmt.condition.span.into(),
                        },
                        if_stmt.condition.span,
                    );
                }

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.check_block(&if_stmt.then_branch, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }

                if let Some(else_branch) = &if_stmt.else_branch {
                    let parent = std::mem::take(&mut self.scope);
                    self.scope = Scope::with_parent(parent);
                    self.check_block(else_branch, interner)?;
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }
            }
            Stmt::Break(_) => {
                // Could check we're in a loop, but skipping for Phase 1
            }
            Stmt::Return(ret) => {
                let ret_type = if let Some(value) = &ret.value {
                    self.check_expr(value, interner)?
                } else {
                    Type::Void
                };

                if let Some(expected) = &self.current_function_return
                    && !self.types_compatible(&ret_type, expected)
                {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected.name().to_string(),
                            found: ret_type.name().to_string(),
                            span: ret.span.into(),
                        },
                        ret.span,
                    );
                }
            }
        }
        Ok(())
    }

    /// Check expression against an expected type (bidirectional type checking)
    /// If expected is None, falls back to inference mode.
    fn check_expr_expecting(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(value) => {
                match expected {
                    Some(ty) if Self::literal_fits(*value, ty) => Ok(ty.clone()),
                    Some(ty) => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: ty.name().to_string(),
                                found: "integer literal".to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(ty.clone())
                    }
                    None => Ok(Type::I64),
                }
            }
            ExprKind::FloatLiteral(_) => {
                match expected {
                    Some(ty) if ty == &Type::F64 => Ok(Type::F64),
                    Some(ty) if ty.is_numeric() => Ok(ty.clone()),
                    Some(ty) => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: ty.name().to_string(),
                                found: "f64".to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        Ok(Type::F64)
                    }
                    None => Ok(Type::F64),
                }
            }
            ExprKind::Binary(bin) => {
                match bin.op {
                    // Arithmetic ops: propagate expected type to both operands
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // If we have an expected type and both sides match, use it
                            if let Some(exp) = expected {
                                if self.types_compatible(&left_ty, exp) && self.types_compatible(&right_ty, exp) {
                                    return Ok(exp.clone());
                                }
                            }
                            // Otherwise return wider type
                            if left_ty == Type::F64 || right_ty == Type::F64 {
                                Ok(Type::F64)
                            } else if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    // Comparison ops: infer left, check right against left
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
                        let left_ty = self.check_expr_expecting(&bin.left, None, interner)?;
                        self.check_expr_expecting(&bin.right, Some(&left_ty), interner)?;
                        Ok(Type::Bool)
                    }
                    // Logical ops: both sides must be bool
                    BinaryOp::And | BinaryOp::Or => {
                        let left_ty = self.check_expr_expecting(&bin.left, Some(&Type::Bool), interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, Some(&Type::Bool), interner)?;
                        if left_ty == Type::Bool && right_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    // Bitwise ops: both sides must be integer
                    BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor | BinaryOp::Shl | BinaryOp::Shr => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_integer() && right_ty.is_integer() {
                            if let Some(exp) = expected {
                                if self.types_compatible(&left_ty, exp) && self.types_compatible(&right_ty, exp) {
                                    return Ok(exp.clone());
                                }
                            }
                            if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }
            ExprKind::Unary(un) => {
                match un.op {
                    UnaryOp::Neg => {
                        // Propagate expected type through negation
                        let operand_ty = self.check_expr_expecting(&un.operand, expected, interner)?;
                        if operand_ty.is_numeric() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => {
                        // Not always expects and returns bool
                        let operand_ty = self.check_expr_expecting(&un.operand, Some(&Type::Bool), interner)?;
                        if operand_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        // Bitwise not: propagate expected type, requires integer
                        let operand_ty = self.check_expr_expecting(&un.operand, expected, interner)?;
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }
            ExprKind::Grouping(inner) => self.check_expr_expecting(inner, expected, interner),
            // All other cases: infer type, then check compatibility
            _ => {
                let inferred = self.check_expr(expr, interner)?;
                if let Some(expected_ty) = expected {
                    if !self.types_compatible(&inferred, expected_ty) {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: expected_ty.name().to_string(),
                                found: inferred.name().to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                }
                Ok(inferred)
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr, interner: &Interner) -> Result<Type, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(_) => Ok(Type::I64), // Default to i64 for now
            ExprKind::FloatLiteral(_) => Ok(Type::F64),
            ExprKind::BoolLiteral(_) => Ok(Type::Bool),
            ExprKind::StringLiteral(_) => Ok(Type::String),
            ExprKind::InterpolatedString(_) => Ok(Type::String),

            ExprKind::Identifier(sym) => {
                if let Some(var) = self.scope.get(*sym) {
                    Ok(var.ty.clone())
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::Error)
                }
            }

            ExprKind::Binary(bin) => {
                let left_ty = self.check_expr(&bin.left, interner)?;
                let right_ty = self.check_expr(&bin.right, interner)?;

                match bin.op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // Return wider type
                            if left_ty == Type::F64 || right_ty == Type::F64 {
                                Ok(Type::F64)
                            } else if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Le
                    | BinaryOp::Ge => Ok(Type::Bool),
                    BinaryOp::And | BinaryOp::Or => {
                        if left_ty == Type::Bool && right_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor | BinaryOp::Shl | BinaryOp::Shr => {
                        if left_ty.is_integer() && right_ty.is_integer() {
                            if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }

            ExprKind::Unary(un) => {
                let operand_ty = self.check_expr(&un.operand, interner)?;
                match un.op {
                    UnaryOp::Neg => {
                        if operand_ty.is_numeric() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => {
                        if operand_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }

            ExprKind::Call(call) => {
                // Handle assert specially
                if self.is_assert_call(&call.callee, interner) {
                    if call.args.len() != 1 {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: 1,
                                found: call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::Void);
                    }

                    let arg_ty = self.check_expr(&call.args[0], interner)?;
                    if arg_ty != Type::Bool && arg_ty != Type::Error {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "bool".to_string(),
                                found: arg_ty.name().to_string(),
                                span: call.args[0].span.into(),
                            },
                            call.args[0].span,
                        );
                    }

                    return Ok(Type::Void);
                }

                if let ExprKind::Identifier(sym) = &call.callee.kind {
                    if let Some(func_type) = self.functions.get(sym) {
                        let func_type = func_type.clone();
                        if call.args.len() != func_type.params.len() {
                            self.add_error(
                                SemanticError::WrongArgumentCount {
                                    expected: func_type.params.len(),
                                    found: call.args.len(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                        }

                        for (arg, param_ty) in call.args.iter().zip(func_type.params.iter()) {
                            let arg_ty = self.check_expr(arg, interner)?;
                            if !self.types_compatible(&arg_ty, param_ty) {
                                self.add_error(
                                    SemanticError::TypeMismatch {
                                        expected: param_ty.name().to_string(),
                                        found: arg_ty.name().to_string(),
                                        span: arg.span.into(),
                                    },
                                    arg.span,
                                );
                            }
                        }

                        return Ok(*func_type.return_type);
                    } else {
                        // Builtin function - allow for now (e.g., println)
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Void);
                    }
                }

                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "function".to_string(),
                        found: "expression".to_string(),
                        span: call.callee.span.into(),
                    },
                    call.callee.span,
                );
                Ok(Type::Error)
            }

            ExprKind::Assign(assign) => {
                let value_ty = self.check_expr(&assign.value, interner)?;

                if let Some(var) = self.scope.get(assign.target) {
                    let is_mutable = var.mutable;
                    let var_ty = var.ty.clone();

                    if !is_mutable {
                        let name = interner.resolve(assign.target);
                        self.add_error(
                            SemanticError::ImmutableAssignment {
                                name: name.to_string(),
                                span: expr.span.into(),
                                declaration: expr.span.into(), // TODO: track declaration span
                            },
                            expr.span,
                        );
                    }
                    if !self.types_compatible(&value_ty, &var_ty) {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: var_ty.name().to_string(),
                                found: value_ty.name().to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                    Ok(var_ty)
                } else {
                    let name = interner.resolve(assign.target);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::Error)
                }
            }

            ExprKind::Grouping(inner) => self.check_expr(inner, interner),
        }
    }

    /// Check if an integer literal value fits in the target type
    fn literal_fits(value: i64, target: &Type) -> bool {
        match target {
            Type::I32 => value >= i32::MIN as i64 && value <= i32::MAX as i64,
            Type::I64 => true,
            Type::F64 => true,
            _ => false,
        }
    }

    fn types_compatible(&self, from: &Type, to: &Type) -> bool {
        if from == to {
            return true;
        }
        // Allow numeric coercion
        if from.is_integer() && to == &Type::I64 {
            return true;
        }
        if from.is_numeric() && to == &Type::F64 {
            return true;
        }
        // Error type is compatible with anything (for error recovery)
        if from == &Type::Error || to == &Type::Error {
            return true;
        }
        false
    }
}

// Note: Default is not implemented because Analyzer requires file and source parameters

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;

    fn check(source: &str) -> Result<(), Vec<TypeError>> {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();
        let mut analyzer = Analyzer::new("test.vole", source);
        analyzer.analyze(&program, &interner)
    }

    // Tests for miette error integration
    #[test]
    fn type_error_contains_semantic_error() {
        let source = "func main() { let x: bool = 42 }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::TypeMismatch { .. }
        ));
    }

    #[test]
    fn undefined_variable_has_correct_error_type() {
        let source = "func main() { let x = y }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::UndefinedVariable { .. }
        ));
    }

    #[test]
    fn immutable_assignment_has_correct_error_type() {
        let source = "func main() { let x = 1\n x = 2 }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::ImmutableAssignment { .. }
        ));
    }

    #[test]
    fn wrong_argument_count_has_correct_error_type() {
        let source = "func main() { assert(true, false) }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::WrongArgumentCount { .. }
        ));
    }

    #[test]
    fn condition_not_bool_has_correct_error_type() {
        // Use a string literal which is definitely not a bool or numeric
        let source = r#"func main() { if "hello" { } }"#;
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::ConditionNotBool { .. }
        ));
    }

    #[test]
    fn type_error_has_span() {
        let source = "func main() { let x = y }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(errors[0].span.line > 0);
    }

    #[test]
    fn analyze_simple_function() {
        let source = "func main() { let x = 42 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_type_mismatch() {
        let source = "func main() { let x: bool = 42 }";
        assert!(check(source).is_err());
    }

    #[test]
    fn analyze_undefined_variable() {
        let source = "func main() { let x = y }";
        assert!(check(source).is_err());
    }

    #[test]
    fn analyze_immutable_assignment() {
        let source = "func main() { let x = 1\n x = 2 }";
        assert!(check(source).is_err());
    }

    #[test]
    fn analyze_mutable_assignment() {
        let source = "func main() { let mut x = 1\n x = 2 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_assert_requires_bool() {
        // assert(42) should fail - argument must be bool
        let source = "func main() { assert(42) }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::TypeMismatch { ref expected, .. } if expected == "bool"
        ));
    }

    #[test]
    fn analyze_assert_valid() {
        // assert(1 == 1) should pass - comparison returns bool
        let source = "func main() { assert(1 == 1) }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_assert_with_bool_literal() {
        let source = "func main() { assert(true) }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_assert_wrong_arg_count() {
        let source = "func main() { assert(true, false) }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::WrongArgumentCount {
                expected: 1,
                found: 2,
                ..
            }
        ));
    }

    #[test]
    fn analyze_tests_block() {
        let source = r#"
            tests {
                test "simple assertion" {
                    assert(true)
                }
            }
        "#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_tests_block_with_invalid_assert() {
        let source = r#"
            tests {
                test "bad assertion" {
                    assert(42)
                }
            }
        "#;
        let result = check(source);
        assert!(result.is_err());
    }

    #[test]
    fn analyze_i32_literal_coercion() {
        let source = "func main() { let x: i32 = 42 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_i32_binary_coercion() {
        let source = "func main() { let x: i32 = 42 * 3 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_i32_to_i64_widening() {
        let source = "func main() { let x: i32 = 42\n let y: i64 = x }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_i64_to_i32_narrowing_error() {
        let source = "func main() { let x: i64 = 42\n let y: i32 = x }";
        let result = check(source);
        assert!(result.is_err());
    }
}
