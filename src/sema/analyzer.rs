// src/sema/analyzer.rs

use crate::errors::SemanticError;
use crate::frontend::*;
use crate::sema::{
    FunctionType, Type,
    scope::{Scope, Variable},
};
use std::collections::{HashMap, HashSet};

/// Information about a captured variable during lambda analysis
#[derive(Debug, Clone)]
struct CaptureInfo {
    name: Symbol,
    is_mutable: bool, // Was the captured variable declared with `let mut`
    is_mutated: bool, // Does the lambda assign to this variable
}

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
    /// Type overrides from flow-sensitive narrowing (e.g., after `if x is T`)
    type_overrides: HashMap<Symbol, Type>,
    /// Stack of lambda scopes for capture analysis. Each entry is a HashMap
    /// mapping captured variable names to their capture info.
    lambda_captures: Vec<HashMap<Symbol, CaptureInfo>>,
    /// Stack of sets tracking variables defined locally in each lambda
    /// (parameters and let bindings inside the lambda body)
    lambda_locals: Vec<HashSet<Symbol>>,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            errors: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
        }
    }

    /// Helper to add a type error
    fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    /// Check if we're currently inside a lambda
    fn in_lambda(&self) -> bool {
        !self.lambda_captures.is_empty()
    }

    /// Check if a symbol is a local variable in the current lambda
    fn is_lambda_local(&self, sym: Symbol) -> bool {
        if let Some(locals) = self.lambda_locals.last() {
            locals.contains(&sym)
        } else {
            false
        }
    }

    /// Add a local variable to the current lambda's locals set
    fn add_lambda_local(&mut self, sym: Symbol) {
        if let Some(locals) = self.lambda_locals.last_mut() {
            locals.insert(sym);
        }
    }

    /// Record a captured variable in the current lambda
    fn record_capture(&mut self, sym: Symbol, is_mutable: bool) {
        if let Some(captures) = self.lambda_captures.last_mut() {
            // Only add if not already captured
            captures.entry(sym).or_insert(CaptureInfo {
                name: sym,
                is_mutable,
                is_mutated: false,
            });
        }
    }

    /// Mark a captured variable as mutated
    fn mark_capture_mutated(&mut self, sym: Symbol) {
        if let Some(captures) = self.lambda_captures.last_mut()
            && let Some(info) = captures.get_mut(&sym)
        {
            info.is_mutated = true;
        }
    }

    /// Get variable type with flow-sensitive overrides
    fn get_variable_type(&self, sym: Symbol) -> Option<Type> {
        // Check overrides first (for narrowed types inside if-blocks)
        if let Some(ty) = self.type_overrides.get(&sym) {
            return Some(ty.clone());
        }
        // Then check scope
        self.scope.get(sym).map(|v| v.ty.clone())
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
                let init_type =
                    self.check_expr_expecting(&let_stmt.init, declared_type.as_ref(), interner)?;

                // Check if trying to use void return value
                if init_type == Type::Void {
                    self.add_error(
                        SemanticError::VoidReturnUsed {
                            span: let_stmt.init.span.into(),
                        },
                        let_stmt.init.span,
                    );
                }

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
            TypeExpr::Array(elem) => {
                let elem_ty = self.resolve_type(elem);
                Type::Array(Box::new(elem_ty))
            }
            TypeExpr::Nil => Type::Nil,
            TypeExpr::Optional(inner) => {
                let inner_ty = self.resolve_type(inner);
                Type::optional(inner_ty)
            }
            TypeExpr::Union(variants) => {
                let types: Vec<Type> = variants.iter().map(|t| self.resolve_type(t)).collect();
                Type::normalize_union(types)
            }
            TypeExpr::Function {
                params,
                return_type,
            } => {
                let param_types: Vec<Type> = params.iter().map(|p| self.resolve_type(p)).collect();
                let ret = self.resolve_type(return_type);
                Type::Function(FunctionType {
                    params: param_types,
                    return_type: Box::new(ret),
                })
            }
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
                let init_type =
                    self.check_expr_expecting(&let_stmt.init, declared_type.as_ref(), interner)?;

                // Check if trying to use void return value
                if init_type == Type::Void {
                    self.add_error(
                        SemanticError::VoidReturnUsed {
                            span: let_stmt.init.span.into(),
                        },
                        let_stmt.init.span,
                    );
                }

                let var_type = declared_type.unwrap_or(init_type);

                self.scope.define(
                    let_stmt.name,
                    Variable {
                        ty: var_type,
                        mutable: let_stmt.mutable,
                    },
                );

                // Track as a local if inside a lambda
                self.add_lambda_local(let_stmt.name);
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

                // Check if condition is `x is T` for flow-sensitive narrowing
                let narrowing_info = if let ExprKind::Is(is_expr) = &if_stmt.condition.kind {
                    if let ExprKind::Identifier(sym) = &is_expr.value.kind {
                        let tested_type = self.resolve_type(&is_expr.type_expr);
                        Some((*sym, tested_type))
                    } else {
                        None
                    }
                } else {
                    None
                };

                // Save current overrides
                let saved_overrides = self.type_overrides.clone();

                // Then branch (with narrowing if applicable)
                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                if let Some((sym, narrowed_type)) = &narrowing_info {
                    self.type_overrides.insert(*sym, narrowed_type.clone());
                }
                self.check_block(&if_stmt.then_branch, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }

                // Restore overrides for else branch (no narrowing there for now)
                self.type_overrides = saved_overrides.clone();

                if let Some(else_branch) = &if_stmt.else_branch {
                    let parent = std::mem::take(&mut self.scope);
                    self.scope = Scope::with_parent(parent);
                    self.check_block(else_branch, interner)?;
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }

                // Restore original overrides after the entire if statement
                self.type_overrides = saved_overrides;
            }
            Stmt::For(for_stmt) => {
                let iterable_ty = self.check_expr(&for_stmt.iterable, interner)?;

                let elem_ty = match iterable_ty {
                    Type::Range => Type::I64,
                    Type::Array(elem) => *elem,
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "iterable (range or array)".to_string(),
                                found: iterable_ty.name().to_string(),
                                span: for_stmt.iterable.span.into(),
                            },
                            for_stmt.iterable.span,
                        );
                        Type::Error
                    }
                };

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.scope.define(
                    for_stmt.var_name,
                    Variable {
                        ty: elem_ty,
                        mutable: false,
                    },
                );

                self.check_block(&for_stmt.body, interner)?;

                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::Break(_) => {
                // Could check we're in a loop, but skipping for Phase 1
            }
            Stmt::Continue(_) => {
                // Could validate we're in a loop, skip for now
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
            ExprKind::IntLiteral(value) => match expected {
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
            },
            ExprKind::FloatLiteral(_) => match expected {
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
            },
            ExprKind::Binary(bin) => {
                match bin.op {
                    // Arithmetic ops: propagate expected type to both operands
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // If we have an expected type and both sides match, use it
                            if let Some(exp) = expected
                                && self.types_compatible(&left_ty, exp)
                                && self.types_compatible(&right_ty, exp)
                            {
                                return Ok(exp.clone());
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
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Le
                    | BinaryOp::Ge => {
                        let left_ty = self.check_expr_expecting(&bin.left, None, interner)?;
                        self.check_expr_expecting(&bin.right, Some(&left_ty), interner)?;
                        Ok(Type::Bool)
                    }
                    // Logical ops: both sides must be bool
                    BinaryOp::And | BinaryOp::Or => {
                        let left_ty =
                            self.check_expr_expecting(&bin.left, Some(&Type::Bool), interner)?;
                        let right_ty =
                            self.check_expr_expecting(&bin.right, Some(&Type::Bool), interner)?;
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
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_integer() && right_ty.is_integer() {
                            if let Some(exp) = expected
                                && self.types_compatible(&left_ty, exp)
                                && self.types_compatible(&right_ty, exp)
                            {
                                return Ok(exp.clone());
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
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, expected, interner)?;
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
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, Some(&Type::Bool), interner)?;
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
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, expected, interner)?;
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
            ExprKind::ArrayLiteral(elements) => {
                let elem_expected = match expected {
                    Some(Type::Array(elem)) => Some(elem.as_ref()),
                    _ => None,
                };

                if elements.is_empty() {
                    if let Some(Type::Array(elem)) = expected {
                        return Ok(Type::Array(elem.clone()));
                    }
                    return Ok(Type::Array(Box::new(Type::Unknown)));
                }

                let elem_ty = self.check_expr_expecting(&elements[0], elem_expected, interner)?;

                for elem in elements.iter().skip(1) {
                    self.check_expr_expecting(elem, Some(&elem_ty), interner)?;
                }

                Ok(Type::Array(Box::new(elem_ty)))
            }
            ExprKind::Index(_) => {
                // Index expressions just delegate to check_expr
                self.check_expr(expr, interner)
            }
            ExprKind::Lambda(lambda) => {
                // Extract expected function type if available
                let expected_fn = expected.and_then(|t| {
                    if let Type::Function(ft) = t {
                        Some(ft)
                    } else {
                        None
                    }
                });
                Ok(self.analyze_lambda(lambda, expected_fn, interner))
            }
            // All other cases: infer type, then check compatibility
            _ => {
                let inferred = self.check_expr(expr, interner)?;
                if let Some(expected_ty) = expected
                    && !self.types_compatible(&inferred, expected_ty)
                {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_ty.name().to_string(),
                            found: inferred.name().to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
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
                // Use get_variable_type to respect flow-sensitive narrowing
                if let Some(ty) = self.get_variable_type(*sym) {
                    // Check if this is a capture (inside lambda, not a local)
                    if self.in_lambda() && !self.is_lambda_local(*sym) {
                        // Look up variable info to get mutability
                        if let Some(var) = self.scope.get(*sym) {
                            self.record_capture(*sym, var.mutable);
                        }
                    }
                    Ok(ty)
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
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
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
                    // First check if it's a top-level function
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
                            // For lambda arguments, pass expected type for inference
                            let arg_ty = if let ExprKind::Lambda(lambda) = &arg.kind {
                                let expected_fn = if let Type::Function(ft) = param_ty {
                                    Some(ft)
                                } else {
                                    None
                                };
                                self.analyze_lambda(lambda, expected_fn, interner)
                            } else {
                                self.check_expr(arg, interner)?
                            };

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
                    }

                    // Check if it's a variable with a function type
                    if let Some(Type::Function(func_type)) = self.get_variable_type(*sym) {
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
                            // For lambda arguments, pass expected type for inference
                            let arg_ty = if let ExprKind::Lambda(lambda) = &arg.kind {
                                let expected_fn = if let Type::Function(ft) = param_ty {
                                    Some(ft)
                                } else {
                                    None
                                };
                                self.analyze_lambda(lambda, expected_fn, interner)
                            } else {
                                self.check_expr(arg, interner)?
                            };

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
                    }

                    // Check if it's a known builtin function
                    let name = interner.resolve(*sym);
                    if name == "println" || name == "print_char" || name == "flush" {
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Void);
                    }

                    // Check if it's a variable with a non-function type
                    if let Some(var_ty) = self.get_variable_type(*sym) {
                        self.add_error(
                            SemanticError::NotCallable {
                                ty: var_ty.name().to_string(),
                                span: call.callee.span.into(),
                            },
                            call.callee.span,
                        );
                        // Still check args for more errors
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Error);
                    }

                    // Unknown identifier - might be an undefined function
                    // (will be caught by codegen or other checks)
                    for arg in &call.args {
                        self.check_expr(arg, interner)?;
                    }
                    return Ok(Type::Void);
                }

                // Non-identifier callee (e.g., a lambda expression being called directly)
                let callee_ty = self.check_expr(&call.callee, interner)?;
                if let Type::Function(func_type) = callee_ty {
                    // Calling a function-typed expression
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
                }

                // Non-callable type
                if callee_ty != Type::Error {
                    self.add_error(
                        SemanticError::NotCallable {
                            ty: callee_ty.name().to_string(),
                            span: call.callee.span.into(),
                        },
                        call.callee.span,
                    );
                }
                Ok(Type::Error)
            }

            ExprKind::Assign(assign) => {
                let value_ty = self.check_expr(&assign.value, interner)?;

                if let Some(var) = self.scope.get(assign.target) {
                    let is_mutable = var.mutable;
                    let var_ty = var.ty.clone();

                    // Check if this is a mutation of a captured variable
                    if self.in_lambda() && !self.is_lambda_local(assign.target) {
                        // Record as capture and mark as mutated
                        self.record_capture(assign.target, is_mutable);
                        self.mark_capture_mutated(assign.target);
                    }

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

            ExprKind::ArrayLiteral(elements) => {
                if elements.is_empty() {
                    // Empty array needs type annotation or we use Unknown
                    Ok(Type::Array(Box::new(Type::Unknown)))
                } else {
                    // Infer element type from first element
                    let elem_ty = self.check_expr(&elements[0], interner)?;

                    // Check remaining elements match
                    for elem in elements.iter().skip(1) {
                        let ty = self.check_expr(elem, interner)?;
                        if !self.types_compatible(&ty, &elem_ty) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: elem_ty.name().to_string(),
                                    found: ty.name().to_string(),
                                    span: elem.span.into(),
                                },
                                elem.span,
                            );
                        }
                    }

                    Ok(Type::Array(Box::new(elem_ty)))
                }
            }

            ExprKind::Index(idx) => {
                let obj_ty = self.check_expr(&idx.object, interner)?;
                let index_ty = self.check_expr(&idx.index, interner)?;

                // Index must be integer
                if !index_ty.is_integer() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: index_ty.name().to_string(),
                            span: idx.index.span.into(),
                        },
                        idx.index.span,
                    );
                }

                // Object must be array
                match obj_ty {
                    Type::Array(elem_ty) => Ok(*elem_ty),
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "array".to_string(),
                                found: obj_ty.name().to_string(),
                                span: idx.object.span.into(),
                            },
                            idx.object.span,
                        );
                        Ok(Type::Error)
                    }
                }
            }

            ExprKind::Range(range) => {
                let start_ty = self.check_expr(&range.start, interner)?;
                let end_ty = self.check_expr(&range.end, interner)?;

                if !start_ty.is_integer() || !end_ty.is_integer() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: format!("{} and {}", start_ty.name(), end_ty.name()),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(Type::Range)
            }

            ExprKind::Match(match_expr) => {
                // Check scrutinee type
                let scrutinee_type = self.check_expr(&match_expr.scrutinee, interner)?;

                // Check exhaustiveness - must have wildcard or identifier catch-all
                let has_catch_all = match_expr.arms.iter().any(|arm| {
                    matches!(
                        arm.pattern,
                        Pattern::Wildcard(_) | Pattern::Identifier { .. }
                    )
                });
                if !has_catch_all {
                    self.add_error(
                        SemanticError::NonExhaustiveMatch {
                            span: match_expr.span.into(),
                        },
                        match_expr.span,
                    );
                }

                // Check each arm, collect result types
                let mut result_type: Option<Type> = None;
                let mut first_arm_span: Option<Span> = None;

                for arm in &match_expr.arms {
                    // Enter new scope for arm (bindings live here)
                    self.scope = Scope::with_parent(std::mem::take(&mut self.scope));

                    // Check pattern
                    self.check_pattern(&arm.pattern, &scrutinee_type, interner);

                    // Check guard if present (must be bool)
                    if let Some(guard) = &arm.guard {
                        let guard_type = self.check_expr(guard, interner)?;
                        if guard_type != Type::Bool && !guard_type.is_numeric() {
                            self.add_error(
                                SemanticError::MatchGuardNotBool {
                                    found: guard_type.name().to_string(),
                                    span: guard.span.into(),
                                },
                                guard.span,
                            );
                        }
                    }

                    // Check body expression
                    let body_type = self.check_expr(&arm.body, interner)?;

                    // Unify with previous arms
                    match &result_type {
                        None => {
                            result_type = Some(body_type);
                            first_arm_span = Some(arm.span);
                        }
                        Some(expected) if *expected != body_type => {
                            self.add_error(
                                SemanticError::MatchArmTypeMismatch {
                                    expected: expected.name().to_string(),
                                    found: body_type.name().to_string(),
                                    first_arm: first_arm_span.unwrap().into(),
                                    span: arm.body.span.into(),
                                },
                                arm.body.span,
                            );
                        }
                        _ => {}
                    }

                    // Exit arm scope
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }

                Ok(result_type.unwrap_or(Type::Void))
            }

            ExprKind::Nil => Ok(Type::Nil),

            ExprKind::NullCoalesce(nc) => {
                let value_type = self.check_expr(&nc.value, interner)?;

                // Value must be an optional (union containing Nil)
                if !value_type.is_optional() {
                    self.add_error(
                        SemanticError::NullCoalesceNotOptional {
                            found: format!("{}", value_type),
                            span: nc.value.span.into(),
                        },
                        nc.value.span,
                    );
                    return Ok(Type::Error);
                }

                // Get the non-nil type
                let unwrapped = value_type.unwrap_optional().unwrap_or(Type::Error);

                // Default must match the unwrapped type
                let _default_type =
                    self.check_expr_expecting(&nc.default, Some(&unwrapped), interner)?;

                // Result is the non-nil type
                Ok(unwrapped)
            }

            ExprKind::Is(is_expr) => {
                let value_type = self.check_expr(&is_expr.value, interner)?;
                let tested_type = self.resolve_type(&is_expr.type_expr);

                // Warn/error if tested type is not a variant of value's union
                if let Type::Union(variants) = &value_type
                    && !variants.contains(&tested_type)
                {
                    self.add_error(
                        SemanticError::IsNotVariant {
                            tested: format!("{}", tested_type),
                            union_type: format!("{}", value_type),
                            span: is_expr.type_span.into(),
                        },
                        is_expr.type_span,
                    );
                }

                // Result is always bool
                Ok(Type::Bool)
            }

            ExprKind::Lambda(lambda) => {
                // For now, analyze without expected type context
                // (Context will be passed when we have assignment/call context)
                Ok(self.analyze_lambda(lambda, None, interner))
            }
        }
    }

    /// Check a pattern against the scrutinee type
    fn check_pattern(&mut self, pattern: &Pattern, scrutinee_type: &Type, interner: &Interner) {
        match pattern {
            Pattern::Wildcard(_) => {
                // Wildcard always matches, nothing to check
            }
            Pattern::Literal(expr) => {
                // Check literal type matches scrutinee type
                if let Ok(lit_type) = self.check_expr(expr, interner)
                    && !self.types_compatible(&lit_type, scrutinee_type)
                    && !self.types_compatible(scrutinee_type, &lit_type)
                {
                    self.add_error(
                        SemanticError::PatternTypeMismatch {
                            expected: scrutinee_type.name().to_string(),
                            found: lit_type.name().to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
            }
            Pattern::Identifier { name, span: _ } => {
                // Bind identifier to scrutinee's type in current scope
                self.scope.define(
                    *name,
                    Variable {
                        ty: scrutinee_type.clone(),
                        mutable: false,
                    },
                );
            }
        }
    }

    /// Analyze a lambda expression, optionally with an expected function type for inference
    fn analyze_lambda(
        &mut self,
        lambda: &LambdaExpr,
        expected_type: Option<&FunctionType>,
        interner: &Interner,
    ) -> Type {
        // Push capture analysis stacks
        self.lambda_captures.push(HashMap::new());
        self.lambda_locals.push(HashSet::new());

        // Resolve parameter types
        let mut param_types = Vec::new();

        for (i, param) in lambda.params.iter().enumerate() {
            let ty = if let Some(type_expr) = &param.ty {
                // Explicit type annotation
                self.resolve_type(type_expr)
            } else if let Some(expected) = expected_type {
                // Infer from expected type
                if i < expected.params.len() {
                    expected.params[i].clone()
                } else {
                    self.add_error(
                        SemanticError::CannotInferLambdaParam {
                            name: interner.resolve(param.name).to_string(),
                            span: param.span.into(),
                        },
                        param.span,
                    );
                    Type::Error
                }
            } else {
                // No type info available
                self.add_error(
                    SemanticError::CannotInferLambdaParam {
                        name: interner.resolve(param.name).to_string(),
                        span: param.span.into(),
                    },
                    param.span,
                );
                Type::Error
            };
            param_types.push(ty);
        }

        // Push new scope for lambda body
        let outer_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(outer_scope);

        // Define parameters in scope and track as locals
        for (param, ty) in lambda.params.iter().zip(param_types.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty.clone(),
                    mutable: false,
                },
            );
            // Parameters are locals, not captures
            self.add_lambda_local(param.name);
        }

        // Determine return type
        let declared_return = lambda.return_type.as_ref().map(|t| self.resolve_type(t));
        let expected_return = expected_type.map(|ft| (*ft.return_type).clone());

        // Analyze body and infer return type
        let body_type = match &lambda.body {
            LambdaBody::Expr(expr) => {
                // For expression body, analyze and use as return type
                match self.check_expr(expr, interner) {
                    Ok(ty) => ty,
                    Err(_) => Type::Error,
                }
            }
            LambdaBody::Block(block) => {
                // For blocks, set up return type context
                let old_return = self.current_function_return.take();
                self.current_function_return = declared_return.clone().or(expected_return.clone());

                let _ = self.check_block(block, interner);

                let ret = self.current_function_return.take().unwrap_or(Type::Void);
                self.current_function_return = old_return;
                ret
            }
        };

        // Restore outer scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }

        // Pop capture stacks and store captures in the lambda
        self.lambda_locals.pop();
        if let Some(captures) = self.lambda_captures.pop() {
            let capture_list: Vec<Capture> = captures
                .into_values()
                .map(|info| Capture {
                    name: info.name,
                    is_mutable: info.is_mutable,
                    is_mutated: info.is_mutated,
                })
                .collect();
            *lambda.captures.borrow_mut() = capture_list;
        }

        // Determine final return type
        let return_type = declared_return.or(expected_return).unwrap_or(body_type);

        Type::Function(FunctionType {
            params: param_types,
            return_type: Box::new(return_type),
        })
    }

    /// Check if an integer literal value fits in the target type
    fn literal_fits(value: i64, target: &Type) -> bool {
        match target {
            Type::I8 => value >= i8::MIN as i64 && value <= i8::MAX as i64,
            Type::I16 => value >= i16::MIN as i64 && value <= i16::MAX as i64,
            Type::I32 => value >= i32::MIN as i64 && value <= i32::MAX as i64,
            Type::I64 => true,
            Type::I128 => true, // i64 always fits in i128
            Type::U8 => value >= 0 && value <= u8::MAX as i64,
            Type::U16 => value >= 0 && value <= u16::MAX as i64,
            Type::U32 => value >= 0 && value <= u32::MAX as i64,
            Type::U64 => value >= 0,       // i64 positive values fit
            Type::F32 | Type::F64 => true, // Integers can become floats
            // For unions, check if literal fits any numeric variant
            Type::Union(variants) => variants.iter().any(|v| Self::literal_fits(value, v)),
            _ => false,
        }
    }

    fn types_compatible(&self, from: &Type, to: &Type) -> bool {
        if from == to {
            return true;
        }

        // Check if from can widen to to
        if from.can_widen_to(to) {
            return true;
        }

        // Allow numeric coercion (kept for backwards compatibility)
        if from.is_integer() && to == &Type::I64 {
            return true;
        }
        if from.is_numeric() && to == &Type::F64 {
            return true;
        }

        // Check if assigning to a union that contains the from type
        if let Type::Union(variants) = to {
            // Direct containment
            if variants.contains(from) {
                return true;
            }
            // Also check if from can widen into a union variant
            for variant in variants {
                if from.can_widen_to(variant) {
                    return true;
                }
            }
        }

        // Nil is compatible with any optional (union containing Nil)
        if *from == Type::Nil && to.is_optional() {
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

    // Helper to parse and analyze, returning the AST for capture inspection
    fn parse_and_analyze(source: &str) -> (Program, Interner) {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();
        let mut analyzer = Analyzer::new("test.vole", source);
        analyzer.analyze(&program, &interner).unwrap();
        (program, interner)
    }

    // Helper to extract lambda from first statement of main function
    fn get_first_lambda(program: &Program) -> &LambdaExpr {
        for decl in &program.declarations {
            if let Decl::Function(func) = decl {
                for stmt in &func.body.stmts {
                    if let Stmt::Let(let_stmt) = stmt {
                        if let ExprKind::Lambda(lambda) = &let_stmt.init.kind {
                            return lambda;
                        }
                    }
                }
            }
        }
        panic!("No lambda found in program");
    }

    #[test]
    fn lambda_no_captures_when_only_params() {
        let source = r#"
            func apply(f: (i64) -> i64, x: i64) -> i64 { return f(x) }
            func main() {
                let f = (x: i64) => x + 1
                apply(f, 10)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.captures.borrow().is_empty());
    }

    #[test]
    fn lambda_captures_outer_variable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let x = 10
                let f = () => x + 1
                apply(f)
            }
        "#;
        let (program, interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        let captures = lambda.captures.borrow();
        assert_eq!(captures.len(), 1);
        let name = interner.resolve(captures[0].name);
        assert_eq!(name, "x");
        assert!(!captures[0].is_mutable);
        assert!(!captures[0].is_mutated);
    }

    #[test]
    fn lambda_captures_mutable_variable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f = () => x + 1
                apply(f)
            }
        "#;
        let (program, interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        let captures = lambda.captures.borrow();
        assert_eq!(captures.len(), 1);
        let name = interner.resolve(captures[0].name);
        assert_eq!(name, "x");
        assert!(captures[0].is_mutable);
        assert!(!captures[0].is_mutated);
    }

    #[test]
    fn lambda_captures_and_mutates_variable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f: () -> i64 = () => {
                    x = x + 1
                    return x
                }
                apply(f)
            }
        "#;
        let (program, interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        let captures = lambda.captures.borrow();
        assert_eq!(captures.len(), 1);
        let name = interner.resolve(captures[0].name);
        assert_eq!(name, "x");
        assert!(captures[0].is_mutable);
        assert!(captures[0].is_mutated);
    }

    #[test]
    fn lambda_does_not_capture_its_own_params() {
        let source = r#"
            func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
            func main() {
                let f = (x: i64) => x * 2
                apply(f, 5)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.captures.borrow().is_empty());
    }

    #[test]
    fn lambda_does_not_capture_its_own_locals() {
        // Test with expression body that uses a local-like pattern
        // Note: this test verifies that locals defined in lambdas are not treated as captures
        let source = r#"
            func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
            func main() {
                let f = (y: i64) => y * 2
                apply(f, 5)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        // Parameters should not be treated as captures
        assert!(lambda.captures.borrow().is_empty());
    }

    #[test]
    fn lambda_block_body_with_local() {
        // Test block body with local let binding
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let f: () -> i64 = () => {
                    let y = 5
                    return y * 2
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        // Local y should not be captured
        assert!(lambda.captures.borrow().is_empty());
    }
}
