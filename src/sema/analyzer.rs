// src/sema/analyzer.rs

use crate::frontend::*;
use crate::sema::{scope::{Scope, Variable}, Type, FunctionType};
use std::collections::HashMap;

#[derive(Debug)]
pub struct TypeError {
    pub message: String,
    pub span: Span,
}

pub struct Analyzer {
    scope: Scope,
    functions: HashMap<Symbol, FunctionType>,
    current_function_return: Option<Type>,
    errors: Vec<TypeError>,
}

impl Analyzer {
    pub fn new() -> Self {
        Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            current_function_return: None,
            errors: Vec::new(),
        }
    }

    pub fn analyze(&mut self, program: &Program, interner: &Interner) -> Result<(), Vec<TypeError>> {
        // First pass: collect function signatures
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let params: Vec<Type> = func.params.iter()
                        .map(|p| self.resolve_type(&p.ty))
                        .collect();
                    let return_type = func.return_type
                        .as_ref()
                        .map(|t| self.resolve_type(t))
                        .unwrap_or(Type::Void);

                    self.functions.insert(func.name, FunctionType {
                        params,
                        return_type: Box::new(return_type),
                    });
                }
            }
        }

        // Second pass: type check function bodies
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.check_function(func, interner)?;
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

    fn check_function(&mut self, func: &FuncDecl, interner: &Interner) -> Result<(), Vec<TypeError>> {
        let func_type = self.functions.get(&func.name).cloned().unwrap();
        self.current_function_return = Some(*func_type.return_type.clone());

        // Create new scope with parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, ty) in func.params.iter().zip(func_type.params.iter()) {
            self.scope.define(param.name, Variable {
                ty: ty.clone(),
                mutable: false,
            });
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

    fn check_block(&mut self, block: &Block, interner: &Interner) -> Result<(), Vec<TypeError>> {
        for stmt in &block.stmts {
            self.check_stmt(stmt, interner)?;
        }
        Ok(())
    }

    fn check_stmt(&mut self, stmt: &Stmt, interner: &Interner) -> Result<(), Vec<TypeError>> {
        match stmt {
            Stmt::Let(let_stmt) => {
                let init_type = self.check_expr(&let_stmt.init, interner)?;

                let var_type = if let Some(ty) = &let_stmt.ty {
                    let declared = self.resolve_type(ty);
                    if !self.types_compatible(&init_type, &declared) {
                        self.errors.push(TypeError {
                            message: format!("type mismatch: expected {}, got {}", declared.name(), init_type.name()),
                            span: let_stmt.span,
                        });
                    }
                    declared
                } else {
                    init_type
                };

                self.scope.define(let_stmt.name, Variable {
                    ty: var_type,
                    mutable: let_stmt.mutable,
                });
            }
            Stmt::Expr(expr_stmt) => {
                self.check_expr(&expr_stmt.expr, interner)?;
            }
            Stmt::While(while_stmt) => {
                let cond_type = self.check_expr(&while_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.errors.push(TypeError {
                        message: format!("while condition must be bool, got {}", cond_type.name()),
                        span: while_stmt.condition.span,
                    });
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
                    self.errors.push(TypeError {
                        message: format!("if condition must be bool, got {}", cond_type.name()),
                        span: if_stmt.condition.span,
                    });
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

                if let Some(expected) = &self.current_function_return {
                    if !self.types_compatible(&ret_type, expected) {
                        self.errors.push(TypeError {
                            message: format!("return type mismatch: expected {}, got {}", expected.name(), ret_type.name()),
                            span: ret.span,
                        });
                    }
                }
            }
        }
        Ok(())
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
                    self.errors.push(TypeError {
                        message: "undefined variable".to_string(),
                        span: expr.span,
                    });
                    Ok(Type::Error)
                }
            }

            ExprKind::Binary(bin) => {
                let left_ty = self.check_expr(&bin.left, interner)?;
                let right_ty = self.check_expr(&bin.right, interner)?;

                match bin.op {
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
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
                            self.errors.push(TypeError {
                                message: format!("cannot perform {:?} on {} and {}", bin.op, left_ty.name(), right_ty.name()),
                                span: expr.span,
                            });
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
                        Ok(Type::Bool)
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
                            self.errors.push(TypeError {
                                message: format!("cannot negate {}", operand_ty.name()),
                                span: expr.span,
                            });
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => Ok(Type::Bool),
                }
            }

            ExprKind::Call(call) => {
                if let ExprKind::Identifier(sym) = &call.callee.kind {
                    if let Some(func_type) = self.functions.get(sym) {
                        let func_type = func_type.clone();
                        if call.args.len() != func_type.params.len() {
                            self.errors.push(TypeError {
                                message: format!("expected {} arguments, got {}", func_type.params.len(), call.args.len()),
                                span: expr.span,
                            });
                        }

                        for (arg, param_ty) in call.args.iter().zip(func_type.params.iter()) {
                            let arg_ty = self.check_expr(arg, interner)?;
                            if !self.types_compatible(&arg_ty, param_ty) {
                                self.errors.push(TypeError {
                                    message: format!("argument type mismatch: expected {}, got {}", param_ty.name(), arg_ty.name()),
                                    span: arg.span,
                                });
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

                self.errors.push(TypeError {
                    message: "expected function name".to_string(),
                    span: call.callee.span,
                });
                Ok(Type::Error)
            }

            ExprKind::Assign(assign) => {
                let value_ty = self.check_expr(&assign.value, interner)?;

                if let Some(var) = self.scope.get(assign.target) {
                    if !var.mutable {
                        self.errors.push(TypeError {
                            message: "cannot assign to immutable variable".to_string(),
                            span: expr.span,
                        });
                    }
                    let var_ty = var.ty.clone();
                    if !self.types_compatible(&value_ty, &var_ty) {
                        self.errors.push(TypeError {
                            message: format!("type mismatch: expected {}, got {}", var_ty.name(), value_ty.name()),
                            span: expr.span,
                        });
                    }
                    Ok(var_ty)
                } else {
                    self.errors.push(TypeError {
                        message: "undefined variable".to_string(),
                        span: expr.span,
                    });
                    Ok(Type::Error)
                }
            }

            ExprKind::Grouping(inner) => self.check_expr(inner, interner),
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

impl Default for Analyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;

    fn check(source: &str) -> Result<(), Vec<TypeError>> {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();
        let mut analyzer = Analyzer::new();
        analyzer.analyze(&program, &interner)
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
}
