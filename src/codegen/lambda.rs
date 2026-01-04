// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.
// This module contains type inference and helper functions for lambda compilation.
//
// Note: The main compilation functions (compile_lambda, compile_pure_lambda,
// compile_lambda_with_captures, etc.) remain in compiler.rs due to circular
// dependencies with compile_expr and compile_stmt. This module extracts the
// standalone helpers that don't have such dependencies.

use std::collections::HashMap;

use crate::frontend::{BinaryOp, Expr, ExprKind, LambdaBody, Symbol};
use crate::sema::{FunctionType, Type};

use super::types::{CompileCtx, resolve_type_expr};

/// Information about a captured variable for lambda compilation
#[derive(Clone)]
pub(crate) struct CaptureBinding {
    /// Index in the closure's captures array
    pub index: usize,
    /// Vole type of the captured variable
    pub vole_type: Type,
}

/// Infer the return type of a lambda expression body.
/// This is used when no explicit return type is provided.
pub(crate) fn infer_lambda_return_type(
    body: &LambdaBody,
    param_types: &[(Symbol, Type)],
    ctx: &CompileCtx,
) -> Type {
    match body {
        LambdaBody::Expr(expr) => infer_expr_type(expr, param_types, ctx),
        LambdaBody::Block(_) => {
            // Block bodies should use explicit return or default to void
            // For now, default to i64 for backwards compatibility
            Type::I64
        }
    }
}

/// Infer the type of an expression given parameter types as context.
/// Returns I64 as fallback for unknown cases.
pub(crate) fn infer_expr_type(
    expr: &Expr,
    param_types: &[(Symbol, Type)],
    ctx: &CompileCtx,
) -> Type {
    match &expr.kind {
        ExprKind::IntLiteral(_) => Type::I64, // Int literals compile to i64
        ExprKind::FloatLiteral(_) => Type::F64,
        ExprKind::BoolLiteral(_) => Type::Bool,
        ExprKind::StringLiteral(_) => Type::String,
        ExprKind::InterpolatedString(_) => Type::String,
        ExprKind::Nil => Type::Nil,

        ExprKind::Identifier(sym) => {
            // Look up in parameters first
            for (name, ty) in param_types {
                if name == sym {
                    return ty.clone();
                }
            }
            // Look up in globals
            for global in ctx.globals {
                if global.name == *sym
                    && let Some(type_expr) = &global.ty
                {
                    return resolve_type_expr(type_expr, ctx.type_aliases);
                }
            }
            Type::I64 // Fallback
        }

        ExprKind::Binary(bin) => {
            let left_ty = infer_expr_type(&bin.left, param_types, ctx);
            let right_ty = infer_expr_type(&bin.right, param_types, ctx);

            match bin.op {
                // Comparison operators always return bool
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge => Type::Bool,

                // Logical operators return bool
                BinaryOp::And | BinaryOp::Or => Type::Bool,

                // Arithmetic: use the "wider" type or left type
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    // If both are the same, use that type
                    if left_ty == right_ty {
                        left_ty
                    } else {
                        // Simple widening logic
                        match (&left_ty, &right_ty) {
                            (Type::I64, _) | (_, Type::I64) => Type::I64,
                            (Type::F64, _) | (_, Type::F64) => Type::F64,
                            (Type::I32, _) | (_, Type::I32) => Type::I32,
                            _ => left_ty,
                        }
                    }
                }

                // Bitwise operators preserve type
                BinaryOp::BitAnd
                | BinaryOp::BitOr
                | BinaryOp::BitXor
                | BinaryOp::Shl
                | BinaryOp::Shr => left_ty,
            }
        }

        ExprKind::Unary(un) => infer_expr_type(&un.operand, param_types, ctx),

        ExprKind::Call(call) => {
            // Infer the callee type to get the return type
            let callee_ty = infer_expr_type(&call.callee, param_types, ctx);
            match callee_ty {
                Type::Function(ft) => *ft.return_type,
                _ => Type::I64, // Fallback if callee isn't a function type
            }
        }

        ExprKind::Lambda(lambda) => {
            // For nested lambdas, construct the function type
            let lambda_params: Vec<Type> = lambda
                .params
                .iter()
                .map(|p| {
                    p.ty.as_ref()
                        .map(|t| resolve_type_expr(t, ctx.type_aliases))
                        .unwrap_or(Type::I64)
                })
                .collect();
            let return_ty = lambda
                .return_type
                .as_ref()
                .map(|t| resolve_type_expr(t, ctx.type_aliases))
                .unwrap_or(Type::I64);
            Type::Function(FunctionType {
                params: lambda_params,
                return_type: Box::new(return_ty),
                is_closure: !lambda.captures.borrow().is_empty(),
            })
        }

        _ => Type::I64, // Fallback for complex expressions
    }
}

/// Create a new CaptureBinding
impl CaptureBinding {
    pub fn new(index: usize, vole_type: Type) -> Self {
        Self { index, vole_type }
    }
}

/// Build capture bindings from a list of captures and variable types
pub(crate) fn build_capture_bindings(
    captures: &[crate::frontend::Capture],
    variables: &HashMap<Symbol, (cranelift::prelude::Variable, Type)>,
) -> HashMap<Symbol, CaptureBinding> {
    let mut bindings = HashMap::new();
    for (i, capture) in captures.iter().enumerate() {
        let vole_type = variables
            .get(&capture.name)
            .map(|(_, ty)| ty.clone())
            .unwrap_or(Type::I64);
        bindings.insert(capture.name, CaptureBinding::new(i, vole_type));
    }
    bindings
}
