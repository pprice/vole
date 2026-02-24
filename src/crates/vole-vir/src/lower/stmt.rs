// lower/stmt.rs
//
// Statement lowering: AST `Stmt` → VIR `VirStmt`.

use vole_frontend::ast::{LetInit, LetStmt, Stmt};
use vole_identity::TypeId;
use vole_sema::IterableKind;

use crate::expr::VirExpr;
use crate::stmt::{VirFor, VirIterKind, VirStmt};

use super::LoweringCtx;
use super::expr::lower_expr;
use super::lower_stmts;

/// Lower a single AST statement into a VIR statement.
///
/// All `Stmt` variants are lowered to typed `VirStmt` nodes.  Expression
/// statements are recursively lowered through `lower_expr`.
///
/// Each variant is listed explicitly so that adding a new `Stmt` variant
/// causes a compile error rather than silently falling through a wildcard.
pub(crate) fn lower_stmt(stmt: &Stmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    match stmt {
        Stmt::Expr(expr_stmt) => VirStmt::Expr {
            value: lower_expr(&expr_stmt.expr, ctx),
        },
        Stmt::While(while_stmt) => lower_while(while_stmt, ctx),
        Stmt::If(if_stmt) => lower_if_stmt(if_stmt, ctx),
        Stmt::Break(_) => VirStmt::Break,
        Stmt::Continue(_) => VirStmt::Continue,
        Stmt::Raise(raise_stmt) => lower_raise(raise_stmt, ctx),
        Stmt::Let(let_stmt) => lower_let(let_stmt, ctx),
        Stmt::For(for_stmt) => lower_for(for_stmt, ctx),
        Stmt::Return(ret) => {
            let value = ret.value.as_ref().map(|v| lower_expr(v, ctx));
            VirStmt::Return { value }
        }
        Stmt::LetTuple(let_tuple) => {
            let value = lower_expr(&let_tuple.init, ctx);
            VirStmt::LetTuple {
                pattern: Box::new(let_tuple.pattern.clone()),
                value,
            }
        }
    }
}

/// Lower a while statement to `VirStmt::While`.
///
/// The condition expression and body statements are recursively lowered.
fn lower_while(while_stmt: &vole_frontend::ast::WhileStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let cond = lower_expr(&while_stmt.condition, ctx);
    let body = lower_stmts(&while_stmt.body.stmts, ctx);
    VirStmt::While { cond, body }
}

/// Lower a raise statement to `VirStmt::Raise`.
///
/// The error name and field value expressions are extracted from the AST.
/// Field values are recursively lowered through `lower_expr`.
fn lower_raise(raise_stmt: &vole_frontend::ast::RaiseStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let fields = raise_stmt
        .fields
        .iter()
        .map(|f| (f.name, lower_expr(&f.value, ctx)))
        .collect();
    VirStmt::Raise {
        error_name: raise_stmt.error_name,
        fields,
    }
}

/// Lower a let statement to `VirStmt::Let`.
///
/// Type aliases (`let T = i32 | i64`) produce no runtime code; they are
/// lowered to `VirStmt::Noop`.
///
/// The binding type (`ty`) comes from:
/// 1. The declared type annotation (via `node_map.get_declared_var_type`),
///    if one was provided in the source — this is the type the codegen
///    should coerce to.
/// 2. Otherwise, the sema-computed expression type.
fn lower_let(let_stmt: &LetStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let init_expr = match &let_stmt.init {
        LetInit::Expr(e) => e,
        // Type aliases produce no runtime code — skip entirely.
        LetInit::TypeAlias(_) => {
            return VirStmt::Noop;
        }
    };

    let value = lower_expr(init_expr, ctx);

    // Determine the binding type: use declared type if annotated, else the
    // init expression's inferred type.
    let declared_ty = ctx.node_map.get_declared_var_type(init_expr.id);
    let expr_ty = ctx
        .node_map
        .get_type(init_expr.id)
        .unwrap_or(TypeId::UNKNOWN);
    let ty = declared_ty.unwrap_or(expr_ty);

    VirStmt::Let {
        name: let_stmt.name,
        value,
        mutable: let_stmt.mutable,
        ty,
    }
}

/// Lower a for statement to `VirStmt::For`.
///
/// Looks up the `IterableKind` from the NodeMap (annotated by sema) and
/// maps it to a `VirIterKind`.  The iterable expression, loop body, and
/// iteration variable are recursively lowered.
fn lower_for(for_stmt: &vole_frontend::ast::ForStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let iterable = lower_expr(&for_stmt.iterable, ctx);
    let body = lower_stmts(&for_stmt.body.stmts, ctx);

    let sema_kind = ctx.node_map.get_iterable_kind(for_stmt.iterable.id);

    let kind = match sema_kind {
        Some(IterableKind::Range) => VirIterKind::Range,
        Some(IterableKind::Array { elem_type }) => {
            let union_storage = ctx.node_map.get_union_storage_kind(for_stmt.iterable.id);
            VirIterKind::Array {
                elem_type,
                union_storage,
            }
        }
        Some(IterableKind::String) => VirIterKind::String,
        Some(IterableKind::IteratorInterface { elem_type }) => {
            VirIterKind::IteratorInterface { elem_type }
        }
        Some(IterableKind::CustomIterator { elem_type }) => {
            VirIterKind::CustomIterator { elem_type }
        }
        Some(IterableKind::CustomIterable { elem_type }) => {
            VirIterKind::CustomIterable { elem_type }
        }
        None => {
            // Fallback for error types — treat as array of i64.
            VirIterKind::Array {
                elem_type: TypeId::I64,
                union_storage: None,
            }
        }
    };

    // Determine the element type for the loop variable.
    let var_type = match kind {
        VirIterKind::Range => TypeId::I64,
        VirIterKind::Array { elem_type, .. } => elem_type,
        VirIterKind::String => TypeId::STRING,
        VirIterKind::IteratorInterface { elem_type }
        | VirIterKind::CustomIterator { elem_type }
        | VirIterKind::CustomIterable { elem_type } => elem_type,
    };

    VirStmt::For(VirFor {
        var_name: for_stmt.var_name,
        var_type,
        iterable,
        body,
        kind,
    })
}

/// Lower an if statement to `VirStmt::Expr { VirExpr::If { ... } }`.
///
/// Vole's VIR has no separate `VirStmt::If` — statement-level `if` is
/// wrapped as a void-typed `VirExpr::If` inside `VirStmt::Expr`.
fn lower_if_stmt(if_stmt: &vole_frontend::ast::IfStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let cond = lower_expr(&if_stmt.condition, ctx);
    let then_body = lower_stmts(&if_stmt.then_branch.stmts, ctx);
    let else_body = if_stmt
        .else_branch
        .as_ref()
        .map(|block| lower_stmts(&block.stmts, ctx));
    VirStmt::Expr {
        value: Box::new(VirExpr::If {
            cond,
            then_body,
            else_body,
            ty: TypeId::VOID,
        }),
    }
}
