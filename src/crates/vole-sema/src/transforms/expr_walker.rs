// vole-sema/src/transforms/expr_walker.rs
//! Generic AST expression walkers.
//!
//! Provides reusable traversal helpers that eliminate duplicated match arms
//! across the generator transform functions (`expr_contains_yield`,
//! `collect_yields_from_expr`, `rewrite_captured_refs`).
//!
//! Two flavours:
//!
//! - **Query** (`any_child_expr`): visit child sub-expressions by shared
//!   reference. Used by boolean checks and collection passes.
//! - **Transform** (`map_expr_children`): rebuild an expression tree by
//!   applying a mapping function to every child sub-expression. Used by
//!   the captured-ref rewriter.

use vole_frontend::ast::*;

// ---------------------------------------------------------------------------
// Query walkers
// ---------------------------------------------------------------------------

/// Visit every immediate child expression of `expr` by calling `visit`.
///
/// Returns `true` (short-circuits) if any call to `visit` returns `true`.
/// Handles all `ExprKind` variants -- callers only need to intercept
/// variant-specific cases *before* delegating here.
pub fn any_child_expr(expr: &Expr, visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    match &expr.kind {
        ExprKind::Binary(bin) => visit(&bin.left) || visit(&bin.right),
        ExprKind::Unary(un) => visit(&un.operand),
        ExprKind::Call(call) => visit(&call.callee) || call.args.iter().any(|a| visit(a.expr())),
        ExprKind::Grouping(inner) => visit(inner),
        ExprKind::ArrayLiteral(elems) => elems.iter().any(&mut *visit),
        ExprKind::RepeatLiteral { element, .. } => visit(element),
        ExprKind::Index(idx) => visit(&idx.object) || visit(&idx.index),
        ExprKind::Match(m) => visit(&m.scrutinee) || m.arms.iter().any(|arm| visit(&arm.body)),
        ExprKind::NullCoalesce(nc) => visit(&nc.value) || visit(&nc.default),
        ExprKind::Is(is_expr) => visit(&is_expr.value),
        ExprKind::FieldAccess(fa) => visit(&fa.object),
        ExprKind::OptionalChain(oc) => visit(&oc.object),
        ExprKind::OptionalMethodCall(omc) => {
            visit(&omc.object) || omc.args.iter().any(|a| visit(a.expr()))
        }
        ExprKind::MethodCall(mc) => visit(&mc.object) || mc.args.iter().any(|a| visit(a.expr())),
        ExprKind::StructLiteral(sl) => sl.fields.iter().any(|f| visit(&f.value)),
        ExprKind::Assign(assign) => visit(&assign.value),
        ExprKind::CompoundAssign(ca) => visit(&ca.value),
        ExprKind::Range(range) => visit(&range.start) || visit(&range.end),
        ExprKind::Try(inner) => visit(inner),
        ExprKind::Yield(y) => visit(&y.value),
        ExprKind::InterpolatedString(parts) => parts.iter().any(|p| match p {
            StringPart::Literal(_) => false,
            StringPart::Expr(e) => visit(e),
        }),
        ExprKind::Lambda(lambda) => match &lambda.body {
            FuncBody::Expr(e) => visit(e),
            FuncBody::Block(b) => any_child_expr_in_block(b, visit),
        },
        ExprKind::Block(block) => {
            any_child_expr_in_stmts(&block.stmts, visit)
                || block.trailing_expr.as_ref().is_some_and(&mut *visit)
        }
        ExprKind::If(if_expr) => {
            visit(&if_expr.condition)
                || visit(&if_expr.then_branch)
                || if_expr.else_branch.as_ref().is_some_and(&mut *visit)
        }
        ExprKind::When(when_expr) => when_expr
            .arms
            .iter()
            .any(|arm| arm.condition.as_ref().is_some_and(&mut *visit) || visit(&arm.body)),
        // Leaf expressions
        ExprKind::IntLiteral(..)
        | ExprKind::FloatLiteral(..)
        | ExprKind::BoolLiteral(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::Identifier(_)
        | ExprKind::Unreachable
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_) => false,
    }
}

/// Short-circuit check across all expressions in a block.
pub fn any_child_expr_in_block(block: &Block, visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    any_child_expr_in_stmts(&block.stmts, visit)
}

fn any_child_expr_in_stmts(stmts: &[Stmt], visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    stmts.iter().any(|s| any_child_expr_in_stmt(s, visit))
}

/// Short-circuit check across all expressions in a statement.
pub fn any_child_expr_in_stmt(stmt: &Stmt, visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    match stmt {
        Stmt::Expr(expr_stmt) => visit(&expr_stmt.expr),
        Stmt::Let(let_stmt) => match &let_stmt.init {
            LetInit::Expr(e) => visit(e),
            LetInit::TypeAlias(_) => false,
        },
        Stmt::While(while_stmt) => {
            visit(&while_stmt.condition) || any_child_expr_in_block(&while_stmt.body, visit)
        }
        Stmt::For(for_stmt) => {
            visit(&for_stmt.iterable) || any_child_expr_in_block(&for_stmt.body, visit)
        }
        Stmt::If(if_stmt) => {
            visit(&if_stmt.condition)
                || any_child_expr_in_block(&if_stmt.then_branch, visit)
                || if_stmt
                    .else_branch
                    .as_ref()
                    .is_some_and(|b| any_child_expr_in_block(b, visit))
        }
        Stmt::Return(ret_stmt) => ret_stmt.value.as_ref().is_some_and(&mut *visit),
        Stmt::LetTuple(lt) => visit(&lt.init),
        Stmt::Raise(_) | Stmt::Break(_) | Stmt::Continue(_) => false,
    }
}
