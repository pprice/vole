// lower/stmt.rs
//
// Statement lowering: AST `Stmt` → VIR `VirStmt`.

use vole_frontend::Interner;
use vole_frontend::ast::Stmt;
use vole_sema::node_map::NodeMap;

use crate::stmt::VirStmt;

use super::expr::lower_expr;

/// Lower a single AST statement into a VIR statement.
///
/// Expression statements (`Stmt::Expr`) are lowered through `lower_expr`,
/// which produces proper VIR for known expression kinds.  All other
/// statement kinds are wrapped in the `VirStmt::Ast` escape hatch.
///
/// Each variant is listed explicitly so that adding a new `Stmt` variant
/// causes a compile error rather than silently falling through a wildcard.
pub(crate) fn lower_stmt(stmt: &Stmt, node_map: &NodeMap, interner: &mut Interner) -> VirStmt {
    match stmt {
        Stmt::Expr(expr_stmt) => VirStmt::Expr {
            value: lower_expr(&expr_stmt.expr, node_map, interner),
        },
        // Ast escape hatches — explicitly listed so new Stmt variants
        // cause a compile error rather than silently falling through.
        Stmt::Let(_)
        | Stmt::LetTuple(_)
        | Stmt::While(_)
        | Stmt::For(_)
        | Stmt::If(_)
        | Stmt::Break(_)
        | Stmt::Continue(_)
        | Stmt::Return(_)
        | Stmt::Raise(_) => VirStmt::Ast {
            stmt: Box::new(stmt.clone()),
        },
    }
}
