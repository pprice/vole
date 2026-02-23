// stmt.rs
//
// VIR statement nodes.

use vole_frontend::Stmt;

/// A single VIR statement.
///
/// Like `VirExpr`, the `Ast` variant is a temporary escape hatch for
/// statements that have not yet been lowered from the AST.
#[derive(Debug, Clone)]
pub enum VirStmt {
    /// Escape hatch: an AST statement not yet lowered to VIR.
    Ast { stmt: Box<Stmt> },
}
