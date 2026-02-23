// expr.rs
//
// VIR expression nodes.

use vole_frontend::Expr;
use vole_identity::TypeId;

/// A single VIR expression.
///
/// Every variant carries enough information for codegen to emit instructions
/// without consulting sema.  During the incremental migration, the `Ast`
/// escape-hatch lets us lower one expression kind at a time while the rest
/// pass through as raw AST nodes.
#[derive(Debug, Clone)]
pub enum VirExpr {
    /// Escape hatch: an AST expression that has not yet been lowered to VIR.
    ///
    /// `ty` is the sema-computed type so codegen can still make layout
    /// decisions without reaching back into the node map.
    Ast { expr: Box<Expr>, ty: TypeId },
}
