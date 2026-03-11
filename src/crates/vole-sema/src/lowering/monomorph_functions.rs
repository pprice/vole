use crate::NodeMap;
use vole_frontend::ast::{FuncBody, Stmt};
use vole_identity::NodeId;

/// Check whether sema has analyzed a function body by probing for NodeMap
/// entries. Returns `true` if body node data exists, `false` otherwise.
///
/// Generic function bodies are skipped during initial sema analysis. The
/// monomorph body analysis pass (`analyze_monomorph_bodies`) re-analyzes them
/// with concrete substitutions — for both main-program and module-originating
/// generics. This check is a safety guard: if sema analysis failed to
/// populate the NodeMap for a body (e.g., due to errors), VIR lowering would
/// panic, so we skip and let codegen fall back to the AST path.
pub fn body_has_sema_data(body: &FuncBody, node_map: &NodeMap) -> bool {
    match body {
        FuncBody::Expr(expr) => node_map.get_type(expr.id).is_some(),
        FuncBody::Block(block) => {
            // Check the first expression NodeId reachable from the first statement
            for stmt in &block.stmts {
                if let Some(node_id) = first_expr_node_id(stmt) {
                    return node_map.get_type(node_id).is_some();
                }
            }
            // Empty body — trivially analyzed
            true
        }
    }
}

/// Extract the first expression NodeId from a statement, if any.
fn first_expr_node_id(stmt: &Stmt) -> Option<NodeId> {
    match stmt {
        Stmt::Expr(s) => Some(s.expr.id),
        Stmt::Let(s) => s.init.as_expr().map(|e| e.id),
        Stmt::LetTuple(s) => Some(s.init.id),
        Stmt::If(s) => Some(s.condition.id),
        Stmt::While(s) => Some(s.condition.id),
        Stmt::For(s) => Some(s.iterable.id),
        Stmt::Return(s) => s.value.as_ref().map(|e| e.id),
        Stmt::Raise(_) => None,
        Stmt::Break(_) | Stmt::Continue(_) => None,
    }
}
