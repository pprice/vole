// lower.rs
//
// Trivial AST-to-VIR lowering (Phase 0).
//
// Every AST node is wrapped in a `VirStmt::Ast` or `VirExpr::Ast` escape
// hatch.  No real lowering happens here — this is the bridge that enables
// incremental migration: once wired into the pipeline, individual statement
// and expression kinds can be lowered one at a time.

use vole_frontend::ast::{FuncBody, FuncDecl, Stmt};
use vole_identity::{FunctionId, Symbol, TypeId};
use vole_sema::node_map::NodeMap;

use crate::expr::VirExpr;
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::VirStmt;

/// Lower a single function declaration into a `VirFunction`.
///
/// `func_id`, `name`, `param_types`, and `return_type` come from the sema
/// entity registry — they are resolved during semantic analysis and passed
/// in by the caller (the compilation pipeline).
///
/// `node_map` is accepted for API compatibility with future phases that will
/// look up per-expression types.  Phase 0 does not use it.
pub fn lower_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    _node_map: &NodeMap,
) -> VirFunction {
    let body = lower_func_body(&func.body);
    VirFunction {
        id: func_id,
        name,
        params: param_types.to_vec(),
        return_type,
        body,
    }
}

/// Lower a `FuncBody` (block or expression) into a `VirBody`.
///
/// Block bodies have their statements wrapped individually; expression bodies
/// become a single trailing `VirExpr::Ast`.
fn lower_func_body(body: &FuncBody) -> VirBody {
    match body {
        FuncBody::Block(block) => lower_stmts(&block.stmts),
        FuncBody::Expr(expr) => {
            let trailing = lower_expr_to_ast(expr);
            VirBody {
                stmts: Vec::new(),
                trailing: Some(trailing),
            }
        }
    }
}

/// Wrap a slice of AST statements into a `VirBody`.
///
/// Each statement is wrapped wholesale in `VirStmt::Ast` — no recursion
/// into sub-expressions.
fn lower_stmts(stmts: &[Stmt]) -> VirBody {
    let vir_stmts: Vec<VirStmt> = stmts
        .iter()
        .map(|stmt| VirStmt::Ast {
            stmt: Box::new(stmt.clone()),
        })
        .collect();
    VirBody {
        stmts: vir_stmts,
        trailing: None,
    }
}

/// Wrap an AST expression in a `VirExpr::Ast` escape hatch.
///
/// Uses `TypeId::UNKNOWN` because Phase 0 does not resolve per-expression
/// types — the Ast escape hatch defers all type decisions to codegen, which
/// still reads the NodeMap directly.
fn lower_expr_to_ast(expr: &vole_frontend::Expr) -> VirRef {
    Box::new(VirExpr::Ast {
        expr: Box::new(expr.clone()),
        ty: TypeId::UNKNOWN,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use vole_frontend::NodeId;
    use vole_frontend::ast::{Block, Expr, ExprKind};
    use vole_identity::{ModuleId, Span};

    fn dummy_span() -> Span {
        Span::default()
    }

    fn dummy_node_id() -> NodeId {
        NodeId::new(ModuleId::new(0), 0)
    }

    fn dummy_func_id() -> FunctionId {
        FunctionId::new(0)
    }

    fn dummy_type_id() -> TypeId {
        TypeId::from_raw(999)
    }

    fn make_break_stmt() -> Stmt {
        Stmt::Break(dummy_span())
    }

    fn make_continue_stmt() -> Stmt {
        Stmt::Continue(dummy_span())
    }

    fn make_bool_expr() -> Expr {
        Expr {
            id: dummy_node_id(),
            kind: ExprKind::BoolLiteral(true),
            span: dummy_span(),
        }
    }

    fn make_block_func(stmts: Vec<Stmt>) -> FuncDecl {
        FuncDecl {
            name: Symbol::UNKNOWN,
            type_params: vec![],
            params: vec![],
            return_type: None,
            body: FuncBody::Block(Block {
                stmts,
                span: dummy_span(),
            }),
            annotations: vec![],
            span: dummy_span(),
        }
    }

    fn make_expr_func(expr: Expr) -> FuncDecl {
        FuncDecl {
            name: Symbol::UNKNOWN,
            type_params: vec![],
            params: vec![],
            return_type: None,
            body: FuncBody::Expr(Box::new(expr)),
            annotations: vec![],
            span: dummy_span(),
        }
    }

    fn empty_node_map() -> NodeMap {
        NodeMap::default()
    }

    #[test]
    fn lower_empty_block_function() {
        let func = make_block_func(vec![]);
        let node_map = empty_node_map();
        let ret_ty = dummy_type_id();

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &[],
            ret_ty,
            &node_map,
        );

        assert_eq!(vir.id, dummy_func_id());
        assert_eq!(vir.return_type, ret_ty);
        assert!(vir.params.is_empty());
        assert!(vir.body.stmts.is_empty());
        assert!(vir.body.trailing.is_none());
    }

    #[test]
    fn lower_block_function_wraps_stmts_as_ast() {
        let func = make_block_func(vec![make_break_stmt(), make_continue_stmt()]);
        let node_map = empty_node_map();
        let ret_ty = dummy_type_id();

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &[],
            ret_ty,
            &node_map,
        );

        assert_eq!(vir.body.stmts.len(), 2);
        assert!(vir.body.trailing.is_none());

        // Every statement should be VirStmt::Ast
        for stmt in &vir.body.stmts {
            match stmt {
                VirStmt::Ast { .. } => {}
                other => panic!("expected VirStmt::Ast, got {other:?}"),
            }
        }
    }

    #[test]
    fn lower_expr_body_function_sets_trailing() {
        let func = make_expr_func(make_bool_expr());
        let node_map = empty_node_map();
        let ret_ty = dummy_type_id();

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &[],
            ret_ty,
            &node_map,
        );

        assert!(vir.body.stmts.is_empty());
        assert!(vir.body.trailing.is_some());

        match vir.body.trailing.as_deref() {
            Some(VirExpr::Ast { ty, .. }) => {
                assert_eq!(*ty, TypeId::UNKNOWN);
            }
            other => panic!("expected VirExpr::Ast trailing, got {other:?}"),
        }
    }

    #[test]
    fn lower_preserves_params_and_return_type() {
        let func = make_block_func(vec![]);
        let node_map = empty_node_map();
        let ret_ty = dummy_type_id();
        let param_a = TypeId::from_raw(10);
        let param_b = TypeId::from_raw(20);
        let params = vec![(Symbol::UNKNOWN, param_a), (Symbol::UNKNOWN, param_b)];

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &params,
            ret_ty,
            &node_map,
        );

        assert_eq!(vir.params.len(), 2);
        assert_eq!(vir.params[0].1, param_a);
        assert_eq!(vir.params[1].1, param_b);
        assert_eq!(vir.return_type, ret_ty);
    }

    #[test]
    fn lower_stmts_preserves_order() {
        let stmts = vec![make_break_stmt(), make_continue_stmt(), make_break_stmt()];
        let body = lower_stmts(&stmts);

        assert_eq!(body.stmts.len(), 3);
        assert!(body.trailing.is_none());

        // Verify the inner AST statements match
        match &body.stmts[0] {
            VirStmt::Ast { stmt } => match stmt.as_ref() {
                Stmt::Break(_) => {}
                other => panic!("expected Break, got {other:?}"),
            },
            other => panic!("expected Ast, got {other:?}"),
        }
        match &body.stmts[1] {
            VirStmt::Ast { stmt } => match stmt.as_ref() {
                Stmt::Continue(_) => {}
                other => panic!("expected Continue, got {other:?}"),
            },
            other => panic!("expected Ast, got {other:?}"),
        }
        match &body.stmts[2] {
            VirStmt::Ast { stmt } => match stmt.as_ref() {
                Stmt::Break(_) => {}
                other => panic!("expected Break, got {other:?}"),
            },
            other => panic!("expected Ast, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_to_ast_uses_unknown_type() {
        let expr = make_bool_expr();
        let vir_ref = lower_expr_to_ast(&expr);

        match vir_ref.as_ref() {
            VirExpr::Ast { expr: inner, ty } => {
                assert_eq!(*ty, TypeId::UNKNOWN);
                match &inner.kind {
                    ExprKind::BoolLiteral(true) => {}
                    other => panic!("expected BoolLiteral(true), got {other:?}"),
                }
            }
            other => panic!("expected Ast, got {other:?}"),
        }
    }
}
