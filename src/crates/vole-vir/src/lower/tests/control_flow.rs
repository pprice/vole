// lower/tests/control_flow.rs
//
// Tests for control flow expression lowering: If, Block, Yield.

use super::*;
use crate::expr::VirExpr;
use crate::lower::expr::lower_expr;
use crate::stmt::VirStmt;

// -----------------------------------------------------------------------
// If expression lowering
// -----------------------------------------------------------------------

fn make_if_expr(condition: Expr, then_branch: Expr, else_branch: Option<Expr>) -> Expr {
    use vole_frontend::ast::IfExpr;
    Expr {
        id: dummy_node_id(),
        kind: ExprKind::If(Box::new(IfExpr {
            condition,
            then_branch,
            else_branch,
            span: dummy_span(),
        })),
        span: dummy_span(),
    }
}

#[test]
fn lower_if_expr_produces_vir_if() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_if_expr(make_bool_expr(), make_int_expr(1), Some(make_int_expr(2)));
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            match cond.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true) cond, got {other:?}"),
            }
            match then_body.trailing.as_deref() {
                Some(VirExpr::IntLiteral { value: 1, .. }) => {}
                other => panic!("expected IntLiteral(1) then, got {other:?}"),
            }
            assert!(then_body.stmts.is_empty());
            let else_body = else_body.as_ref().expect("should have else body");
            match else_body.trailing.as_deref() {
                Some(VirExpr::IntLiteral { value: 2, .. }) => {}
                other => panic!("expected IntLiteral(2) else, got {other:?}"),
            }
            assert!(else_body.stmts.is_empty());
        }
        other => panic!("expected VirExpr::If, got {other:?}"),
    }
}

#[test]
fn lower_if_expr_no_else() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_if_expr(make_bool_expr(), make_int_expr(42), None);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::If {
            else_body: None, ..
        } => {}
        VirExpr::If {
            else_body: Some(_), ..
        } => panic!("expected no else body"),
        other => panic!("expected VirExpr::If, got {other:?}"),
    }
}

#[test]
fn lower_if_expr_preserves_type() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_if_expr(make_bool_expr(), make_int_expr(1), Some(make_int_expr(2)));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::If { ty, .. } => assert_eq!(*ty, TypeId::I64),
        other => panic!("expected VirExpr::If, got {other:?}"),
    }
}

#[test]
fn lower_if_expr_recursive_lowering() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    // if true { if false { 1 } else { 2 } } else { 3 }
    let inner_if = make_if_expr(
        Expr {
            id: dummy_node_id(),
            kind: ExprKind::BoolLiteral(false),
            span: dummy_span(),
        },
        make_int_expr(1),
        Some(make_int_expr(2)),
    );
    let expr = make_if_expr(make_bool_expr(), inner_if, Some(make_int_expr(3)));
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::If { then_body, .. } => {
            // The then branch should contain a nested VirExpr::If
            match then_body.trailing.as_deref() {
                Some(VirExpr::If { .. }) => {}
                other => panic!("expected nested VirExpr::If, got {other:?}"),
            }
        }
        other => panic!("expected VirExpr::If, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Block expression lowering
// -----------------------------------------------------------------------

#[test]
fn lower_block_expr_empty() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![],
            trailing_expr: None,
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            assert!(stmts.is_empty());
            assert!(trailing.is_none());
        }
        other => panic!("expected VirExpr::Block, got {other:?}"),
    }
}

#[test]
fn lower_block_expr_with_trailing() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![],
            trailing_expr: Some(make_int_expr(99)),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            assert!(stmts.is_empty());
            match trailing.as_deref() {
                Some(VirExpr::IntLiteral { value: 99, .. }) => {}
                other => panic!("expected IntLiteral(99) trailing, got {other:?}"),
            }
        }
        other => panic!("expected VirExpr::Block, got {other:?}"),
    }
}

#[test]
fn lower_block_expr_with_stmts_and_trailing() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![make_break_stmt()],
            trailing_expr: Some(make_bool_expr()),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            assert_eq!(stmts.len(), 1);
            match &stmts[0] {
                VirStmt::Ast { .. } => {}
                other => panic!("expected VirStmt::Ast for break, got {other:?}"),
            }
            match trailing.as_deref() {
                Some(VirExpr::BoolLiteral(true)) => {}
                other => panic!("expected BoolLiteral(true) trailing, got {other:?}"),
            }
        }
        other => panic!("expected VirExpr::Block, got {other:?}"),
    }
}

#[test]
fn lower_block_expr_preserves_type() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::I64);
    let expr = Expr {
        id: node_id,
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![],
            trailing_expr: Some(make_int_expr(42)),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Block { ty, .. } => assert_eq!(*ty, TypeId::I64),
        other => panic!("expected VirExpr::Block, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Yield expression lowering
// -----------------------------------------------------------------------

#[test]
fn lower_expr_yield_produces_vir_yield() {
    use vole_frontend::ast::YieldExpr;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Yield(Box::new(YieldExpr {
            value: make_int_expr(42),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Yield { value } => match value.as_ref() {
            VirExpr::IntLiteral { value: 42, .. } => {}
            other => panic!("expected IntLiteral(42) inside Yield, got {other:?}"),
        },
        other => panic!("expected VirExpr::Yield, got {other:?}"),
    }
}

#[test]
fn lower_expr_yield_lowers_inner_recursively() {
    use vole_frontend::ast::YieldExpr;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    // yield true -- the inner bool should be lowered to VirExpr::BoolLiteral
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Yield(Box::new(YieldExpr {
            value: make_bool_expr(),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Yield { value } => match value.as_ref() {
            VirExpr::BoolLiteral(true) => {}
            other => panic!("expected BoolLiteral(true) inside Yield, got {other:?}"),
        },
        other => panic!("expected VirExpr::Yield, got {other:?}"),
    }
}
