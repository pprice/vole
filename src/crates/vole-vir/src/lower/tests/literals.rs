// lower/tests/literals.rs
//
// Tests for literal expression lowering: bool, int, float, string, wide,
// grouping, and unknown-kind fallback.

use super::*;
use crate::expr::VirExpr;
use crate::lower::expr::lower_expr;

#[test]
fn lower_expr_bool_literal() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_bool_expr();
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BoolLiteral(true) => {}
        other => panic!("expected BoolLiteral(true), got {other:?}"),
    }
}

#[test]
fn lower_expr_int_literal_no_type() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::IntLiteral(42, None),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    // No type in NodeMap -> TypeId::UNKNOWN
    match vir_ref.as_ref() {
        VirExpr::IntLiteral { value: 42, ty } => {
            assert_eq!(*ty, TypeId::UNKNOWN);
        }
        other => panic!("expected IntLiteral, got {other:?}"),
    }
}

#[test]
fn lower_expr_int_literal_with_type() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::I32);
    let expr = Expr {
        id: node_id,
        kind: ExprKind::IntLiteral(99, None),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::IntLiteral { value: 99, ty } => {
            assert_eq!(*ty, TypeId::I32);
        }
        other => panic!("expected IntLiteral with I32, got {other:?}"),
    }
}

#[test]
fn lower_expr_int_literal_i128_becomes_wide() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::I128);
    let expr = Expr {
        id: node_id,
        kind: ExprKind::IntLiteral(42, None),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::WideLiteral { low, high, ty } => {
            assert_eq!(*low, 42);
            assert_eq!(*high, 0);
            assert_eq!(*ty, TypeId::I128);
        }
        other => panic!("expected WideLiteral for i128, got {other:?}"),
    }
}

#[test]
fn lower_expr_negative_int_i128_sign_extends() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::I128);
    let expr = Expr {
        id: node_id,
        kind: ExprKind::IntLiteral(-1, None),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::WideLiteral { low, high, ty } => {
            // -1 as i128 = all 1-bits -> low = u64::MAX, high = u64::MAX
            assert_eq!(*low, u64::MAX);
            assert_eq!(*high, u64::MAX);
            assert_eq!(*ty, TypeId::I128);
        }
        other => panic!("expected WideLiteral for negative i128, got {other:?}"),
    }
}

#[test]
fn lower_expr_float_literal() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::F64);
    let expr = Expr {
        id: node_id,
        kind: ExprKind::FloatLiteral(3.14, None),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::FloatLiteral { value, ty } => {
            assert!((*value - 3.14).abs() < f64::EPSILON);
            assert_eq!(*ty, TypeId::F64);
        }
        other => panic!("expected FloatLiteral, got {other:?}"),
    }
}

#[test]
fn lower_expr_grouping_strips_parens() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let inner = Expr {
        id: dummy_node_id(),
        kind: ExprKind::BoolLiteral(false),
        span: dummy_span(),
    };
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Grouping(Box::new(inner)),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BoolLiteral(false) => {}
        other => panic!("expected BoolLiteral(false) through grouping, got {other:?}"),
    }
}

#[test]
fn lower_expr_unknown_kind_becomes_ast() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Identifier(Symbol::UNKNOWN),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// StringLiteral lowering
// -----------------------------------------------------------------------

#[test]
fn lower_expr_string_literal() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::StringLiteral("hello world".to_string()),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::StringLiteral(sym) => {
            assert_eq!(interner.resolve(*sym), "hello world");
        }
        other => panic!("expected StringLiteral, got {other:?}"),
    }
}

#[test]
fn lower_expr_string_literal_empty() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::StringLiteral(String::new()),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::StringLiteral(sym) => {
            assert_eq!(interner.resolve(*sym), "");
        }
        other => panic!("expected StringLiteral for empty string, got {other:?}"),
    }
}

#[test]
fn lower_expr_string_literal_deduplicates() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr1 = Expr {
        id: dummy_node_id(),
        kind: ExprKind::StringLiteral("same".to_string()),
        span: dummy_span(),
    };
    let expr2 = Expr {
        id: dummy_node_id(),
        kind: ExprKind::StringLiteral("same".to_string()),
        span: dummy_span(),
    };
    let vir1 = lower_expr(&expr1, &node_map, &mut interner);
    let vir2 = lower_expr(&expr2, &node_map, &mut interner);

    // Both should produce the same Symbol
    let sym1 = match vir1.as_ref() {
        VirExpr::StringLiteral(s) => *s,
        _ => panic!("expected StringLiteral"),
    };
    let sym2 = match vir2.as_ref() {
        VirExpr::StringLiteral(s) => *s,
        _ => panic!("expected StringLiteral"),
    };
    assert_eq!(sym1, sym2);
}
