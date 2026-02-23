// lower/tests/operators.rs
//
// Tests for binary and unary operator lowering, including And/Or desugar,
// string concat, operator mapping coverage.

use super::*;
use crate::expr::{VirBinOp, VirExpr, VirUnOp};
use crate::lower::expr::{lower_expr, map_binary_op, map_unary_op};
use vole_frontend::ast::{BinaryExpr, BinaryOp, UnaryExpr, UnaryOp};

fn make_binary_expr(left: Expr, op: BinaryOp, right: Expr) -> Expr {
    Expr {
        id: dummy_node_id(),
        kind: ExprKind::Binary(Box::new(BinaryExpr { left, op, right })),
        span: dummy_span(),
    }
}

fn make_unary_expr(op: UnaryOp, operand: Expr) -> Expr {
    Expr {
        id: dummy_node_id(),
        kind: ExprKind::Unary(Box::new(UnaryExpr { op, operand })),
        span: dummy_span(),
    }
}

// -----------------------------------------------------------------------
// Binary expression lowering
// -----------------------------------------------------------------------

#[test]
fn lower_binary_add_produces_binary_op() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_int_expr(1), BinaryOp::Add, make_int_expr(2));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BinaryOp {
            op, lhs, rhs, ty, ..
        } => {
            assert_eq!(*op, VirBinOp::Add);
            assert_eq!(*ty, TypeId::I64);
            match lhs.as_ref() {
                VirExpr::IntLiteral { value: 1, .. } => {}
                other => panic!("expected IntLiteral(1) lhs, got {other:?}"),
            }
            match rhs.as_ref() {
                VirExpr::IntLiteral { value: 2, .. } => {}
                other => panic!("expected IntLiteral(2) rhs, got {other:?}"),
            }
        }
        other => panic!("expected BinaryOp, got {other:?}"),
    }
}

#[test]
fn lower_binary_sub_produces_binary_op() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_int_expr(10), BinaryOp::Sub, make_int_expr(5));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BinaryOp { op, .. } => assert_eq!(*op, VirBinOp::Sub),
        other => panic!("expected BinaryOp(Sub), got {other:?}"),
    }
}

#[test]
fn lower_binary_comparison_produces_binary_op() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_int_expr(1), BinaryOp::Lt, make_int_expr(2));
    node_map.set_type(expr.id, TypeId::BOOL);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BinaryOp { op, ty, .. } => {
            assert_eq!(*op, VirBinOp::Lt);
            assert_eq!(*ty, TypeId::BOOL);
        }
        other => panic!("expected BinaryOp(Lt), got {other:?}"),
    }
}

#[test]
fn lower_binary_bitwise_produces_binary_op() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_int_expr(0xFF), BinaryOp::BitAnd, make_int_expr(0x0F));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BinaryOp { op, .. } => assert_eq!(*op, VirBinOp::BitAnd),
        other => panic!("expected BinaryOp(BitAnd), got {other:?}"),
    }
}

#[test]
fn lower_binary_and_desugars_to_if() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_bool_expr(), BinaryOp::And, make_bool_expr());
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    // a && b -> if a { b } else { false }
    match vir_ref.as_ref() {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            // Condition is the left operand (bool literal true)
            match cond.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true) cond, got {other:?}"),
            }
            // Then branch is the right operand (bool literal true)
            match then_body.trailing.as_deref() {
                Some(VirExpr::BoolLiteral(true)) => {}
                other => panic!("expected BoolLiteral(true) then, got {other:?}"),
            }
            // Else branch is BoolLiteral(false)
            let else_body = else_body.as_ref().expect("And should have else body");
            match else_body.trailing.as_deref() {
                Some(VirExpr::BoolLiteral(false)) => {}
                other => panic!("expected BoolLiteral(false) else, got {other:?}"),
            }
        }
        other => panic!("expected If for And desugar, got {other:?}"),
    }
}

#[test]
fn lower_binary_or_desugars_to_if() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_bool_expr(), BinaryOp::Or, make_bool_expr());
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    // a || b -> if a { true } else { b }
    match vir_ref.as_ref() {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            // Condition is the left operand (bool literal true)
            match cond.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true) cond, got {other:?}"),
            }
            // Then branch is BoolLiteral(true)
            match then_body.trailing.as_deref() {
                Some(VirExpr::BoolLiteral(true)) => {}
                other => panic!("expected BoolLiteral(true) then, got {other:?}"),
            }
            // Else branch is the right operand (bool literal true)
            let else_body = else_body.as_ref().expect("Or should have else body");
            match else_body.trailing.as_deref() {
                Some(VirExpr::BoolLiteral(true)) => {}
                other => panic!("expected BoolLiteral(true) else, got {other:?}"),
            }
        }
        other => panic!("expected If for Or desugar, got {other:?}"),
    }
}

#[test]
fn lower_string_add_produces_string_concat() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let left = Expr {
        id: dummy_node_id(),
        kind: ExprKind::StringLiteral("hello".to_string()),
        span: dummy_span(),
    };
    let right = Expr {
        id: dummy_node_id(),
        kind: ExprKind::StringLiteral(" world".to_string()),
        span: dummy_span(),
    };
    let expr = make_binary_expr(left, BinaryOp::Add, right);
    // Mark the outer expression as STRING to trigger string concat detection
    node_map.set_type(expr.id, TypeId::STRING);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::StringConcat { parts } => {
            assert_eq!(parts.len(), 2);
            match parts[0].as_ref() {
                VirExpr::StringLiteral(sym) => {
                    assert_eq!(interner.resolve(*sym), "hello");
                }
                other => panic!("expected StringLiteral part[0], got {other:?}"),
            }
            match parts[1].as_ref() {
                VirExpr::StringLiteral(sym) => {
                    assert_eq!(interner.resolve(*sym), " world");
                }
                other => panic!("expected StringLiteral part[1], got {other:?}"),
            }
        }
        other => panic!("expected StringConcat, got {other:?}"),
    }
}

#[test]
fn lower_non_string_add_is_not_string_concat() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_binary_expr(make_int_expr(1), BinaryOp::Add, make_int_expr(2));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    // Should be BinaryOp, not StringConcat
    match vir_ref.as_ref() {
        VirExpr::BinaryOp { op, .. } => assert_eq!(*op, VirBinOp::Add),
        other => panic!("expected BinaryOp(Add), got {other:?}"),
    }
}

#[test]
fn lower_binary_lowers_operands_recursively() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    // (1 + 2) * 3 -- the inner `1 + 2` should be lowered to BinaryOp too
    let inner = make_binary_expr(make_int_expr(1), BinaryOp::Add, make_int_expr(2));
    node_map.set_type(inner.id, TypeId::I64);
    let outer = make_binary_expr(inner, BinaryOp::Mul, make_int_expr(3));
    node_map.set_type(outer.id, TypeId::I64);
    let vir_ref = lower_expr(&outer, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BinaryOp { op, lhs, .. } => {
            assert_eq!(*op, VirBinOp::Mul);
            // Inner lhs should also be a BinaryOp
            match lhs.as_ref() {
                VirExpr::BinaryOp { op: inner_op, .. } => {
                    assert_eq!(*inner_op, VirBinOp::Add);
                }
                other => panic!("expected nested BinaryOp(Add), got {other:?}"),
            }
        }
        other => panic!("expected BinaryOp(Mul), got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Unary expression lowering
// -----------------------------------------------------------------------

#[test]
fn lower_unary_neg_produces_unary_op() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_unary_expr(UnaryOp::Neg, make_int_expr(42));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::UnaryOp { op, operand, ty } => {
            assert_eq!(*op, VirUnOp::Neg);
            assert_eq!(*ty, TypeId::I64);
            match operand.as_ref() {
                VirExpr::IntLiteral { value: 42, .. } => {}
                other => panic!("expected IntLiteral(42) operand, got {other:?}"),
            }
        }
        other => panic!("expected UnaryOp(Neg), got {other:?}"),
    }
}

#[test]
fn lower_unary_not_produces_unary_op() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_unary_expr(UnaryOp::Not, make_bool_expr());
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::UnaryOp { op, .. } => assert_eq!(*op, VirUnOp::Not),
        other => panic!("expected UnaryOp(Not), got {other:?}"),
    }
}

#[test]
fn lower_unary_bitnot_produces_unary_op() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = make_unary_expr(UnaryOp::BitNot, make_int_expr(0xFF));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::UnaryOp { op, .. } => assert_eq!(*op, VirUnOp::BitNot),
        other => panic!("expected UnaryOp(BitNot), got {other:?}"),
    }
}

#[test]
fn lower_unary_nested_in_binary() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    // -1 + 2: unary neg on 1, then binary add with 2
    let neg = make_unary_expr(UnaryOp::Neg, make_int_expr(1));
    node_map.set_type(neg.id, TypeId::I64);
    let expr = make_binary_expr(neg, BinaryOp::Add, make_int_expr(2));
    node_map.set_type(expr.id, TypeId::I64);
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::BinaryOp { op, lhs, .. } => {
            assert_eq!(*op, VirBinOp::Add);
            match lhs.as_ref() {
                VirExpr::UnaryOp {
                    op: inner_op,
                    operand,
                    ..
                } => {
                    assert_eq!(*inner_op, VirUnOp::Neg);
                    match operand.as_ref() {
                        VirExpr::IntLiteral { value: 1, .. } => {}
                        other => panic!("expected IntLiteral(1), got {other:?}"),
                    }
                }
                other => panic!("expected UnaryOp(Neg) as lhs, got {other:?}"),
            }
        }
        other => panic!("expected BinaryOp(Add), got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Operator mapping coverage
// -----------------------------------------------------------------------

#[test]
fn map_binary_op_covers_all_variants() {
    // Verify all BinaryOp variants map correctly (excludes And/Or which
    // are handled as Ast escape hatches and never reach map_binary_op in
    // practice, but the mapping function handles them anyway for completeness).
    assert_eq!(map_binary_op(BinaryOp::Add), VirBinOp::Add);
    assert_eq!(map_binary_op(BinaryOp::Sub), VirBinOp::Sub);
    assert_eq!(map_binary_op(BinaryOp::Mul), VirBinOp::Mul);
    assert_eq!(map_binary_op(BinaryOp::Div), VirBinOp::Div);
    assert_eq!(map_binary_op(BinaryOp::Mod), VirBinOp::Mod);
    assert_eq!(map_binary_op(BinaryOp::Eq), VirBinOp::Eq);
    assert_eq!(map_binary_op(BinaryOp::Ne), VirBinOp::Ne);
    assert_eq!(map_binary_op(BinaryOp::Lt), VirBinOp::Lt);
    assert_eq!(map_binary_op(BinaryOp::Le), VirBinOp::Le);
    assert_eq!(map_binary_op(BinaryOp::Gt), VirBinOp::Gt);
    assert_eq!(map_binary_op(BinaryOp::Ge), VirBinOp::Ge);
    assert_eq!(map_binary_op(BinaryOp::And), VirBinOp::And);
    assert_eq!(map_binary_op(BinaryOp::Or), VirBinOp::Or);
    assert_eq!(map_binary_op(BinaryOp::BitAnd), VirBinOp::BitAnd);
    assert_eq!(map_binary_op(BinaryOp::BitOr), VirBinOp::BitOr);
    assert_eq!(map_binary_op(BinaryOp::BitXor), VirBinOp::BitXor);
    assert_eq!(map_binary_op(BinaryOp::Shl), VirBinOp::Shl);
    assert_eq!(map_binary_op(BinaryOp::Shr), VirBinOp::Shr);
}

#[test]
fn map_unary_op_covers_all_variants() {
    assert_eq!(map_unary_op(UnaryOp::Neg), VirUnOp::Neg);
    assert_eq!(map_unary_op(UnaryOp::Not), VirUnOp::Not);
    assert_eq!(map_unary_op(UnaryOp::BitNot), VirUnOp::BitNot);
}
