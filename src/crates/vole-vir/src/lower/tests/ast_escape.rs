// lower/tests/ast_escape.rs
//
// Tests for AST escape hatch lowering: Range, Unreachable, Import, TypeLiteral,
// Assign, CompoundAssign, ArrayLiteral, RepeatLiteral, Call.

use super::*;
use crate::expr::VirExpr;
use crate::lower::expr::lower_expr;

// -----------------------------------------------------------------------
// Ast escape hatch lowering: Range, Unreachable, Import, TypeLiteral
// -----------------------------------------------------------------------

#[test]
fn lower_expr_range_becomes_ast() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Range(Box::new(vole_frontend::ast::RangeExpr {
            start: make_int_expr(0),
            end: make_int_expr(10),
            inclusive: false,
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for Range, got {other:?}"),
    }
}

#[test]
fn lower_expr_unreachable_becomes_ast() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Unreachable,
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for Unreachable, got {other:?}"),
    }
}

#[test]
fn lower_expr_import_becomes_ast() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Import("std:math".to_string()),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for Import, got {other:?}"),
    }
}

#[test]
fn lower_expr_type_literal_becomes_ast() {
    use vole_frontend::ast::{PrimitiveType, TypeExpr, TypeExprKind};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::TypeLiteral(Box::new(TypeExpr {
            kind: TypeExprKind::Primitive(PrimitiveType::I64),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for TypeLiteral, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Ast escape hatch lowering: Assign, CompoundAssign, ArrayLiteral,
// RepeatLiteral (vol-aq9j, vol-w4mg)
// -----------------------------------------------------------------------

#[test]
fn lower_expr_assign_becomes_ast() {
    use vole_frontend::ast::{AssignExpr, AssignTarget};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Assign(Box::new(AssignExpr {
            target: AssignTarget::Variable(Symbol::UNKNOWN),
            value: make_int_expr(42),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for Assign, got {other:?}"),
    }
}

#[test]
fn lower_expr_compound_assign_becomes_ast() {
    use vole_frontend::ast::{AssignTarget, CompoundAssignExpr, CompoundOp};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::CompoundAssign(Box::new(CompoundAssignExpr {
            target: AssignTarget::Variable(Symbol::UNKNOWN),
            op: CompoundOp::Add,
            value: make_int_expr(1),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for CompoundAssign, got {other:?}"),
    }
}

#[test]
fn lower_expr_array_literal_becomes_ast() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::ArrayLiteral(vec![make_int_expr(1), make_int_expr(2), make_int_expr(3)]),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for ArrayLiteral, got {other:?}"),
    }
}

#[test]
fn lower_expr_repeat_literal_becomes_ast() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::RepeatLiteral {
            element: Box::new(make_int_expr(0)),
            count: 10,
        },
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for RepeatLiteral, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Call expression lowering (vol-kzj3)
// -----------------------------------------------------------------------

#[test]
fn lower_expr_call_becomes_ast() {
    use vole_frontend::ast::{CallArg, CallExpr};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let callee = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Identifier(Symbol::UNKNOWN),
        span: dummy_span(),
    };
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Call(Box::new(CallExpr {
            callee,
            args: vec![CallArg::Positional(make_int_expr(42))],
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    // Calls stay as Ast escape hatch until sema annotates call
    // dispatch kind (similar to MethodDispatchKind for method calls).
    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for Call, got {other:?}"),
    }
}

#[test]
fn lower_expr_call_no_args_becomes_ast() {
    use vole_frontend::ast::CallExpr;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let callee = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Identifier(Symbol::UNKNOWN),
        span: dummy_span(),
    };
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Call(Box::new(CallExpr {
            callee,
            args: vec![],
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for Call (no args), got {other:?}"),
    }
}

#[test]
fn lower_expr_call_preserves_type() {
    use vole_frontend::ast::CallExpr;
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::I64);
    let callee = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Identifier(Symbol::UNKNOWN),
        span: dummy_span(),
    };
    let expr = Expr {
        id: node_id,
        kind: ExprKind::Call(Box::new(CallExpr {
            callee,
            args: vec![],
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    // The Ast escape hatch should carry the sema-computed type
    match vir_ref.as_ref() {
        VirExpr::Ast { ty, .. } => {
            assert_eq!(*ty, TypeId::I64);
        }
        other => panic!("expected Ast with type, got {other:?}"),
    }
}
