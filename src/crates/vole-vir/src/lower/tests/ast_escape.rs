// lower/tests/ast_escape.rs
//
// Tests for lowered simple expressions (Unreachable, Import, TypeLiteral, Range)
// and remaining AST escape hatches (Assign, RepeatLiteral, Call).
// Also tests compound assignment desugaring (variable targets lowered,
// index/field targets remain as Ast) and ArrayLiteral VIR lowering.

use super::*;
use crate::expr::VirExpr;
use crate::lower::expr::lower_expr;

// -----------------------------------------------------------------------
// Proper VIR lowering: Unreachable, Import, TypeLiteral, Range
// -----------------------------------------------------------------------

#[test]
fn lower_expr_unreachable() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Unreachable,
        span: Span {
            line: 42,
            ..dummy_span()
        },
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Unreachable { line: 42 } => {}
        other => panic!("expected Unreachable with line 42, got {other:?}"),
    }
}

#[test]
fn lower_expr_unreachable_preserves_line() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Unreachable,
        span: Span {
            line: 0,
            ..dummy_span()
        },
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Unreachable { line: 0 } => {}
        other => panic!("expected Unreachable with line 0, got {other:?}"),
    }
}

#[test]
fn lower_expr_import() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Import("std:math".to_string()),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Import { ty } => {
            assert_eq!(*ty, TypeId::UNKNOWN);
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

#[test]
fn lower_expr_import_with_type() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, dummy_type_id());
    let expr = Expr {
        id: node_id,
        kind: ExprKind::Import("std:io".to_string()),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Import { ty } => {
            assert_eq!(*ty, dummy_type_id());
        }
        other => panic!("expected Import with type, got {other:?}"),
    }
}

#[test]
fn lower_expr_type_literal() {
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
        VirExpr::TypeLiteral => {}
        other => panic!("expected TypeLiteral, got {other:?}"),
    }
}

#[test]
fn lower_expr_range_exclusive() {
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
        VirExpr::Range {
            start,
            end,
            inclusive: false,
        } => {
            // Start should be IntLiteral(0)
            match start.as_ref() {
                VirExpr::IntLiteral { value: 0, .. } => {}
                other => panic!("expected start IntLiteral(0), got {other:?}"),
            }
            // End should be IntLiteral(10)
            match end.as_ref() {
                VirExpr::IntLiteral { value: 10, .. } => {}
                other => panic!("expected end IntLiteral(10), got {other:?}"),
            }
        }
        other => panic!("expected Range (exclusive), got {other:?}"),
    }
}

#[test]
fn lower_expr_range_inclusive() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Range(Box::new(vole_frontend::ast::RangeExpr {
            start: make_int_expr(1),
            end: make_int_expr(5),
            inclusive: true,
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Range {
            start,
            end,
            inclusive: true,
        } => {
            match start.as_ref() {
                VirExpr::IntLiteral { value: 1, .. } => {}
                other => panic!("expected start IntLiteral(1), got {other:?}"),
            }
            match end.as_ref() {
                VirExpr::IntLiteral { value: 5, .. } => {}
                other => panic!("expected end IntLiteral(5), got {other:?}"),
            }
        }
        other => panic!("expected Range (inclusive), got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Ast escape hatch lowering: Assign, CompoundAssign, RepeatLiteral
// and proper VIR lowering: ArrayLiteral (vol-aq9j, vol-w4mg, vol-pc2m)
// -----------------------------------------------------------------------

#[test]
fn lower_expr_assign_variable_becomes_local_store() {
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
        VirExpr::LocalStore { name, value } => {
            assert_eq!(*name, Symbol::UNKNOWN);
            match value.as_ref() {
                VirExpr::IntLiteral { value: 42, .. } => {}
                other => panic!("expected IntLiteral(42) as store value, got {other:?}"),
            }
        }
        other => panic!("expected LocalStore for variable Assign, got {other:?}"),
    }
}

#[test]
fn lower_expr_compound_assign_variable_desugars_to_store() {
    use crate::expr::VirBinOp;
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
        VirExpr::LocalStore { name, value } => {
            assert_eq!(*name, Symbol::UNKNOWN);
            match value.as_ref() {
                VirExpr::BinaryOp { op, lhs, rhs, .. } => {
                    assert_eq!(*op, VirBinOp::Add);
                    assert!(
                        matches!(lhs.as_ref(), VirExpr::LocalLoad { name, .. } if *name == Symbol::UNKNOWN)
                    );
                    assert!(matches!(rhs.as_ref(), VirExpr::IntLiteral { value: 1, .. }));
                }
                other => panic!("expected BinaryOp, got {other:?}"),
            }
        }
        other => panic!("expected LocalStore for variable CompoundAssign, got {other:?}"),
    }
}

#[test]
fn lower_expr_compound_assign_index_becomes_ast() {
    use vole_frontend::ast::{AssignTarget, CompoundAssignExpr, CompoundOp};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::CompoundAssign(Box::new(CompoundAssignExpr {
            target: AssignTarget::Index {
                object: Box::new(make_int_expr(0)),
                index: Box::new(make_int_expr(0)),
            },
            op: CompoundOp::Add,
            value: make_int_expr(1),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::Ast { .. } => {}
        other => panic!("expected Ast escape hatch for index CompoundAssign, got {other:?}"),
    }
}

#[test]
fn lower_expr_array_literal_becomes_vir() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::ArrayLiteral(vec![make_int_expr(1), make_int_expr(2), make_int_expr(3)]),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &node_map, &mut interner);

    match vir_ref.as_ref() {
        VirExpr::ArrayLiteral { elements, ty } => {
            assert_eq!(elements.len(), 3);
            assert_eq!(*ty, TypeId::UNKNOWN);
        }
        other => panic!("expected ArrayLiteral, got {other:?}"),
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
