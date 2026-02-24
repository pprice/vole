// lower/tests/control_flow.rs
//
// Tests for control flow lowering: If, Block, Yield expressions,
// and While, If, Break, Continue, Return statements.

use super::*;
use crate::vir_lower::expr::lower_expr;
use crate::vir_lower::stmt::lower_stmt;
use vole_vir::expr::VirExpr;
use vole_vir::stmt::VirStmt;

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = make_if_expr(make_bool_expr(), make_int_expr(1), Some(make_int_expr(2)));
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = make_if_expr(make_bool_expr(), make_int_expr(42), None);
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let expr = make_if_expr(make_bool_expr(), make_int_expr(1), Some(make_int_expr(2)));
    node_map.set_type(expr.id, TypeId::I64);
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::If { ty, .. } => assert_eq!(*ty, TypeId::I64),
        other => panic!("expected VirExpr::If, got {other:?}"),
    }
}

#[test]
fn lower_if_expr_recursive_lowering() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
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
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![],
            trailing_expr: None,
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![],
            trailing_expr: Some(make_int_expr(99)),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![make_break_stmt()],
            trailing_expr: Some(make_bool_expr()),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            assert_eq!(stmts.len(), 1);
            match &stmts[0] {
                VirStmt::Break => {}
                other => panic!("expected VirStmt::Break, got {other:?}"),
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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let node_id = dummy_node_id();
    node_map.set_type(node_id, TypeId::I64);
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = Expr {
        id: node_id,
        kind: ExprKind::Block(Box::new(vole_frontend::ast::BlockExpr {
            stmts: vec![],
            trailing_expr: Some(make_int_expr(42)),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Yield(Box::new(YieldExpr {
            value: make_int_expr(42),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

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
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    // yield true -- the inner bool should be lowered to VirExpr::BoolLiteral
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Yield(Box::new(YieldExpr {
            value: make_bool_expr(),
            span: dummy_span(),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::Yield { value } => match value.as_ref() {
            VirExpr::BoolLiteral(true) => {}
            other => panic!("expected BoolLiteral(true) inside Yield, got {other:?}"),
        },
        other => panic!("expected VirExpr::Yield, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Statement lowering: Break, Continue
// -----------------------------------------------------------------------

#[test]
fn lower_break_stmt() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_break_stmt();
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Break => {}
        other => panic!("expected VirStmt::Break, got {other:?}"),
    }
}

#[test]
fn lower_continue_stmt() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_continue_stmt();
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Continue => {}
        other => panic!("expected VirStmt::Continue, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Statement lowering: Return
// -----------------------------------------------------------------------

#[test]
fn lower_return_with_value() {
    use vole_frontend::ast::ReturnStmt;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = Stmt::Return(ReturnStmt {
        value: Some(make_int_expr(42)),
        span: dummy_span(),
    });
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Return { value: Some(v) } => match v.as_ref() {
            VirExpr::IntLiteral { value: 42, .. } => {}
            other => panic!("expected IntLiteral(42) as return value, got {other:?}"),
        },
        other => panic!("expected VirStmt::Return with value, got {other:?}"),
    }
}

#[test]
fn lower_return_void() {
    use vole_frontend::ast::ReturnStmt;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = Stmt::Return(ReturnStmt {
        value: None,
        span: dummy_span(),
    });
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Return { value: None } => {}
        other => panic!("expected VirStmt::Return with no value, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Statement lowering: While
// -----------------------------------------------------------------------

fn make_while_stmt(condition: Expr, body_stmts: Vec<Stmt>) -> Stmt {
    use vole_frontend::ast::WhileStmt;
    Stmt::While(WhileStmt {
        condition,
        body: Block {
            stmts: body_stmts,
            span: dummy_span(),
        },
        span: dummy_span(),
    })
}

#[test]
fn lower_while_empty_body() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_while_stmt(make_bool_expr(), vec![]);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::While { cond, body } => {
            match cond.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true) condition, got {other:?}"),
            }
            assert!(body.stmts.is_empty());
            assert!(body.trailing.is_none());
        }
        other => panic!("expected VirStmt::While, got {other:?}"),
    }
}

#[test]
fn lower_while_with_body() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_while_stmt(make_bool_expr(), vec![make_break_stmt()]);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::While { body, .. } => {
            assert_eq!(body.stmts.len(), 1);
            match &body.stmts[0] {
                VirStmt::Break => {}
                other => panic!("expected VirStmt::Break in body, got {other:?}"),
            }
        }
        other => panic!("expected VirStmt::While, got {other:?}"),
    }
}

#[test]
fn lower_while_lowers_condition_recursively() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_while_stmt(make_int_expr(1), vec![]);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::While { cond, .. } => match cond.as_ref() {
            VirExpr::IntLiteral { value: 1, .. } => {}
            other => panic!("expected IntLiteral(1) condition, got {other:?}"),
        },
        other => panic!("expected VirStmt::While, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Statement lowering: If (as statement)
// -----------------------------------------------------------------------

fn make_if_stmt(condition: Expr, then_stmts: Vec<Stmt>, else_stmts: Option<Vec<Stmt>>) -> Stmt {
    use vole_frontend::ast::IfStmt;
    Stmt::If(IfStmt {
        condition,
        then_branch: Block {
            stmts: then_stmts,
            span: dummy_span(),
        },
        else_branch: else_stmts.map(|stmts| Block {
            stmts,
            span: dummy_span(),
        }),
        span: dummy_span(),
    })
}

#[test]
fn lower_if_stmt_no_else() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_if_stmt(make_bool_expr(), vec![make_break_stmt()], None);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Expr { value } => match value.as_ref() {
            VirExpr::If {
                cond,
                then_body,
                else_body,
                ty,
                ..
            } => {
                match cond.as_ref() {
                    VirExpr::BoolLiteral(true) => {}
                    other => panic!("expected BoolLiteral(true) cond, got {other:?}"),
                }
                assert_eq!(then_body.stmts.len(), 1);
                match &then_body.stmts[0] {
                    VirStmt::Break => {}
                    other => panic!("expected VirStmt::Break, got {other:?}"),
                }
                assert!(then_body.trailing.is_none());
                assert!(else_body.is_none());
                assert_eq!(*ty, TypeId::VOID);
            }
            other => panic!("expected VirExpr::If, got {other:?}"),
        },
        other => panic!("expected VirStmt::Expr, got {other:?}"),
    }
}

#[test]
fn lower_if_stmt_with_else() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_if_stmt(
        make_bool_expr(),
        vec![make_break_stmt()],
        Some(vec![make_continue_stmt()]),
    );
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Expr { value } => match value.as_ref() {
            VirExpr::If {
                then_body,
                else_body,
                ty,
                ..
            } => {
                assert_eq!(then_body.stmts.len(), 1);
                match &then_body.stmts[0] {
                    VirStmt::Break => {}
                    other => panic!("expected VirStmt::Break in then, got {other:?}"),
                }
                let else_body = else_body.as_ref().expect("should have else body");
                assert_eq!(else_body.stmts.len(), 1);
                match &else_body.stmts[0] {
                    VirStmt::Continue => {}
                    other => panic!("expected VirStmt::Continue in else, got {other:?}"),
                }
                assert!(else_body.trailing.is_none());
                assert_eq!(*ty, TypeId::VOID);
            }
            other => panic!("expected VirExpr::If, got {other:?}"),
        },
        other => panic!("expected VirStmt::Expr, got {other:?}"),
    }
}

#[test]
fn lower_if_stmt_is_void_typed() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_if_stmt(make_bool_expr(), vec![], None);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Expr { value } => match value.as_ref() {
            VirExpr::If { ty, .. } => assert_eq!(*ty, TypeId::VOID),
            other => panic!("expected VirExpr::If, got {other:?}"),
        },
        other => panic!("expected VirStmt::Expr, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Statement lowering: Raise
// -----------------------------------------------------------------------

fn make_raise_stmt(error_name: Symbol, fields: Vec<(Symbol, Expr)>) -> Stmt {
    use vole_frontend::ast::{RaiseStmt, StructFieldInit};
    Stmt::Raise(RaiseStmt {
        error_name,
        fields: fields
            .into_iter()
            .map(|(name, value)| StructFieldInit {
                name,
                value,
                span: dummy_span(),
                shorthand: false,
            })
            .collect(),
        span: dummy_span(),
    })
}

#[test]
fn lower_raise_no_fields() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let error_sym = interner.intern("NotFound");
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_raise_stmt(error_sym, vec![]);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Raise {
            error_name, fields, ..
        } => {
            assert_eq!(*error_name, error_sym);
            assert!(fields.is_empty());
        }
        other => panic!("expected VirStmt::Raise, got {other:?}"),
    }
}

#[test]
fn lower_raise_single_field() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let error_sym = interner.intern("ParseError");
    let msg_sym = interner.intern("message");
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_raise_stmt(error_sym, vec![(msg_sym, make_int_expr(42))]);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Raise {
            error_name, fields, ..
        } => {
            assert_eq!(*error_name, error_sym);
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, msg_sym);
            match fields[0].1.as_ref() {
                VirExpr::IntLiteral { value: 42, .. } => {}
                other => panic!("expected IntLiteral(42) field value, got {other:?}"),
            }
        }
        other => panic!("expected VirStmt::Raise, got {other:?}"),
    }
}

#[test]
fn lower_raise_multiple_fields() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let error_sym = interner.intern("IoError");
    let code_sym = interner.intern("code");
    let retry_sym = interner.intern("retry");
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let stmt = make_raise_stmt(
        error_sym,
        vec![
            (code_sym, make_int_expr(404)),
            (retry_sym, make_bool_expr()),
        ],
    );
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Raise {
            error_name, fields, ..
        } => {
            assert_eq!(*error_name, error_sym);
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, code_sym);
            match fields[0].1.as_ref() {
                VirExpr::IntLiteral { value: 404, .. } => {}
                other => panic!("expected IntLiteral(404), got {other:?}"),
            }
            assert_eq!(fields[1].0, retry_sym);
            match fields[1].1.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true), got {other:?}"),
            }
        }
        other => panic!("expected VirStmt::Raise, got {other:?}"),
    }
}

#[test]
fn lower_raise_field_values_lowered_recursively() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let error_sym = interner.intern("Err");
    let val_sym = interner.intern("val");
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    // Field value is a bool literal — should be lowered to VirExpr::BoolLiteral
    let stmt = make_raise_stmt(error_sym, vec![(val_sym, make_bool_expr())]);
    let vir = lower_stmt(&stmt, &mut ctx);

    match &vir {
        VirStmt::Raise { fields, .. } => {
            assert_eq!(fields.len(), 1);
            // Bool literal should be lowered to VirExpr::BoolLiteral, not Ast
            match fields[0].1.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true), got {other:?}"),
            }
        }
        other => panic!("expected VirStmt::Raise, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Pattern lowering: Tuple (vol-oapf)
// -----------------------------------------------------------------------

fn make_match_arm(pattern: vole_frontend::Pattern, body: Expr) -> vole_frontend::ast::MatchArm {
    vole_frontend::ast::MatchArm {
        id: dummy_node_id(),
        pattern,
        guard: None,
        body,
        span: dummy_span(),
    }
}

fn make_tuple_pattern(elements: Vec<vole_frontend::Pattern>) -> vole_frontend::Pattern {
    vole_frontend::Pattern {
        id: dummy_node_id(),
        kind: vole_frontend::PatternKind::Tuple { elements },
        span: dummy_span(),
    }
}

fn make_binding_pattern(name: Symbol) -> vole_frontend::Pattern {
    vole_frontend::Pattern {
        id: dummy_node_id(),
        kind: vole_frontend::PatternKind::Identifier { name },
        span: dummy_span(),
    }
}

fn make_wildcard_pattern() -> vole_frontend::Pattern {
    vole_frontend::Pattern {
        id: dummy_node_id(),
        kind: vole_frontend::PatternKind::Wildcard,
        span: dummy_span(),
    }
}

#[test]
fn lower_tuple_pattern_with_bindings() {
    use vole_vir::expr::VirPattern;
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let mut type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();

    let x_sym = interner.intern("x");
    let y_sym = interner.intern("y");

    // Create a tuple type [i64, bool] in the arena.
    let tuple_ty = type_arena.tuple(vec![TypeId::I64, TypeId::BOOL]);

    // Set up scrutinee with a known type.
    let scrutinee_id = NodeId::new(ModuleId::new(0), 100);
    node_map.set_type(scrutinee_id, tuple_ty);

    let scrutinee_expr = Expr {
        id: scrutinee_id,
        kind: ExprKind::Identifier(interner.intern("t")),
        span: dummy_span(),
    };

    let tuple_pat = make_tuple_pattern(vec![
        make_binding_pattern(x_sym),
        make_binding_pattern(y_sym),
    ]);

    let arm = make_match_arm(tuple_pat, make_int_expr(42));
    let match_node_id = NodeId::new(ModuleId::new(0), 200);
    let match_expr = Expr {
        id: match_node_id,
        kind: ExprKind::Match(Box::new(vole_frontend::ast::MatchExpr {
            scrutinee: scrutinee_expr,
            arms: vec![arm],
            span: dummy_span(),
        })),
        span: dummy_span(),
    };

    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let vir_ref = lower_expr(&match_expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::Match { arms, .. } => {
            assert_eq!(arms.len(), 1);
            match &arms[0].pattern {
                VirPattern::Tuple { bindings } => {
                    assert_eq!(bindings.len(), 2);

                    assert_eq!(bindings[0].element_index, 0);
                    assert_eq!(bindings[0].ty, TypeId::I64);
                    match &bindings[0].pattern {
                        VirPattern::Binding { name, ty, .. } => {
                            assert_eq!(*name, x_sym);
                            assert_eq!(*ty, TypeId::I64);
                        }
                        other => panic!("expected Binding for x, got {other:?}"),
                    }

                    assert_eq!(bindings[1].element_index, 1);
                    assert_eq!(bindings[1].ty, TypeId::BOOL);
                    match &bindings[1].pattern {
                        VirPattern::Binding { name, ty, .. } => {
                            assert_eq!(*name, y_sym);
                            assert_eq!(*ty, TypeId::BOOL);
                        }
                        other => panic!("expected Binding for y, got {other:?}"),
                    }
                }
                other => panic!("expected VirPattern::Tuple, got {other:?}"),
            }
        }
        other => panic!("expected VirExpr::Match, got {other:?}"),
    }
}

#[test]
fn lower_tuple_pattern_with_wildcard() {
    use vole_vir::expr::VirPattern;
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let mut type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();

    let x_sym = interner.intern("x");

    // Create a tuple type [i64, string] in the arena.
    let tuple_ty = type_arena.tuple(vec![TypeId::I64, TypeId::STRING]);

    let scrutinee_id = NodeId::new(ModuleId::new(0), 100);
    node_map.set_type(scrutinee_id, tuple_ty);

    let scrutinee_expr = Expr {
        id: scrutinee_id,
        kind: ExprKind::Identifier(interner.intern("t")),
        span: dummy_span(),
    };

    // Pattern: [x, _]
    let tuple_pat = make_tuple_pattern(vec![make_binding_pattern(x_sym), make_wildcard_pattern()]);

    let arm = make_match_arm(tuple_pat, make_int_expr(1));
    let match_expr = Expr {
        id: NodeId::new(ModuleId::new(0), 200),
        kind: ExprKind::Match(Box::new(vole_frontend::ast::MatchExpr {
            scrutinee: scrutinee_expr,
            arms: vec![arm],
            span: dummy_span(),
        })),
        span: dummy_span(),
    };

    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let vir_ref = lower_expr(&match_expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::Match { arms, .. } => {
            assert_eq!(arms.len(), 1);
            match &arms[0].pattern {
                VirPattern::Tuple { bindings } => {
                    assert_eq!(bindings.len(), 2);

                    // First element: Binding
                    assert_eq!(bindings[0].element_index, 0);
                    assert_eq!(bindings[0].ty, TypeId::I64);
                    assert!(matches!(&bindings[0].pattern, VirPattern::Binding { .. }));

                    // Second element: Wildcard
                    assert_eq!(bindings[1].element_index, 1);
                    assert_eq!(bindings[1].ty, TypeId::STRING);
                    assert!(matches!(&bindings[1].pattern, VirPattern::Wildcard));
                }
                other => panic!("expected VirPattern::Tuple, got {other:?}"),
            }
        }
        other => panic!("expected VirExpr::Match, got {other:?}"),
    }
}

#[test]
fn lower_tuple_pattern_unknown_scrutinee_type() {
    use vole_vir::expr::VirPattern;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();

    let x_sym = interner.intern("x");

    // No type set for scrutinee — element types should fall back to UNKNOWN.
    let scrutinee_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Identifier(interner.intern("t")),
        span: dummy_span(),
    };

    let tuple_pat = make_tuple_pattern(vec![make_binding_pattern(x_sym)]);

    let arm = make_match_arm(tuple_pat, make_int_expr(1));
    let match_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Match(Box::new(vole_frontend::ast::MatchExpr {
            scrutinee: scrutinee_expr,
            arms: vec![arm],
            span: dummy_span(),
        })),
        span: dummy_span(),
    };

    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    let vir_ref = lower_expr(&match_expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::Match { arms, .. } => {
            assert_eq!(arms.len(), 1);
            match &arms[0].pattern {
                VirPattern::Tuple { bindings } => {
                    assert_eq!(bindings.len(), 1);
                    assert_eq!(bindings[0].element_index, 0);
                    assert_eq!(bindings[0].ty, TypeId::UNKNOWN);
                    match &bindings[0].pattern {
                        VirPattern::Binding { ty, .. } => {
                            assert_eq!(*ty, TypeId::UNKNOWN);
                        }
                        other => panic!("expected Binding, got {other:?}"),
                    }
                }
                other => panic!("expected VirPattern::Tuple, got {other:?}"),
            }
        }
        other => panic!("expected VirExpr::Match, got {other:?}"),
    }
}
