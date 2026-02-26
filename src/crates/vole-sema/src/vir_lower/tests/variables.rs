// lower/tests/variables.rs
//
// Tests for Identifier -> LocalLoad and Assign -> LocalStore lowering.

use super::*;
use crate::vir_lower::expr::lower_expr;
use vole_vir::expr::VirExpr;

// -----------------------------------------------------------------------
// Identifier -> LocalLoad
// -----------------------------------------------------------------------

#[test]
fn lower_identifier_becomes_local_load() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("x");
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Identifier(sym),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::LocalLoad { name, ty, .. } => {
            assert_eq!(*name, sym);
            assert_eq!(*ty, vir_type_id(TypeId::UNKNOWN));
        }
        other => panic!("expected LocalLoad, got {other:?}"),
    }
}

#[test]
fn lower_identifier_preserves_sema_type() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("count");
    let node_id = NodeId::new(ModuleId::new(0), 100);
    node_map.set_type(node_id, TypeId::I64);
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: node_id,
        kind: ExprKind::Identifier(sym),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::LocalLoad { name, ty, .. } => {
            assert_eq!(*name, sym);
            assert_eq!(*ty, vir_type_id(TypeId::I64));
        }
        other => panic!("expected LocalLoad with I64 type, got {other:?}"),
    }
}

#[test]
fn lower_identifier_bool_type() {
    let mut node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("flag");
    let node_id = NodeId::new(ModuleId::new(0), 101);
    node_map.set_type(node_id, TypeId::BOOL);
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: node_id,
        kind: ExprKind::Identifier(sym),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::LocalLoad { name, ty, .. } => {
            assert_eq!(*name, sym);
            assert_eq!(*ty, vir_type_id(TypeId::BOOL));
        }
        other => panic!("expected LocalLoad with BOOL type, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Assign with Variable target -> LocalStore
// -----------------------------------------------------------------------

#[test]
fn lower_assign_variable_becomes_local_store() {
    use vole_frontend::ast::{AssignExpr, AssignTarget};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("x");
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Assign(Box::new(AssignExpr {
            target: AssignTarget::Variable(sym),
            value: make_int_expr(99),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::LocalStore { name, value } => {
            assert_eq!(*name, sym);
            match value.as_ref() {
                VirExpr::IntLiteral { value: 99, .. } => {}
                other => panic!("expected IntLiteral(99), got {other:?}"),
            }
        }
        other => panic!("expected LocalStore, got {other:?}"),
    }
}

#[test]
fn lower_assign_variable_lowers_value_recursively() {
    use vole_frontend::ast::{AssignExpr, AssignTarget};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("y");
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Assign(Box::new(AssignExpr {
            target: AssignTarget::Variable(sym),
            value: Expr {
                id: dummy_node_id(),
                kind: ExprKind::BoolLiteral(true),
                span: dummy_span(),
            },
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::LocalStore { name, value } => {
            assert_eq!(*name, sym);
            match value.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral(true), got {other:?}"),
            }
        }
        other => panic!("expected LocalStore, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Assign with Discard target -> evaluates inner expression only
// -----------------------------------------------------------------------

#[test]
fn lower_assign_discard_evaluates_inner_expr() {
    use vole_frontend::ast::{AssignExpr, AssignTarget};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Assign(Box::new(AssignExpr {
            target: AssignTarget::Discard,
            value: make_int_expr(42),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    // Discard assign `_ = 42` lowers to just the inner expression `42`.
    match vir_ref.as_ref() {
        VirExpr::IntLiteral { value: 42, .. } => {}
        other => panic!("expected IntLiteral(42) for discard assign, got {other:?}"),
    }
}

#[test]
fn lower_assign_field_becomes_field_store() {
    use vole_frontend::ast::{AssignExpr, AssignTarget};
    use vole_vir::expr::FieldStorage;
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("field");
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Assign(Box::new(AssignExpr {
            target: AssignTarget::Field {
                object: Box::new(make_int_expr(0)),
                field: sym,
                field_span: dummy_span(),
            },
            value: make_int_expr(42),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::FieldStore {
            object,
            field,
            storage,
            value,
        } => {
            assert!(matches!(
                object.as_ref(),
                VirExpr::IntLiteral { value: 0, .. }
            ));
            assert_eq!(*field, sym);
            assert_eq!(*storage, FieldStorage::ByName);
            assert!(matches!(
                value.as_ref(),
                VirExpr::IntLiteral { value: 42, .. }
            ));
        }
        other => panic!("expected FieldStore for field assign, got {other:?}"),
    }
}

#[test]
fn lower_assign_index_becomes_index_store() {
    use vole_frontend::ast::{AssignExpr, AssignTarget};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );
    let expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Assign(Box::new(AssignExpr {
            target: AssignTarget::Index {
                object: Box::new(make_int_expr(0)),
                index: Box::new(make_int_expr(1)),
            },
            value: make_int_expr(42),
        })),
        span: dummy_span(),
    };
    let vir_ref = lower_expr(&expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::IndexStore {
            object,
            index,
            value,
            union_storage,
        } => {
            assert!(matches!(
                object.as_ref(),
                VirExpr::IntLiteral { value: 0, .. }
            ));
            assert!(matches!(
                index.as_ref(),
                VirExpr::IntLiteral { value: 1, .. }
            ));
            assert!(matches!(
                value.as_ref(),
                VirExpr::IntLiteral { value: 42, .. }
            ));
            assert!(union_storage.is_none());
        }
        other => panic!("expected IndexStore for index assign, got {other:?}"),
    }
}
