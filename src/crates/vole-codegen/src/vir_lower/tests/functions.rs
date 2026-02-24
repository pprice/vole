// lower/tests/functions.rs
//
// Tests for function-level lowering: lower_function, lower_monomorphized_function,
// lower_method, lower_stmts.

use super::*;
use crate::vir_lower::{lower_function, lower_monomorphized_function, lower_stmts};
use vole_sema::TypeArena;
use vole_vir::expr::VirExpr;
use vole_vir::stmt::VirStmt;

#[test]
fn lower_empty_block_function() {
    let func = make_block_func(vec![]);
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let ret_ty = dummy_type_id();

    let vir = lower_function(
        &func,
        dummy_func_id(),
        "test_fn".into(),
        &[],
        ret_ty,
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );

    assert_eq!(vir.id, dummy_func_id());
    assert_eq!(vir.return_type, ret_ty);
    assert!(vir.params.is_empty());
    assert!(vir.body.stmts.is_empty());
    assert!(vir.body.trailing.is_none());
}

#[test]
fn lower_block_function_lowers_control_flow() {
    let func = make_block_func(vec![make_break_stmt(), make_continue_stmt()]);
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let ret_ty = dummy_type_id();

    let vir = lower_function(
        &func,
        dummy_func_id(),
        "test_fn".into(),
        &[],
        ret_ty,
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );

    assert_eq!(vir.body.stmts.len(), 2);
    assert!(vir.body.trailing.is_none());

    match &vir.body.stmts[0] {
        VirStmt::Break => {}
        other => panic!("expected VirStmt::Break, got {other:?}"),
    }
    match &vir.body.stmts[1] {
        VirStmt::Continue => {}
        other => panic!("expected VirStmt::Continue, got {other:?}"),
    }
}

#[test]
fn lower_expr_body_function_sets_trailing() {
    let func = make_expr_func(make_bool_expr());
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let ret_ty = dummy_type_id();

    let vir = lower_function(
        &func,
        dummy_func_id(),
        "test_fn".into(),
        &[],
        ret_ty,
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );

    assert!(vir.body.stmts.is_empty());
    assert!(vir.body.trailing.is_some());

    // BoolLiteral is now lowered to VirExpr::BoolLiteral
    match vir.body.trailing.as_deref() {
        Some(VirExpr::BoolLiteral(true)) => {}
        other => panic!("expected VirExpr::BoolLiteral(true) trailing, got {other:?}"),
    }
}

#[test]
fn lower_preserves_params_and_return_type() {
    let func = make_block_func(vec![]);
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
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
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );

    assert_eq!(vir.params.len(), 2);
    assert_eq!(vir.params[0].1, param_a);
    assert_eq!(vir.params[1].1, param_b);
    assert_eq!(vir.return_type, ret_ty);
}

#[test]
fn lower_stmts_preserves_order() {
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
    let stmts = vec![make_break_stmt(), make_continue_stmt(), make_break_stmt()];
    let body = lower_stmts(&stmts, &mut ctx);

    assert_eq!(body.stmts.len(), 3);
    assert!(body.trailing.is_none());

    // Break and Continue are now properly lowered to VIR
    match &body.stmts[0] {
        VirStmt::Break => {}
        other => panic!("expected Break, got {other:?}"),
    }
    match &body.stmts[1] {
        VirStmt::Continue => {}
        other => panic!("expected Continue, got {other:?}"),
    }
    match &body.stmts[2] {
        VirStmt::Break => {}
        other => panic!("expected Break, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Monomorphized function lowering
// -----------------------------------------------------------------------

#[test]
fn lower_monomorphized_with_concrete_types() {
    let arena = TypeArena::new();
    let entities = test_entities();
    let name_table = test_name_table();
    let func = make_block_func(vec![make_break_stmt()]);
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let i64_ty = arena.i64();
    let string_ty = arena.string();
    let params = vec![(Symbol::UNKNOWN, i64_ty)];

    let vir = lower_monomorphized_function(
        &func,
        dummy_func_id(),
        "identity__mono_0".into(),
        &params,
        string_ty,
        &node_map,
        &arena,
        dummy_name_id(),
        &mut interner,
        &entities,
        &name_table,
    );

    assert_eq!(vir.name, "identity__mono_0");
    assert_eq!(vir.params.len(), 1);
    assert_eq!(vir.params[0].1, i64_ty);
    assert_eq!(vir.return_type, string_ty);
    assert_eq!(vir.body.stmts.len(), 1);
}

#[test]
fn lower_monomorphized_expr_body() {
    let arena = TypeArena::new();
    let entities = test_entities();
    let name_table = test_name_table();
    let func = make_expr_func(make_bool_expr());
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let bool_ty = arena.bool();

    let vir = lower_monomorphized_function(
        &func,
        dummy_func_id(),
        "to_bool__mono_0".into(),
        &[],
        bool_ty,
        &node_map,
        &arena,
        dummy_name_id(),
        &mut interner,
        &entities,
        &name_table,
    );

    assert_eq!(vir.name, "to_bool__mono_0");
    assert!(vir.body.stmts.is_empty());
    assert!(vir.body.trailing.is_some());
    assert_eq!(vir.return_type, bool_ty);
}

#[test]
#[should_panic(expected = "param 0 still contains a type parameter")]
fn lower_monomorphized_rejects_type_param_in_params() {
    let mut arena = TypeArena::new();
    let entities = test_entities();
    let name_table = test_name_table();
    let func = make_block_func(vec![]);
    let node_map = empty_node_map();
    let mut interner = test_interner();
    // Create a type parameter — this should trigger the assertion
    let mut names = NameTable::new();
    let t_name_id = names.intern_raw(names.main_module(), &["T"]);
    let type_param = arena.type_param(t_name_id);
    let params = vec![(Symbol::UNKNOWN, type_param)];

    let _ = lower_monomorphized_function(
        &func,
        dummy_func_id(),
        "bad__mono_0".into(),
        &params,
        arena.i64(),
        &node_map,
        &arena,
        dummy_name_id(),
        &mut interner,
        &entities,
        &name_table,
    );
}

#[test]
#[should_panic(expected = "return type still contains a type parameter")]
fn lower_monomorphized_rejects_type_param_in_return() {
    let mut arena = TypeArena::new();
    let entities = test_entities();
    let name_table = test_name_table();
    let func = make_block_func(vec![]);
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let mut names = NameTable::new();
    let t_name_id = names.intern_raw(names.main_module(), &["T"]);
    let type_param = arena.type_param(t_name_id);

    let _ = lower_monomorphized_function(
        &func,
        dummy_func_id(),
        "bad__mono_0".into(),
        &[],
        type_param,
        &node_map,
        &arena,
        dummy_name_id(),
        &mut interner,
        &entities,
        &name_table,
    );
}

// -----------------------------------------------------------------------
// Statement lowering
// -----------------------------------------------------------------------

#[test]
fn lower_stmt_expr_produces_vir_expr() {
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
    use vole_frontend::ast::ExprStmt;
    let stmt = Stmt::Expr(ExprStmt {
        expr: make_bool_expr(),
        span: dummy_span(),
    });
    let vir_stmt = crate::vir_lower::stmt::lower_stmt(&stmt, &mut ctx);

    match &vir_stmt {
        VirStmt::Expr { value } => match value.as_ref() {
            VirExpr::BoolLiteral(true) => {}
            other => panic!("expected BoolLiteral in Expr stmt, got {other:?}"),
        },
        other => panic!("expected VirStmt::Expr, got {other:?}"),
    }
}

#[test]
fn lower_stmt_let_becomes_vir_let() {
    use vole_frontend::ast::{LetInit, LetStmt};
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
    // Let with Expr init is now lowered to VirStmt::Let
    let stmt = Stmt::Let(LetStmt {
        name: Symbol::UNKNOWN,
        ty: None,
        mutable: false,
        init: LetInit::Expr(make_int_expr(42)),
        span: dummy_span(),
    });
    let vir_stmt = crate::vir_lower::stmt::lower_stmt(&stmt, &mut ctx);

    match &vir_stmt {
        VirStmt::Let {
            name,
            mutable,
            value,
            ..
        } => {
            assert_eq!(*name, Symbol::UNKNOWN);
            assert!(!mutable);
            match value.as_ref() {
                VirExpr::IntLiteral { value, .. } => assert_eq!(*value, 42),
                other => panic!("expected IntLiteral in Let init, got {other:?}"),
            }
        }
        other => panic!("expected VirStmt::Let, got {other:?}"),
    }
}

#[test]
fn lower_stmt_let_type_alias_becomes_noop() {
    use vole_frontend::ast::{LetInit, LetStmt, TypeExpr, TypeExprKind};
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let sym = interner.intern("Foo");
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
    );
    // Let with TypeAlias init is a compile-time construct: lowers to Noop
    let stmt = Stmt::Let(LetStmt {
        name: Symbol::UNKNOWN,
        ty: None,
        mutable: false,
        init: LetInit::TypeAlias(TypeExpr {
            kind: TypeExprKind::Named(sym),
            span: dummy_span(),
        }),
        span: dummy_span(),
    });
    let vir_stmt = crate::vir_lower::stmt::lower_stmt(&stmt, &mut ctx);

    match &vir_stmt {
        VirStmt::Noop => {}
        other => panic!("expected VirStmt::Noop for TypeAlias, got {other:?}"),
    }
}
