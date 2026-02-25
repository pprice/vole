// lower/tests/generic_mode.rs
//
// Tests for the generic (tolerant) lowering mode.
//
// Verifies that:
// - Generic mode doesn't panic on missing sema decisions.
// - Concrete mode still panics on missing decisions.
// - Placeholder variants are correctly emitted.

use super::*;
use crate::analysis_cache::IsCheckResult as SemaIsCheckResult;
use crate::generic::MonomorphKey;
use crate::types::FunctionType;
use crate::vir_lower::expr::lower_expr;
use crate::vir_lower::stmt::lower_stmt;
use vole_frontend::ast::{
    AsCastExpr, AsCastKind, CallArg, CallExpr, ExprKind, ForStmt, IsExpr, Stmt, StringPart,
    TypeExpr, TypeExprKind,
};
use vole_identity::StringConversion;
use vole_vir::calls::CallTarget;
use vole_vir::expr::{IsCheckResult, VirExpr, VirStringPart};
use vole_vir::stmt::{VirIterKind, VirStmt};

// -----------------------------------------------------------------------
// is_check_result — generic mode placeholder
// -----------------------------------------------------------------------

#[test]
fn generic_mode_is_check_missing_uses_check_unknown() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let inner_expr = make_int_expr(42);
    let is_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Is(Box::new(IsExpr {
            value: inner_expr,
            type_expr: TypeExpr {
                kind: TypeExprKind::Named(Symbol::UNKNOWN),
                span: dummy_span(),
            },
            type_span: dummy_span(),
        })),
        span: dummy_span(),
    };

    // Should NOT panic in generic mode despite missing is_check_result
    let vir_ref = lower_expr(&is_expr, &mut ctx);

    match vir_ref.as_ref() {
        VirExpr::IsCheck { result, .. } => {
            assert_eq!(
                *result,
                IsCheckResult::CheckUnknown(TypeId::UNKNOWN, vole_identity::VirTypeId::UNKNOWN)
            );
        }
        other => panic!("expected IsCheck, got {other:?}"),
    }
}

#[test]
#[should_panic(expected = "missing sema is_check_result")]
fn concrete_mode_is_check_missing_panics() {
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

    let inner_expr = make_int_expr(42);
    let is_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::Is(Box::new(IsExpr {
            value: inner_expr,
            type_expr: TypeExpr {
                kind: TypeExprKind::Named(Symbol::UNKNOWN),
                span: dummy_span(),
            },
            type_span: dummy_span(),
        })),
        span: dummy_span(),
    };

    // Should panic in concrete mode
    let _ = lower_expr(&is_expr, &mut ctx);
}

// -----------------------------------------------------------------------
// is_check_result — concrete mode still works with data present
// -----------------------------------------------------------------------

#[test]
fn concrete_mode_is_check_with_data_works() {
    let mut node_map = empty_node_map();
    let node = dummy_node_id();
    node_map.set_is_check_result(node, SemaIsCheckResult::AlwaysTrue);

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

    let inner_expr = make_int_expr(42);
    let is_expr = Expr {
        id: node,
        kind: ExprKind::Is(Box::new(IsExpr {
            value: inner_expr,
            type_expr: TypeExpr {
                kind: TypeExprKind::Named(Symbol::UNKNOWN),
                span: dummy_span(),
            },
            type_span: dummy_span(),
        })),
        span: dummy_span(),
    };

    let vir_ref = lower_expr(&is_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::IsCheck { result, .. } => {
            assert_eq!(*result, IsCheckResult::AlwaysTrue);
        }
        other => panic!("expected IsCheck, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// as_cast — generic mode placeholder
// -----------------------------------------------------------------------

#[test]
fn generic_mode_as_cast_missing_uses_check_unknown() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let inner_expr = make_int_expr(42);
    let as_cast_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::AsCast(Box::new(AsCastExpr {
            value: inner_expr,
            kind: AsCastKind::Safe,
            type_expr: TypeExpr {
                kind: TypeExprKind::Named(Symbol::UNKNOWN),
                span: dummy_span(),
            },
            type_span: dummy_span(),
        })),
        span: dummy_span(),
    };

    // Should NOT panic in generic mode
    let vir_ref = lower_expr(&as_cast_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::AsCast { result, .. } => {
            assert_eq!(
                *result,
                IsCheckResult::CheckUnknown(TypeId::UNKNOWN, vole_identity::VirTypeId::UNKNOWN)
            );
        }
        other => panic!("expected AsCast, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// interpolated string — generic mode StringConversion::Generic
// -----------------------------------------------------------------------

#[test]
fn generic_mode_interpolated_string_uses_generic_conversion() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let parts = vec![
        StringPart::Literal("x = ".to_string()),
        StringPart::Expr(Box::new(make_int_expr(42))),
    ];
    let interp_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::InterpolatedString(parts),
        span: dummy_span(),
    };

    let vir_ref = lower_expr(&interp_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::InterpolatedString { parts } => {
            assert_eq!(parts.len(), 2);
            match &parts[1] {
                VirStringPart::Expr { conversion, .. } => {
                    assert!(
                        matches!(conversion, StringConversion::Generic { .. }),
                        "expected Generic conversion in generic mode, got {conversion:?}"
                    );
                }
                other => panic!("expected Expr part, got {other:?}"),
            }
        }
        other => panic!("expected InterpolatedString, got {other:?}"),
    }
}

#[test]
fn concrete_mode_interpolated_string_uses_identity_fallback() {
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

    let parts = vec![
        StringPart::Literal("x = ".to_string()),
        StringPart::Expr(Box::new(make_int_expr(42))),
    ];
    let interp_expr = Expr {
        id: dummy_node_id(),
        kind: ExprKind::InterpolatedString(parts),
        span: dummy_span(),
    };

    let vir_ref = lower_expr(&interp_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::InterpolatedString { parts } => {
            assert_eq!(parts.len(), 2);
            match &parts[1] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(
                        *conversion,
                        StringConversion::Identity,
                        "expected Identity in concrete mode, got {conversion:?}"
                    );
                }
                other => panic!("expected Expr part, got {other:?}"),
            }
        }
        other => panic!("expected InterpolatedString, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// for loop — generic mode iterable kind placeholder
// -----------------------------------------------------------------------

#[test]
fn generic_mode_for_loop_missing_iterable_kind_uses_generic() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let for_stmt = ForStmt {
        var_name: Symbol::UNKNOWN,
        iterable: make_int_expr(0), // Dummy iterable
        body: Block {
            stmts: vec![],
            span: dummy_span(),
        },
        span: dummy_span(),
    };

    let vir_stmt = lower_stmt(&Stmt::For(for_stmt), &mut ctx);
    match &vir_stmt {
        VirStmt::For(vir_for) => {
            assert!(
                matches!(vir_for.kind, VirIterKind::Generic { .. }),
                "expected VirIterKind::Generic in generic mode, got {:?}",
                vir_for.kind
            );
        }
        other => panic!("expected For, got {other:?}"),
    }
}

#[test]
fn concrete_mode_for_loop_missing_iterable_kind_falls_back_to_array() {
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

    let for_stmt = ForStmt {
        var_name: Symbol::UNKNOWN,
        iterable: make_int_expr(0), // Dummy iterable
        body: Block {
            stmts: vec![],
            span: dummy_span(),
        },
        span: dummy_span(),
    };

    let vir_stmt = lower_stmt(&Stmt::For(for_stmt), &mut ctx);
    match &vir_stmt {
        VirStmt::For(vir_for) => {
            assert!(
                matches!(vir_for.kind, VirIterKind::Array { .. }),
                "expected VirIterKind::Array fallback in concrete mode, got {:?}",
                vir_for.kind
            );
        }
        other => panic!("expected For, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// require_is_check_result — direct helper tests
// -----------------------------------------------------------------------

#[test]
fn require_is_check_result_generic_returns_check_unknown() {
    let node_map = empty_node_map();
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let result = ctx.require_is_check_result(dummy_node_id(), 1);
    assert_eq!(result, SemaIsCheckResult::CheckUnknown(TypeId::UNKNOWN));
}

#[test]
fn require_is_check_result_generic_returns_present_data() {
    let mut node_map = empty_node_map();
    let node = dummy_node_id();
    node_map.set_is_check_result(node, SemaIsCheckResult::AlwaysFalse);

    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let result = ctx.require_is_check_result(node, 1);
    assert_eq!(result, SemaIsCheckResult::AlwaysFalse);
}

// -----------------------------------------------------------------------
// generic call — GenericCall emitted for calls to other generics
// -----------------------------------------------------------------------

#[test]
fn generic_mode_call_with_monomorph_key_emits_generic_call() {
    let mut interner = test_interner();
    let mut type_arena = test_type_arena();
    let mut entities = test_entities();
    let mut name_table = test_name_table();
    let mut type_table = test_type_table();

    // Register a generic callee function so function_by_name resolves.
    let callee_sym = interner.intern("identity");
    let callee_name_id = name_table.intern(name_table.main_module(), &[callee_sym], &interner);
    let sig = FunctionType::unary(TypeId::I64, TypeId::I64);
    let func_id = entities.register_function(callee_name_id, callee_name_id, ModuleId::new(0), sig);

    // Build a call expression: `identity(42)`.
    let arg_expr = make_int_expr(42);
    let call_node_id = NodeId::new(ModuleId::new(0), 500);
    let call_expr = Expr {
        id: call_node_id,
        kind: ExprKind::Call(Box::new(CallExpr {
            callee: Expr {
                id: dummy_node_id(),
                kind: ExprKind::Identifier(callee_sym),
                span: dummy_span(),
            },
            args: vec![CallArg::Positional(arg_expr)],
        })),
        span: dummy_span(),
    };

    // Set the MonomorphKey on the call node — type arg is a type param T.
    let t_name_id = name_table.intern_raw(name_table.main_module(), &["T"]);
    let t_type_id = type_arena.type_param(t_name_id);
    let key = MonomorphKey::new(callee_name_id, vec![t_type_id]);

    let mut node_map = empty_node_map();
    node_map.set_generic(call_node_id, key);

    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let vir_ref = lower_expr(&call_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::Call { target, args, .. } => {
            match target {
                CallTarget::GenericCall {
                    function_id,
                    type_args,
                } => {
                    assert_eq!(*function_id, func_id);
                    assert_eq!(type_args.len(), 1);
                    // The type arg should be a Param (translated from TypeParam).
                    let vir_ty = ctx.type_table.get(type_args[0]);
                    assert!(
                        matches!(vir_ty, vole_vir::types::VirType::Param { name } if *name == t_name_id),
                        "expected VirType::Param for T, got {vir_ty:?}"
                    );
                }
                other => panic!("expected CallTarget::GenericCall, got {other:?}"),
            }
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected VirExpr::Call, got {other:?}"),
    }
}

#[test]
fn generic_mode_call_without_monomorph_key_emits_unresolved() {
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let entities = test_entities();
    let name_table = test_name_table();
    let mut type_table = test_type_table();

    let callee_sym = interner.intern("println");
    let call_node_id = NodeId::new(ModuleId::new(0), 600);
    let call_expr = Expr {
        id: call_node_id,
        kind: ExprKind::Call(Box::new(CallExpr {
            callee: Expr {
                id: dummy_node_id(),
                kind: ExprKind::Identifier(callee_sym),
                span: dummy_span(),
            },
            args: vec![],
        })),
        span: dummy_span(),
    };

    let node_map = empty_node_map();
    let mut ctx = make_generic_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let vir_ref = lower_expr(&call_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::Call { target, .. } => {
            assert!(
                matches!(target, CallTarget::Unresolved { .. }),
                "expected Unresolved for non-generic call, got {target:?}"
            );
        }
        other => panic!("expected VirExpr::Call, got {other:?}"),
    }
}

#[test]
fn concrete_mode_call_with_monomorph_key_still_emits_unresolved() {
    let mut interner = test_interner();
    let type_arena = test_type_arena();
    let mut entities = test_entities();
    let mut name_table = test_name_table();
    let mut type_table = test_type_table();

    let callee_sym = interner.intern("identity");
    let callee_name_id = name_table.intern(name_table.main_module(), &[callee_sym], &interner);
    let sig = FunctionType::unary(TypeId::I64, TypeId::I64);
    let _func_id =
        entities.register_function(callee_name_id, callee_name_id, ModuleId::new(0), sig);

    let call_node_id = NodeId::new(ModuleId::new(0), 700);
    let call_expr = Expr {
        id: call_node_id,
        kind: ExprKind::Call(Box::new(CallExpr {
            callee: Expr {
                id: dummy_node_id(),
                kind: ExprKind::Identifier(callee_sym),
                span: dummy_span(),
            },
            args: vec![],
        })),
        span: dummy_span(),
    };

    let key = MonomorphKey::new(callee_name_id, vec![TypeId::I64]);
    let mut node_map = empty_node_map();
    node_map.set_generic(call_node_id, key);

    // Concrete mode — should still emit Unresolved (GenericCall is only
    // for generic templates).
    let mut ctx = make_ctx(
        &node_map,
        &mut interner,
        &type_arena,
        &entities,
        &name_table,
        &mut type_table,
    );

    let vir_ref = lower_expr(&call_expr, &mut ctx);
    match vir_ref.as_ref() {
        VirExpr::Call { target, .. } => {
            assert!(
                matches!(target, CallTarget::Unresolved { .. }),
                "expected Unresolved in concrete mode, got {target:?}"
            );
        }
        other => panic!("expected VirExpr::Call, got {other:?}"),
    }
}
