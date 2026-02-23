// lower/stmt.rs
//
// Statement lowering: AST `Stmt` → VIR `VirStmt`.

use vole_frontend::Interner;
use vole_frontend::ast::{LetInit, LetStmt, Stmt};
use vole_identity::TypeId;
use vole_sema::IterableKind;
use vole_sema::node_map::NodeMap;

use crate::expr::VirExpr;
use crate::stmt::{VirFor, VirIterKind, VirStmt};

use super::expr::lower_expr;
use super::lower_stmts;

/// Lower a single AST statement into a VIR statement.
///
/// Expression statements (`Stmt::Expr`) are lowered through `lower_expr`,
/// which produces proper VIR for known expression kinds.  Statement-level
/// control flow (While, If, Break, Continue, Raise) is lowered to proper
/// VIR nodes.  Remaining statement kinds — including Return — are wrapped
/// in the `VirStmt::Ast` escape hatch.
///
/// Return is kept as Ast because `compile_vir_return` does not yet handle
/// interface boxing, fallible returns, struct returns, or RC bookkeeping;
/// the old `return_stmt()` path handles all of these correctly.
///
/// Each variant is listed explicitly so that adding a new `Stmt` variant
/// causes a compile error rather than silently falling through a wildcard.
pub(crate) fn lower_stmt(stmt: &Stmt, node_map: &NodeMap, interner: &mut Interner) -> VirStmt {
    match stmt {
        Stmt::Expr(expr_stmt) => VirStmt::Expr {
            value: lower_expr(&expr_stmt.expr, node_map, interner),
        },
        Stmt::While(while_stmt) => lower_while(while_stmt, node_map, interner),
        Stmt::If(if_stmt) => lower_if_stmt(if_stmt, node_map, interner),
        Stmt::Break(_) => VirStmt::Break,
        Stmt::Continue(_) => VirStmt::Continue,
        Stmt::Raise(raise_stmt) => lower_raise(raise_stmt, node_map, interner),
        Stmt::Let(let_stmt) => lower_let(let_stmt, node_map, interner),
        Stmt::For(for_stmt) => lower_for(for_stmt, node_map, interner),
        // Ast escape hatches — explicitly listed so new Stmt variants
        // cause a compile error rather than silently falling through.
        //
        // Return stays as Ast until compile_vir_return handles interface
        // boxing, fallible returns, struct returns, and RC bookkeeping.
        //
        // LetTuple stays as Ast because element types require TypeArena
        // (unwrap_tuple / unwrap_fixed_array) which is not available in
        // the lowering context.
        Stmt::Return(_) | Stmt::LetTuple(_) => VirStmt::Ast {
            stmt: Box::new(stmt.clone()),
        },
    }
}

/// Lower a while statement to `VirStmt::While`.
///
/// The condition expression and body statements are recursively lowered.
fn lower_while(
    while_stmt: &vole_frontend::ast::WhileStmt,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirStmt {
    let cond = lower_expr(&while_stmt.condition, node_map, interner);
    let body = lower_stmts(&while_stmt.body.stmts, node_map, interner);
    VirStmt::While { cond, body }
}

/// Lower a raise statement to `VirStmt::Raise`.
///
/// The error name and field value expressions are extracted from the AST.
/// Field values are recursively lowered through `lower_expr`.
fn lower_raise(
    raise_stmt: &vole_frontend::ast::RaiseStmt,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirStmt {
    let fields = raise_stmt
        .fields
        .iter()
        .map(|f| (f.name, lower_expr(&f.value, node_map, interner)))
        .collect();
    VirStmt::Raise {
        error_name: raise_stmt.error_name,
        fields,
    }
}

/// Lower a let statement to `VirStmt::Let`.
///
/// Type aliases (`let T = i32 | i64`) produce no runtime code; they are
/// kept as `VirStmt::Ast` so the old codegen can handle the no-op.
///
/// The binding type (`ty`) comes from:
/// 1. The declared type annotation (via `node_map.get_declared_var_type`),
///    if one was provided in the source — this is the type the codegen
///    should coerce to.
/// 2. Otherwise, the sema-computed expression type.
fn lower_let(let_stmt: &LetStmt, node_map: &NodeMap, interner: &mut Interner) -> VirStmt {
    let init_expr = match &let_stmt.init {
        LetInit::Expr(e) => e,
        // Type aliases produce no runtime code.
        LetInit::TypeAlias(_) => {
            return VirStmt::Ast {
                stmt: Box::new(Stmt::Let(let_stmt.clone())),
            };
        }
    };

    let value = lower_expr(init_expr, node_map, interner);

    // Determine the binding type: use declared type if annotated, else the
    // init expression's inferred type.
    let declared_ty = node_map.get_declared_var_type(init_expr.id);
    let expr_ty = node_map.get_type(init_expr.id).unwrap_or(TypeId::UNKNOWN);
    let ty = declared_ty.unwrap_or(expr_ty);

    VirStmt::Let {
        name: let_stmt.name,
        value,
        mutable: let_stmt.mutable,
        ty,
    }
}

/// Lower a for statement to `VirStmt::For`.
///
/// Looks up the `IterableKind` from the NodeMap (annotated by sema) and
/// maps it to a `VirIterKind`.  The iterable expression, loop body, and
/// iteration variable are recursively lowered.
fn lower_for(
    for_stmt: &vole_frontend::ast::ForStmt,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirStmt {
    let iterable = lower_expr(&for_stmt.iterable, node_map, interner);
    let body = lower_stmts(&for_stmt.body.stmts, node_map, interner);

    let sema_kind = node_map.get_iterable_kind(for_stmt.iterable.id);

    let kind = match sema_kind {
        Some(IterableKind::Range) => VirIterKind::Range,
        Some(IterableKind::Array { elem_type }) => {
            let union_storage = node_map.get_union_storage_kind(for_stmt.iterable.id);
            VirIterKind::Array {
                elem_type,
                union_storage,
            }
        }
        Some(IterableKind::String) => VirIterKind::String,
        Some(IterableKind::IteratorInterface { elem_type }) => {
            VirIterKind::IteratorInterface { elem_type }
        }
        Some(IterableKind::CustomIterator { elem_type }) => {
            VirIterKind::CustomIterator { elem_type }
        }
        Some(IterableKind::CustomIterable { elem_type }) => {
            VirIterKind::CustomIterable { elem_type }
        }
        None => {
            // Fallback for error types — treat as array of i64.
            VirIterKind::Array {
                elem_type: TypeId::I64,
                union_storage: None,
            }
        }
    };

    // Determine the element type for the loop variable.
    let var_type = match kind {
        VirIterKind::Range => TypeId::I64,
        VirIterKind::Array { elem_type, .. } => elem_type,
        VirIterKind::String => TypeId::STRING,
        VirIterKind::IteratorInterface { elem_type }
        | VirIterKind::CustomIterator { elem_type }
        | VirIterKind::CustomIterable { elem_type } => elem_type,
    };

    VirStmt::For(VirFor {
        var_name: for_stmt.var_name,
        var_type,
        iterable,
        body,
        kind,
    })
}

/// Lower an if statement to `VirStmt::Expr { VirExpr::If { ... } }`.
///
/// Vole's VIR has no separate `VirStmt::If` — statement-level `if` is
/// wrapped as a void-typed `VirExpr::If` inside `VirStmt::Expr`.
fn lower_if_stmt(
    if_stmt: &vole_frontend::ast::IfStmt,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirStmt {
    let cond = lower_expr(&if_stmt.condition, node_map, interner);
    let then_body = lower_stmts(&if_stmt.then_branch.stmts, node_map, interner);
    let else_body = if_stmt
        .else_branch
        .as_ref()
        .map(|block| lower_stmts(&block.stmts, node_map, interner));
    VirStmt::Expr {
        value: Box::new(VirExpr::If {
            cond,
            then_body,
            else_body,
            ty: TypeId::VOID,
        }),
    }
}
