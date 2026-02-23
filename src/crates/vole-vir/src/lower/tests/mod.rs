// lower/tests/mod.rs
//
// Test modules for AST-to-VIR lowering.

mod ast_escape;
mod control_flow;
mod functions;
mod literals;
mod operators;
mod variables;

use vole_frontend::Interner;
use vole_frontend::NodeId;
use vole_frontend::ast::{Block, Expr, ExprKind, FuncBody, FuncDecl, Stmt};
use vole_identity::{FunctionId, ModuleId, NameId, Span, Symbol, TypeId};
use vole_sema::node_map::NodeMap;

fn dummy_span() -> Span {
    Span::default()
}

fn dummy_node_id() -> NodeId {
    NodeId::new(ModuleId::new(0), 0)
}

fn dummy_func_id() -> FunctionId {
    FunctionId::new(0)
}

fn dummy_type_id() -> TypeId {
    TypeId::from_raw(999)
}

fn dummy_name_id() -> NameId {
    NameId::new_for_test(42)
}

fn make_break_stmt() -> Stmt {
    Stmt::Break(dummy_span())
}

fn make_continue_stmt() -> Stmt {
    Stmt::Continue(dummy_span())
}

fn make_bool_expr() -> Expr {
    Expr {
        id: dummy_node_id(),
        kind: ExprKind::BoolLiteral(true),
        span: dummy_span(),
    }
}

fn make_int_expr(value: i64) -> Expr {
    Expr {
        id: dummy_node_id(),
        kind: ExprKind::IntLiteral(value, None),
        span: dummy_span(),
    }
}

fn make_block_func(stmts: Vec<Stmt>) -> FuncDecl {
    FuncDecl {
        name: Symbol::UNKNOWN,
        type_params: vec![],
        params: vec![],
        return_type: None,
        body: FuncBody::Block(Block {
            stmts,
            span: dummy_span(),
        }),
        annotations: vec![],
        span: dummy_span(),
    }
}

fn make_expr_func(expr: Expr) -> FuncDecl {
    FuncDecl {
        name: Symbol::UNKNOWN,
        type_params: vec![],
        params: vec![],
        return_type: None,
        body: FuncBody::Expr(Box::new(expr)),
        annotations: vec![],
        span: dummy_span(),
    }
}

fn empty_node_map() -> NodeMap {
    NodeMap::default()
}

fn test_interner() -> Interner {
    Interner::new()
}
