// vir_lower/tests/mod.rs
//
// Test modules for AST-to-VIR lowering.

mod ast_escape;
mod control_flow;
mod functions;
mod generic_mode;
mod literals;
mod operators;
mod variables;

use crate::node_map::NodeMap;
use crate::{EntityRegistry, TypeArena};
use vole_frontend::ast::{Block, Expr, ExprKind, FuncBody, FuncDecl, Stmt};
use vole_identity::{
    FunctionId, Interner, ModuleId, NameId, NameTable, NodeId, Span, Symbol, TypeId, VirTypeId,
};
use vole_vir::type_table::VirTypeTable;

use super::LoweringCtx;

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
    TypeId::VOID
}

fn vir_type_id(id: TypeId) -> VirTypeId {
    VirTypeId::from_raw(id.raw())
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

fn test_type_arena() -> TypeArena {
    TypeArena::new()
}

fn test_entities() -> EntityRegistry {
    EntityRegistry::default()
}

fn test_name_table() -> NameTable {
    NameTable::new()
}

fn test_type_table() -> VirTypeTable {
    VirTypeTable::new()
}

/// Leaked empty cross-module context for tests.
///
/// Tests don't exercise cross-module resolution, so this provides a
/// `&'static CrossModuleCtx` without requiring each test to allocate one.
fn empty_cross_module() -> &'static super::CrossModuleCtx {
    use std::sync::OnceLock;
    static CTX: OnceLock<super::CrossModuleCtx> = OnceLock::new();
    CTX.get_or_init(super::CrossModuleCtx::empty)
}

/// Leaked empty implement registry for tests.
fn empty_implements() -> &'static crate::implement_registry::ImplementRegistry {
    use std::sync::OnceLock;
    static REG: OnceLock<crate::implement_registry::ImplementRegistry> = OnceLock::new();
    REG.get_or_init(crate::implement_registry::ImplementRegistry::new)
}

/// Create a `LoweringCtx` from test fixtures (concrete mode).
///
/// This is a convenience helper that bundles the common test parameters.
fn make_ctx<'a>(
    node_map: &'a NodeMap,
    interner: &'a mut Interner,
    type_arena: &'a TypeArena,
    entities: &'a EntityRegistry,
    name_table: &'a NameTable,
    type_table: &'a mut VirTypeTable,
) -> LoweringCtx<'a> {
    LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id: name_table.main_module(),
        generic: false,
        func_return_type: TypeId::VOID,
        captures: rustc_hash::FxHashSet::default(),
        cross_module: empty_cross_module(),
        implements: empty_implements(),
    }
}

/// Create a `LoweringCtx` in generic mode.
///
/// Missing NodeMap decisions produce placeholder values instead of panicking.
fn make_generic_ctx<'a>(
    node_map: &'a NodeMap,
    interner: &'a mut Interner,
    type_arena: &'a TypeArena,
    entities: &'a EntityRegistry,
    name_table: &'a NameTable,
    type_table: &'a mut VirTypeTable,
) -> LoweringCtx<'a> {
    LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id: name_table.main_module(),
        generic: true,
        func_return_type: TypeId::VOID,
        captures: rustc_hash::FxHashSet::default(),
        cross_module: empty_cross_module(),
        implements: empty_implements(),
    }
}
