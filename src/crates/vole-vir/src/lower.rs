// lower.rs
//
// AST-to-VIR lowering.
//
// Walks the AST, lowering known expression kinds (literals, grouping) to
// proper VIR nodes and wrapping everything else in `VirStmt::Ast` /
// `VirExpr::Ast` escape hatches.  Expression statements (`Stmt::Expr`)
// are lowered through `lower_expr`, which enables literal expressions to
// be emitted as `VirExpr::IntLiteral`, `FloatLiteral`, `BoolLiteral`, etc.
// All other statement kinds remain as `VirStmt::Ast`.

use vole_frontend::Interner;
use vole_frontend::ast::{BinaryOp, ExprKind, FuncBody, FuncDecl, InterfaceMethod, Stmt, UnaryOp};
use vole_frontend::{self, Expr};
use vole_identity::{FunctionId, MethodId, NameId, Symbol, TypeId};
use vole_sema::TypeArena;
use vole_sema::node_map::NodeMap;

use crate::expr::{VirBinOp, VirExpr, VirUnOp};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::VirStmt;

/// Lower a single function declaration into a `VirFunction`.
///
/// `func_id`, `name`, `param_types`, and `return_type` come from the sema
/// entity registry — they are resolved during semantic analysis and passed
/// in by the caller (the compilation pipeline).
///
/// `node_map` is accepted for API compatibility with future phases that will
/// look up per-expression types.  Phase 0 does not use it.
pub fn lower_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirFunction {
    let body = lower_func_body(&func.body, node_map, interner);
    VirFunction {
        id: func_id,
        name,
        params: param_types.to_vec(),
        return_type,
        body,
        mangled_name_id: None,
        method_id: None,
    }
}

/// Lower a monomorphized function instance into a `VirFunction`.
///
/// Like [`lower_function`], but for a generic function that has been
/// instantiated with concrete type arguments.  The caller provides
/// already-substituted `param_types` and `return_type` from the
/// `MonomorphInstance`'s `func_type`.
///
/// In debug builds, asserts that no `TypeId` in the output still
/// contains a type parameter — all types must be concrete after
/// monomorphization.
///
/// The body remains Ast-wrapped (Phase 2 migrates bodies).
#[allow(clippy::too_many_arguments)]
pub fn lower_monomorphized_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    mangled_name_id: NameId,
    interner: &mut Interner,
) -> VirFunction {
    debug_assert_concrete_types(param_types, return_type, type_arena, &name);
    let mut vir = lower_function(
        func,
        func_id,
        name,
        param_types,
        return_type,
        node_map,
        interner,
    );
    vir.mangled_name_id = Some(mangled_name_id);
    vir
}

/// Lower a class/struct method (instance or static) into a `VirFunction`.
///
/// Similar to [`lower_function`] but associates a `MethodId` instead of
/// using the `FunctionId` for lookup.  The `func_id` is a dummy value
/// (methods don't have a `FunctionId` in the entity registry); the real
/// identity is carried by `method_id`.
pub fn lower_method(
    func: &FuncDecl,
    method_id: MethodId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirFunction {
    let body = lower_func_body(&func.body, node_map, interner);
    VirFunction {
        id: FunctionId::new(0), // dummy — methods use method_id for lookup
        name,
        params: param_types.to_vec(),
        return_type,
        body,
        mangled_name_id: None,
        method_id: Some(method_id),
    }
}

/// Lower an interface method (default method with a body) into a `VirFunction`.
///
/// Interface methods use `InterfaceMethod` AST nodes (which have an optional
/// body) rather than `FuncDecl`.  Only methods with a body should be lowered.
pub fn lower_interface_method(
    method: &InterfaceMethod,
    method_id: MethodId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> Option<VirFunction> {
    let body_ast = method.body.as_ref()?;
    let body = lower_func_body(body_ast, node_map, interner);
    Some(VirFunction {
        id: FunctionId::new(0), // dummy — methods use method_id for lookup
        name,
        params: param_types.to_vec(),
        return_type,
        body,
        mangled_name_id: None,
        method_id: Some(method_id),
    })
}

/// Assert (debug-only) that all types in a monomorphized function signature
/// are concrete — no `TypeParam` or `TypeParamRef` remains.
fn debug_assert_concrete_types(
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    arena: &TypeArena,
    func_name: &str,
) {
    if !cfg!(debug_assertions) {
        return;
    }
    for (i, (_sym, ty)) in param_types.iter().enumerate() {
        debug_assert!(
            !arena.contains_type_param(*ty),
            "VIR monomorph `{func_name}`: param {i} still contains a type parameter \
             (TypeId={ty:?})"
        );
    }
    debug_assert!(
        !arena.contains_type_param(return_type),
        "VIR monomorph `{func_name}`: return type still contains a type parameter \
         (TypeId={return_type:?})"
    );
}

/// Lower a test case body into a `VirBody`.
///
/// Test bodies use the same `FuncBody` type as functions, so this delegates
/// to `lower_func_body`.  Exposed as a public API so the lowering pipeline
/// in `analyzed.rs` can lower test bodies alongside function bodies.
pub fn lower_test_body(body: &FuncBody, node_map: &NodeMap, interner: &mut Interner) -> VirBody {
    lower_func_body(body, node_map, interner)
}

/// Lower a `FuncBody` (block or expression) into a `VirBody`.
///
/// Block bodies have their statements walked individually; expression bodies
/// become a single trailing VIR expression.
fn lower_func_body(body: &FuncBody, node_map: &NodeMap, interner: &mut Interner) -> VirBody {
    match body {
        FuncBody::Block(block) => lower_stmts(&block.stmts, node_map, interner),
        FuncBody::Expr(expr) => {
            let trailing = lower_expr(expr, node_map, interner);
            VirBody {
                stmts: Vec::new(),
                trailing: Some(trailing),
            }
        }
    }
}

/// Lower a slice of AST statements into a `VirBody`.
///
/// Expression statements have their inner expression lowered through
/// `lower_expr` (which emits proper VIR for known kinds like literals).
/// All other statement kinds are wrapped in `VirStmt::Ast`.
fn lower_stmts(stmts: &[Stmt], node_map: &NodeMap, interner: &mut Interner) -> VirBody {
    let vir_stmts: Vec<VirStmt> = stmts
        .iter()
        .map(|s| lower_stmt(s, node_map, interner))
        .collect();
    VirBody {
        stmts: vir_stmts,
        trailing: None,
    }
}

/// Lower a single AST statement into a VIR statement.
///
/// Expression statements (`Stmt::Expr`) are lowered through `lower_expr`,
/// which produces proper VIR for known expression kinds. All other
/// statement kinds are wrapped in the `VirStmt::Ast` escape hatch.
fn lower_stmt(stmt: &Stmt, node_map: &NodeMap, interner: &mut Interner) -> VirStmt {
    match stmt {
        Stmt::Expr(expr_stmt) => VirStmt::Expr {
            value: lower_expr(&expr_stmt.expr, node_map, interner),
        },
        _ => VirStmt::Ast {
            stmt: Box::new(stmt.clone()),
        },
    }
}

/// Lower an AST expression into a VIR expression.
///
/// Known expression kinds (literals, grouping) are emitted as proper VIR
/// nodes. Everything else is wrapped in `VirExpr::Ast`.
fn lower_expr(expr: &Expr, node_map: &NodeMap, interner: &mut Interner) -> VirRef {
    // Strip grouping parentheses — lower the inner expression directly.
    if let ExprKind::Grouping(inner) = &expr.kind {
        return lower_expr(inner, node_map, interner);
    }

    let ty = node_map.get_type(expr.id).unwrap_or(TypeId::UNKNOWN);
    match &expr.kind {
        ExprKind::IntLiteral(value, _suffix) => lower_int_literal(*value, ty),
        ExprKind::FloatLiteral(value, _suffix) => {
            Box::new(VirExpr::FloatLiteral { value: *value, ty })
        }
        ExprKind::BoolLiteral(value) => Box::new(VirExpr::BoolLiteral(*value)),
        ExprKind::StringLiteral(s) => {
            let sym = interner.intern(s);
            Box::new(VirExpr::StringLiteral(sym))
        }
        ExprKind::Binary(bin_expr) => lower_binary(bin_expr, expr, ty, node_map, interner),
        ExprKind::Unary(un_expr) => lower_unary(un_expr, ty, node_map, interner),
        // Ast escape hatches — explicitly listed so new ExprKind variants
        // cause a compile error rather than silently falling through.
        ExprKind::Grouping(_) => unreachable!("handled above"),
        ExprKind::Assign(_)
        | ExprKind::CompoundAssign(_)
        | ExprKind::ArrayLiteral(_)
        | ExprKind::RepeatLiteral { .. }
        | ExprKind::InterpolatedString(_)
        | ExprKind::Identifier(_)
        | ExprKind::Call(_)
        | ExprKind::Range(_)
        | ExprKind::Index(_)
        | ExprKind::Match(_)
        | ExprKind::Unreachable
        | ExprKind::NullCoalesce(_)
        | ExprKind::Is(_)
        | ExprKind::AsCast(_)
        | ExprKind::Lambda(_)
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_)
        | ExprKind::StructLiteral(_)
        | ExprKind::FieldAccess(_)
        | ExprKind::OptionalChain(_)
        | ExprKind::OptionalMethodCall(_)
        | ExprKind::MethodCall(_)
        | ExprKind::Try(_)
        | ExprKind::Yield(_)
        | ExprKind::Block(_)
        | ExprKind::If(_)
        | ExprKind::When(_)
        | ExprKind::MetaAccess(_) => Box::new(VirExpr::Ast {
            expr: Box::new(expr.clone()),
            ty,
        }),
    }
}

/// Lower an integer literal, splitting into `WideLiteral` for i128/f128.
fn lower_int_literal(value: i64, ty: TypeId) -> VirRef {
    if ty == TypeId::I128 || ty == TypeId::F128 {
        // Sign-extend i64 to i128 then split into low/high u64.
        let wide = value as i128;
        Box::new(VirExpr::WideLiteral {
            low: wide as u64,
            high: (wide >> 64) as u64,
            ty,
        })
    } else {
        Box::new(VirExpr::IntLiteral { value, ty })
    }
}

/// Lower a binary expression.
///
/// And/Or operators stay as `Ast` escape hatches (they require short-circuit
/// control flow, handled in Phase 4).  String concatenation (string + string)
/// is emitted as `StringConcat`.  All other binary operators become `BinaryOp`.
fn lower_binary(
    bin_expr: &vole_frontend::ast::BinaryExpr,
    expr: &Expr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    // And/Or require short-circuit control flow — keep as Ast.
    if matches!(bin_expr.op, BinaryOp::And | BinaryOp::Or) {
        return Box::new(VirExpr::Ast {
            expr: Box::new(expr.clone()),
            ty,
        });
    }

    let lhs = lower_expr(&bin_expr.left, node_map, interner);
    let rhs = lower_expr(&bin_expr.right, node_map, interner);

    // String concatenation: result type is STRING and op is Add.
    if ty == TypeId::STRING && bin_expr.op == BinaryOp::Add {
        return Box::new(VirExpr::StringConcat {
            parts: vec![lhs, rhs],
        });
    }

    let vir_op = map_binary_op(bin_expr.op);
    Box::new(VirExpr::BinaryOp {
        op: vir_op,
        lhs,
        rhs,
        ty,
    })
}

/// Lower a unary expression to `VirExpr::UnaryOp`.
fn lower_unary(
    un_expr: &vole_frontend::ast::UnaryExpr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let operand = lower_expr(&un_expr.operand, node_map, interner);
    let vir_op = map_unary_op(un_expr.op);
    Box::new(VirExpr::UnaryOp {
        op: vir_op,
        operand,
        ty,
    })
}

/// Map an AST `BinaryOp` to the VIR `VirBinOp`.
fn map_binary_op(op: BinaryOp) -> VirBinOp {
    match op {
        BinaryOp::Add => VirBinOp::Add,
        BinaryOp::Sub => VirBinOp::Sub,
        BinaryOp::Mul => VirBinOp::Mul,
        BinaryOp::Div => VirBinOp::Div,
        BinaryOp::Mod => VirBinOp::Mod,
        BinaryOp::Eq => VirBinOp::Eq,
        BinaryOp::Ne => VirBinOp::Ne,
        BinaryOp::Lt => VirBinOp::Lt,
        BinaryOp::Le => VirBinOp::Le,
        BinaryOp::Gt => VirBinOp::Gt,
        BinaryOp::Ge => VirBinOp::Ge,
        BinaryOp::And => VirBinOp::And,
        BinaryOp::Or => VirBinOp::Or,
        BinaryOp::BitAnd => VirBinOp::BitAnd,
        BinaryOp::BitOr => VirBinOp::BitOr,
        BinaryOp::BitXor => VirBinOp::BitXor,
        BinaryOp::Shl => VirBinOp::Shl,
        BinaryOp::Shr => VirBinOp::Shr,
    }
}

/// Map an AST `UnaryOp` to the VIR `VirUnOp`.
fn map_unary_op(op: UnaryOp) -> VirUnOp {
    match op {
        UnaryOp::Neg => VirUnOp::Neg,
        UnaryOp::Not => VirUnOp::Not,
        UnaryOp::BitNot => VirUnOp::BitNot,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{VirBinOp, VirUnOp};
    use vole_frontend::NodeId;
    use vole_frontend::ast::{BinaryExpr, Block, Expr, ExprKind, UnaryExpr};
    use vole_identity::{ModuleId, Span};

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

    #[test]
    fn lower_empty_block_function() {
        let func = make_block_func(vec![]);
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let ret_ty = dummy_type_id();

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &[],
            ret_ty,
            &node_map,
            &mut interner,
        );

        assert_eq!(vir.id, dummy_func_id());
        assert_eq!(vir.return_type, ret_ty);
        assert!(vir.params.is_empty());
        assert!(vir.body.stmts.is_empty());
        assert!(vir.body.trailing.is_none());
    }

    #[test]
    fn lower_block_function_wraps_stmts_as_ast() {
        let func = make_block_func(vec![make_break_stmt(), make_continue_stmt()]);
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let ret_ty = dummy_type_id();

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &[],
            ret_ty,
            &node_map,
            &mut interner,
        );

        assert_eq!(vir.body.stmts.len(), 2);
        assert!(vir.body.trailing.is_none());

        // Every statement should be VirStmt::Ast
        for stmt in &vir.body.stmts {
            match stmt {
                VirStmt::Ast { .. } => {}
                other => panic!("expected VirStmt::Ast, got {other:?}"),
            }
        }
    }

    #[test]
    fn lower_expr_body_function_sets_trailing() {
        let func = make_expr_func(make_bool_expr());
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let ret_ty = dummy_type_id();

        let vir = lower_function(
            &func,
            dummy_func_id(),
            "test_fn".into(),
            &[],
            ret_ty,
            &node_map,
            &mut interner,
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
        let stmts = vec![make_break_stmt(), make_continue_stmt(), make_break_stmt()];
        let body = lower_stmts(&stmts, &node_map, &mut interner);

        assert_eq!(body.stmts.len(), 3);
        assert!(body.trailing.is_none());

        // Verify the inner AST statements match
        match &body.stmts[0] {
            VirStmt::Ast { stmt } => match stmt.as_ref() {
                Stmt::Break(_) => {}
                other => panic!("expected Break, got {other:?}"),
            },
            other => panic!("expected Ast, got {other:?}"),
        }
        match &body.stmts[1] {
            VirStmt::Ast { stmt } => match stmt.as_ref() {
                Stmt::Continue(_) => {}
                other => panic!("expected Continue, got {other:?}"),
            },
            other => panic!("expected Ast, got {other:?}"),
        }
        match &body.stmts[2] {
            VirStmt::Ast { stmt } => match stmt.as_ref() {
                Stmt::Break(_) => {}
                other => panic!("expected Break, got {other:?}"),
            },
            other => panic!("expected Ast, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Expression lowering
    // -----------------------------------------------------------------------

    #[test]
    fn lower_expr_bool_literal() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = make_bool_expr();
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::BoolLiteral(true) => {}
            other => panic!("expected BoolLiteral(true), got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_int_literal_no_type() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = Expr {
            id: dummy_node_id(),
            kind: ExprKind::IntLiteral(42, None),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        // No type in NodeMap → TypeId::UNKNOWN
        match vir_ref.as_ref() {
            VirExpr::IntLiteral { value: 42, ty } => {
                assert_eq!(*ty, TypeId::UNKNOWN);
            }
            other => panic!("expected IntLiteral, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_int_literal_with_type() {
        let mut node_map = empty_node_map();
        let mut interner = test_interner();
        let node_id = dummy_node_id();
        node_map.set_type(node_id, TypeId::I32);
        let expr = Expr {
            id: node_id,
            kind: ExprKind::IntLiteral(99, None),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::IntLiteral { value: 99, ty } => {
                assert_eq!(*ty, TypeId::I32);
            }
            other => panic!("expected IntLiteral with I32, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_int_literal_i128_becomes_wide() {
        let mut node_map = empty_node_map();
        let mut interner = test_interner();
        let node_id = dummy_node_id();
        node_map.set_type(node_id, TypeId::I128);
        let expr = Expr {
            id: node_id,
            kind: ExprKind::IntLiteral(42, None),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::WideLiteral { low, high, ty } => {
                assert_eq!(*low, 42);
                assert_eq!(*high, 0);
                assert_eq!(*ty, TypeId::I128);
            }
            other => panic!("expected WideLiteral for i128, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_negative_int_i128_sign_extends() {
        let mut node_map = empty_node_map();
        let mut interner = test_interner();
        let node_id = dummy_node_id();
        node_map.set_type(node_id, TypeId::I128);
        let expr = Expr {
            id: node_id,
            kind: ExprKind::IntLiteral(-1, None),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::WideLiteral { low, high, ty } => {
                // -1 as i128 = all 1-bits → low = u64::MAX, high = u64::MAX
                assert_eq!(*low, u64::MAX);
                assert_eq!(*high, u64::MAX);
                assert_eq!(*ty, TypeId::I128);
            }
            other => panic!("expected WideLiteral for negative i128, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_float_literal() {
        let mut node_map = empty_node_map();
        let mut interner = test_interner();
        let node_id = dummy_node_id();
        node_map.set_type(node_id, TypeId::F64);
        let expr = Expr {
            id: node_id,
            kind: ExprKind::FloatLiteral(3.14, None),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::FloatLiteral { value, ty } => {
                assert!((*value - 3.14).abs() < f64::EPSILON);
                assert_eq!(*ty, TypeId::F64);
            }
            other => panic!("expected FloatLiteral, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_grouping_strips_parens() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let inner = Expr {
            id: dummy_node_id(),
            kind: ExprKind::BoolLiteral(false),
            span: dummy_span(),
        };
        let expr = Expr {
            id: dummy_node_id(),
            kind: ExprKind::Grouping(Box::new(inner)),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::BoolLiteral(false) => {}
            other => panic!("expected BoolLiteral(false) through grouping, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_unknown_kind_becomes_ast() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = Expr {
            id: dummy_node_id(),
            kind: ExprKind::Identifier(Symbol::UNKNOWN),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::Ast { .. } => {}
            other => panic!("expected Ast escape hatch, got {other:?}"),
        }
    }

    #[test]
    fn lower_stmt_expr_produces_vir_expr() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        use vole_frontend::ast::ExprStmt;
        let stmt = Stmt::Expr(ExprStmt {
            expr: make_bool_expr(),
            span: dummy_span(),
        });
        let vir_stmt = lower_stmt(&stmt, &node_map, &mut interner);

        match &vir_stmt {
            VirStmt::Expr { value } => match value.as_ref() {
                VirExpr::BoolLiteral(true) => {}
                other => panic!("expected BoolLiteral in Expr stmt, got {other:?}"),
            },
            other => panic!("expected VirStmt::Expr, got {other:?}"),
        }
    }

    #[test]
    fn lower_stmt_non_expr_becomes_ast() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let stmt = make_break_stmt();
        let vir_stmt = lower_stmt(&stmt, &node_map, &mut interner);

        match &vir_stmt {
            VirStmt::Ast { .. } => {}
            other => panic!("expected VirStmt::Ast, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Monomorphized function lowering
    // -----------------------------------------------------------------------

    #[test]
    fn lower_monomorphized_with_concrete_types() {
        let arena = TypeArena::new();
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
        let func = make_block_func(vec![]);
        let node_map = empty_node_map();
        let mut interner = test_interner();
        // Create a type parameter — this should trigger the assertion
        let mut names = vole_identity::NameTable::new();
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
        );
    }

    #[test]
    #[should_panic(expected = "return type still contains a type parameter")]
    fn lower_monomorphized_rejects_type_param_in_return() {
        let mut arena = TypeArena::new();
        let func = make_block_func(vec![]);
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let mut names = vole_identity::NameTable::new();
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
        );
    }

    // -----------------------------------------------------------------------
    // StringLiteral lowering
    // -----------------------------------------------------------------------

    #[test]
    fn lower_expr_string_literal() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = Expr {
            id: dummy_node_id(),
            kind: ExprKind::StringLiteral("hello world".to_string()),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::StringLiteral(sym) => {
                assert_eq!(interner.resolve(*sym), "hello world");
            }
            other => panic!("expected StringLiteral, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_string_literal_empty() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = Expr {
            id: dummy_node_id(),
            kind: ExprKind::StringLiteral(String::new()),
            span: dummy_span(),
        };
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::StringLiteral(sym) => {
                assert_eq!(interner.resolve(*sym), "");
            }
            other => panic!("expected StringLiteral for empty string, got {other:?}"),
        }
    }

    #[test]
    fn lower_expr_string_literal_deduplicates() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr1 = Expr {
            id: dummy_node_id(),
            kind: ExprKind::StringLiteral("same".to_string()),
            span: dummy_span(),
        };
        let expr2 = Expr {
            id: dummy_node_id(),
            kind: ExprKind::StringLiteral("same".to_string()),
            span: dummy_span(),
        };
        let vir1 = lower_expr(&expr1, &node_map, &mut interner);
        let vir2 = lower_expr(&expr2, &node_map, &mut interner);

        // Both should produce the same Symbol
        let sym1 = match vir1.as_ref() {
            VirExpr::StringLiteral(s) => *s,
            _ => panic!("expected StringLiteral"),
        };
        let sym2 = match vir2.as_ref() {
            VirExpr::StringLiteral(s) => *s,
            _ => panic!("expected StringLiteral"),
        };
        assert_eq!(sym1, sym2);
    }

    // -----------------------------------------------------------------------
    // Binary expression lowering
    // -----------------------------------------------------------------------

    fn make_int_expr(value: i64) -> Expr {
        Expr {
            id: dummy_node_id(),
            kind: ExprKind::IntLiteral(value, None),
            span: dummy_span(),
        }
    }

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

    #[test]
    fn lower_binary_add_produces_binary_op() {
        let mut node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = make_binary_expr(make_int_expr(1), BinaryOp::Add, make_int_expr(2));
        node_map.set_type(expr.id, TypeId::I64);
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::BinaryOp { op, lhs, rhs, ty } => {
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
    fn lower_binary_and_stays_as_ast() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = make_binary_expr(make_bool_expr(), BinaryOp::And, make_bool_expr());
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::Ast { .. } => {}
            other => panic!("expected Ast escape hatch for And, got {other:?}"),
        }
    }

    #[test]
    fn lower_binary_or_stays_as_ast() {
        let node_map = empty_node_map();
        let mut interner = test_interner();
        let expr = make_binary_expr(make_bool_expr(), BinaryOp::Or, make_bool_expr());
        let vir_ref = lower_expr(&expr, &node_map, &mut interner);

        match vir_ref.as_ref() {
            VirExpr::Ast { .. } => {}
            other => panic!("expected Ast escape hatch for Or, got {other:?}"),
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
        // (1 + 2) * 3 — the inner `1 + 2` should be lowered to BinaryOp too
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
            kind: ExprKind::ArrayLiteral(vec![
                make_int_expr(1),
                make_int_expr(2),
                make_int_expr(3),
            ]),
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
}
