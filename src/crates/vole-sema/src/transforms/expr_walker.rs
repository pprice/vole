// vole-sema/src/transforms/expr_walker.rs
//! Generic AST expression walkers.
//!
//! Provides reusable traversal helpers that eliminate duplicated match arms
//! across the generator transform functions (`expr_contains_yield`,
//! `collect_yields_from_expr`, `rewrite_captured_refs`).
//!
//! Two flavours:
//!
//! - **Query** (`any_child_expr`): visit child sub-expressions by shared
//!   reference. Used by boolean checks and collection passes.
//! - **Transform** (`map_expr_children`): rebuild an expression tree by
//!   applying a mapping function to every child sub-expression. Used by
//!   the captured-ref rewriter.

use vole_frontend::ast::*;

// ---------------------------------------------------------------------------
// Query walkers
// ---------------------------------------------------------------------------

/// Visit every immediate child expression of `expr` by calling `visit`.
///
/// Returns `true` (short-circuits) if any call to `visit` returns `true`.
/// Handles all `ExprKind` variants -- callers only need to intercept
/// variant-specific cases *before* delegating here.
pub fn any_child_expr(expr: &Expr, visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    match &expr.kind {
        ExprKind::Binary(bin) => visit(&bin.left) || visit(&bin.right),
        ExprKind::Unary(un) => visit(&un.operand),
        ExprKind::Call(call) => visit(&call.callee) || call.args.iter().any(&mut *visit),
        ExprKind::Grouping(inner) => visit(inner),
        ExprKind::ArrayLiteral(elems) => elems.iter().any(&mut *visit),
        ExprKind::RepeatLiteral { element, .. } => visit(element),
        ExprKind::Index(idx) => visit(&idx.object) || visit(&idx.index),
        ExprKind::Match(m) => visit(&m.scrutinee) || m.arms.iter().any(|arm| visit(&arm.body)),
        ExprKind::NullCoalesce(nc) => visit(&nc.value) || visit(&nc.default),
        ExprKind::Is(is_expr) => visit(&is_expr.value),
        ExprKind::FieldAccess(fa) => visit(&fa.object),
        ExprKind::OptionalChain(oc) => visit(&oc.object),
        ExprKind::MethodCall(mc) => visit(&mc.object) || mc.args.iter().any(&mut *visit),
        ExprKind::StructLiteral(sl) => sl.fields.iter().any(|f| visit(&f.value)),
        ExprKind::Assign(assign) => visit(&assign.value),
        ExprKind::CompoundAssign(ca) => visit(&ca.value),
        ExprKind::Range(range) => visit(&range.start) || visit(&range.end),
        ExprKind::Try(inner) => visit(inner),
        ExprKind::Yield(y) => visit(&y.value),
        ExprKind::InterpolatedString(parts) => parts.iter().any(|p| match p {
            StringPart::Literal(_) => false,
            StringPart::Expr(e) => visit(e),
        }),
        ExprKind::Lambda(lambda) => match &lambda.body {
            FuncBody::Expr(e) => visit(e),
            FuncBody::Block(b) => any_child_expr_in_block(b, visit),
        },
        ExprKind::Block(block) => {
            any_child_expr_in_stmts(&block.stmts, visit)
                || block.trailing_expr.as_ref().is_some_and(&mut *visit)
        }
        ExprKind::If(if_expr) => {
            visit(&if_expr.condition)
                || visit(&if_expr.then_branch)
                || if_expr.else_branch.as_ref().is_some_and(&mut *visit)
        }
        ExprKind::When(when_expr) => when_expr
            .arms
            .iter()
            .any(|arm| arm.condition.as_ref().is_some_and(&mut *visit) || visit(&arm.body)),
        // Leaf expressions
        ExprKind::IntLiteral(..)
        | ExprKind::FloatLiteral(..)
        | ExprKind::BoolLiteral(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::Identifier(_)
        | ExprKind::Unreachable
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_) => false,
    }
}

/// Visit every immediate child expression without short-circuiting.
pub fn for_each_child_expr(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    any_child_expr(expr, &mut |e| {
        visit(e);
        false
    });
}

/// Short-circuit check across all expressions in a block.
pub fn any_child_expr_in_block(block: &Block, visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    any_child_expr_in_stmts(&block.stmts, visit)
}

fn any_child_expr_in_stmts(stmts: &[Stmt], visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    stmts.iter().any(|s| any_child_expr_in_stmt(s, visit))
}

/// Short-circuit check across all expressions in a statement.
pub fn any_child_expr_in_stmt(stmt: &Stmt, visit: &mut impl FnMut(&Expr) -> bool) -> bool {
    match stmt {
        Stmt::Expr(expr_stmt) => visit(&expr_stmt.expr),
        Stmt::Let(let_stmt) => match &let_stmt.init {
            LetInit::Expr(e) => visit(e),
            LetInit::TypeAlias(_) => false,
        },
        Stmt::While(while_stmt) => {
            visit(&while_stmt.condition) || any_child_expr_in_block(&while_stmt.body, visit)
        }
        Stmt::For(for_stmt) => {
            visit(&for_stmt.iterable) || any_child_expr_in_block(&for_stmt.body, visit)
        }
        Stmt::If(if_stmt) => {
            visit(&if_stmt.condition)
                || any_child_expr_in_block(&if_stmt.then_branch, visit)
                || if_stmt
                    .else_branch
                    .as_ref()
                    .is_some_and(|b| any_child_expr_in_block(b, visit))
        }
        Stmt::Return(ret_stmt) => ret_stmt.value.as_ref().is_some_and(&mut *visit),
        Stmt::LetTuple(lt) => visit(&lt.init),
        Stmt::Raise(_) | Stmt::Break(_) | Stmt::Continue(_) => false,
    }
}

// ---------------------------------------------------------------------------
// Transform walker
// ---------------------------------------------------------------------------

/// Rebuild an `ExprKind` by applying `map` to every child sub-expression.
///
/// `map` is called on each child -- it is responsible for deciding whether
/// to recurse further or return a different expression. The `map` closure
/// must produce complete `Expr` values (including `NodeId`s).
///
/// Returns only the transformed `ExprKind`; the caller wraps it in an
/// `Expr` with its own id and span.
///
/// Leaf expressions (literals, identifiers, etc.) are cloned unchanged.
pub fn map_expr_children(kind: &ExprKind, map: &mut impl FnMut(&Expr) -> Expr) -> ExprKind {
    match kind {
        ExprKind::Binary(bin) => ExprKind::Binary(Box::new(BinaryExpr {
            left: map(&bin.left),
            op: bin.op,
            right: map(&bin.right),
        })),
        ExprKind::Unary(un) => ExprKind::Unary(Box::new(UnaryExpr {
            op: un.op,
            operand: map(&un.operand),
        })),
        ExprKind::Call(call) => ExprKind::Call(Box::new(CallExpr {
            callee: map(&call.callee),
            args: call.args.iter().map(&mut *map).collect(),
        })),
        ExprKind::Grouping(inner) => ExprKind::Grouping(Box::new(map(inner))),
        ExprKind::ArrayLiteral(elems) => {
            ExprKind::ArrayLiteral(elems.iter().map(&mut *map).collect())
        }
        ExprKind::RepeatLiteral { element, count } => ExprKind::RepeatLiteral {
            element: Box::new(map(element)),
            count: *count,
        },
        ExprKind::Index(idx) => ExprKind::Index(Box::new(IndexExpr {
            object: map(&idx.object),
            index: map(&idx.index),
        })),
        ExprKind::Match(m) => ExprKind::Match(Box::new(MatchExpr {
            scrutinee: map(&m.scrutinee),
            arms: m
                .arms
                .iter()
                .map(|arm| MatchArm {
                    id: arm.id,
                    pattern: arm.pattern.clone(),
                    guard: arm.guard.as_ref().map(&mut *map),
                    body: map(&arm.body),
                    span: arm.span,
                })
                .collect(),
            span: m.span,
        })),
        ExprKind::NullCoalesce(nc) => ExprKind::NullCoalesce(Box::new(NullCoalesceExpr {
            value: map(&nc.value),
            default: map(&nc.default),
        })),
        ExprKind::Is(is_expr) => ExprKind::Is(Box::new(IsExpr {
            value: map(&is_expr.value),
            type_expr: is_expr.type_expr.clone(),
            type_span: is_expr.type_span,
        })),
        ExprKind::FieldAccess(fa) => ExprKind::FieldAccess(Box::new(FieldAccessExpr {
            object: map(&fa.object),
            field: fa.field,
            field_span: fa.field_span,
        })),
        ExprKind::OptionalChain(oc) => ExprKind::OptionalChain(Box::new(OptionalChainExpr {
            object: map(&oc.object),
            field: oc.field,
            field_span: oc.field_span,
        })),
        ExprKind::MethodCall(mc) => ExprKind::MethodCall(Box::new(MethodCallExpr {
            object: map(&mc.object),
            method: mc.method,
            args: mc.args.iter().map(&mut *map).collect(),
            method_span: mc.method_span,
            type_args: mc.type_args.clone(),
        })),
        ExprKind::StructLiteral(sl) => ExprKind::StructLiteral(Box::new(StructLiteralExpr {
            path: sl.path.clone(),
            type_args: sl.type_args.clone(),
            fields: sl
                .fields
                .iter()
                .map(|f| StructFieldInit {
                    name: f.name,
                    value: map(&f.value),
                    span: f.span,
                    shorthand: f.shorthand,
                })
                .collect(),
        })),
        ExprKind::Assign(assign) => ExprKind::Assign(Box::new(AssignExpr {
            target: map_assign_target_children(&assign.target, map),
            value: map(&assign.value),
        })),
        ExprKind::CompoundAssign(ca) => ExprKind::CompoundAssign(Box::new(CompoundAssignExpr {
            target: map_assign_target_children(&ca.target, map),
            op: ca.op,
            value: map(&ca.value),
        })),
        ExprKind::Range(range) => ExprKind::Range(Box::new(RangeExpr {
            start: map(&range.start),
            end: map(&range.end),
            inclusive: range.inclusive,
        })),
        ExprKind::Try(inner) => ExprKind::Try(Box::new(map(inner))),
        ExprKind::Yield(y) => ExprKind::Yield(Box::new(YieldExpr {
            value: map(&y.value),
            span: y.span,
        })),
        ExprKind::InterpolatedString(parts) => ExprKind::InterpolatedString(
            parts
                .iter()
                .map(|p| match p {
                    StringPart::Literal(s) => StringPart::Literal(s.clone()),
                    StringPart::Expr(e) => StringPart::Expr(Box::new(map(e))),
                })
                .collect(),
        ),
        ExprKind::Lambda(lambda) => {
            let body = match &lambda.body {
                FuncBody::Expr(e) => FuncBody::Expr(Box::new(map(e))),
                FuncBody::Block(b) => FuncBody::Block(map_block_children(b, map)),
            };
            ExprKind::Lambda(Box::new(LambdaExpr {
                type_params: lambda.type_params.clone(),
                params: lambda.params.clone(),
                return_type: lambda.return_type.clone(),
                body,
                span: lambda.span,
                captures: lambda.captures.clone(),
                has_side_effects: lambda.has_side_effects.clone(),
            }))
        }
        ExprKind::Block(block) => ExprKind::Block(Box::new(BlockExpr {
            stmts: block
                .stmts
                .iter()
                .map(|s| map_stmt_children(s, map))
                .collect(),
            trailing_expr: block.trailing_expr.as_ref().map(&mut *map),
            span: block.span,
        })),
        ExprKind::If(if_expr) => ExprKind::If(Box::new(IfExpr {
            condition: map(&if_expr.condition),
            then_branch: map(&if_expr.then_branch),
            else_branch: if_expr.else_branch.as_ref().map(&mut *map),
            span: if_expr.span,
        })),
        ExprKind::When(when_expr) => ExprKind::When(Box::new(WhenExpr {
            arms: when_expr
                .arms
                .iter()
                .map(|arm| WhenArm {
                    condition: arm.condition.as_ref().map(&mut *map),
                    body: map(&arm.body),
                    span: arm.span,
                })
                .collect(),
            span: when_expr.span,
        })),
        // Leaf expressions -- clone unchanged
        ExprKind::IntLiteral(..)
        | ExprKind::FloatLiteral(..)
        | ExprKind::BoolLiteral(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::Identifier(_)
        | ExprKind::Unreachable
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_) => kind.clone(),
    }
}

/// Map child expressions inside an `AssignTarget`.
fn map_assign_target_children(
    target: &AssignTarget,
    map: &mut impl FnMut(&Expr) -> Expr,
) -> AssignTarget {
    match target {
        AssignTarget::Variable(_) | AssignTarget::Discard => target.clone(),
        AssignTarget::Index { object, index } => AssignTarget::Index {
            object: Box::new(map(object)),
            index: Box::new(map(index)),
        },
        AssignTarget::Field {
            object,
            field,
            field_span,
        } => AssignTarget::Field {
            object: Box::new(map(object)),
            field: *field,
            field_span: *field_span,
        },
    }
}

/// Map child expressions inside a block.
fn map_block_children(block: &Block, map: &mut impl FnMut(&Expr) -> Expr) -> Block {
    Block {
        stmts: block
            .stmts
            .iter()
            .map(|s| map_stmt_children(s, map))
            .collect(),
        span: block.span,
    }
}

/// Map child expressions inside a statement.
fn map_stmt_children(stmt: &Stmt, map: &mut impl FnMut(&Expr) -> Expr) -> Stmt {
    match stmt {
        Stmt::Expr(expr_stmt) => Stmt::Expr(ExprStmt {
            expr: map(&expr_stmt.expr),
            span: expr_stmt.span,
        }),
        Stmt::Let(let_stmt) => {
            let init = match &let_stmt.init {
                LetInit::Expr(e) => LetInit::Expr(map(e)),
                LetInit::TypeAlias(ty) => LetInit::TypeAlias(ty.clone()),
            };
            Stmt::Let(LetStmt {
                name: let_stmt.name,
                ty: let_stmt.ty.clone(),
                mutable: let_stmt.mutable,
                init,
                span: let_stmt.span,
            })
        }
        Stmt::LetTuple(lt) => Stmt::LetTuple(LetTupleStmt {
            pattern: lt.pattern.clone(),
            mutable: lt.mutable,
            init: map(&lt.init),
            span: lt.span,
        }),
        Stmt::While(while_stmt) => Stmt::While(WhileStmt {
            condition: map(&while_stmt.condition),
            body: map_block_children(&while_stmt.body, map),
            span: while_stmt.span,
        }),
        Stmt::For(for_stmt) => Stmt::For(ForStmt {
            var_name: for_stmt.var_name,
            iterable: map(&for_stmt.iterable),
            body: map_block_children(&for_stmt.body, map),
            span: for_stmt.span,
        }),
        Stmt::If(if_stmt) => Stmt::If(IfStmt {
            condition: map(&if_stmt.condition),
            then_branch: map_block_children(&if_stmt.then_branch, map),
            else_branch: if_stmt
                .else_branch
                .as_ref()
                .map(|b| map_block_children(b, map)),
            span: if_stmt.span,
        }),
        Stmt::Return(ret_stmt) => Stmt::Return(ReturnStmt {
            value: ret_stmt.value.as_ref().map(&mut *map),
            span: ret_stmt.span,
        }),
        Stmt::Raise(raise_stmt) => {
            let fields = raise_stmt
                .fields
                .iter()
                .map(|f| StructFieldInit {
                    name: f.name,
                    value: map(&f.value),
                    span: f.span,
                    shorthand: f.shorthand,
                })
                .collect();
            Stmt::Raise(RaiseStmt {
                error_name: raise_stmt.error_name,
                fields,
                span: raise_stmt.span,
            })
        }
        Stmt::Break(span) => Stmt::Break(*span),
        Stmt::Continue(span) => Stmt::Continue(*span),
    }
}
