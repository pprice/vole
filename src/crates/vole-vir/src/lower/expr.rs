// lower/expr.rs
//
// Expression lowering: AST `Expr` → VIR `VirExpr`.
//
// Includes all expression helpers: literal, binary, unary, control flow, yield.

use vole_frontend::Expr;
use vole_frontend::Interner;
use vole_frontend::ast::{BinaryOp, ExprKind, UnaryOp};
use vole_identity::TypeId;
use vole_sema::node_map::NodeMap;

use crate::expr::{VirBinOp, VirExpr, VirUnOp};
use crate::func::VirBody;
use crate::refs::VirRef;
use crate::stmt::VirStmt;

use super::stmt::lower_stmt;

/// Lower an AST expression into a VIR expression.
///
/// Known expression kinds (literals, grouping) are emitted as proper VIR
/// nodes. Everything else is wrapped in `VirExpr::Ast`.
pub(crate) fn lower_expr(expr: &Expr, node_map: &NodeMap, interner: &mut Interner) -> VirRef {
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
        // Call expressions: explicit match arm for future lowering.
        //
        // Call dispatch requires information that is not yet available in the
        // NodeMap during lowering (function registry, module bindings, closure
        // state, monomorphization keys, etc.).  The call() method in codegen
        // uses ~15 dispatch paths that inspect runtime registries.
        //
        // Until sema annotates a "call dispatch kind" on Call nodes (similar
        // to MethodDispatchKind for method calls), we cannot distinguish
        // direct calls from closures/builtins/FFI during lowering.  All calls
        // remain as Ast escape hatches for now.
        ExprKind::Call(_) => Box::new(VirExpr::Ast {
            expr: Box::new(expr.clone()),
            ty,
        }),
        ExprKind::If(if_expr) => lower_if_expr(if_expr, ty, node_map, interner),
        ExprKind::Block(block_expr) => lower_block_expr(block_expr, ty, node_map, interner),
        ExprKind::Yield(yield_expr) => lower_yield(yield_expr, node_map, interner),
        ExprKind::Unreachable => Box::new(VirExpr::Unreachable {
            line: expr.span.line,
        }),
        ExprKind::Import(_) => Box::new(VirExpr::Import { ty }),
        ExprKind::TypeLiteral(_) => Box::new(VirExpr::TypeLiteral),
        ExprKind::Range(range_expr) => lower_range(range_expr, node_map, interner),
        // Ast escape hatches — explicitly listed so new ExprKind variants
        // cause a compile error rather than silently falling through.
        ExprKind::Grouping(_) => unreachable!("handled above"),
        ExprKind::Assign(_)
        | ExprKind::CompoundAssign(_)
        | ExprKind::ArrayLiteral(_)
        | ExprKind::RepeatLiteral { .. }
        | ExprKind::InterpolatedString(_)
        | ExprKind::Identifier(_)
        | ExprKind::Index(_)
        | ExprKind::Match(_)
        | ExprKind::NullCoalesce(_)
        | ExprKind::Is(_)
        | ExprKind::AsCast(_)
        | ExprKind::Lambda(_)
        | ExprKind::StructLiteral(_)
        | ExprKind::FieldAccess(_)
        | ExprKind::OptionalChain(_)
        | ExprKind::OptionalMethodCall(_)
        | ExprKind::MethodCall(_)
        | ExprKind::Try(_)
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
/// And/Or operators are desugared into `VirExpr::If` for short-circuit
/// evaluation:
///   `a && b` -> `if a { b } else { false }`
///   `a || b` -> `if a { true } else { b }`
///
/// String concatenation (string + string) is emitted as `StringConcat`.
/// All other binary operators become `BinaryOp`.
fn lower_binary(
    bin_expr: &vole_frontend::ast::BinaryExpr,
    _expr: &Expr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    // And/Or: desugar to VirExpr::If for short-circuit evaluation.
    if bin_expr.op == BinaryOp::And {
        return lower_and(bin_expr, ty, node_map, interner);
    }
    if bin_expr.op == BinaryOp::Or {
        return lower_or(bin_expr, ty, node_map, interner);
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

/// Desugar `a && b` -> `if a { b } else { false }`.
fn lower_and(
    bin_expr: &vole_frontend::ast::BinaryExpr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let cond = lower_expr(&bin_expr.left, node_map, interner);
    let then_val = lower_expr(&bin_expr.right, node_map, interner);
    Box::new(VirExpr::If {
        cond,
        then_body: VirBody {
            stmts: Vec::new(),
            trailing: Some(then_val),
        },
        else_body: Some(VirBody {
            stmts: Vec::new(),
            trailing: Some(Box::new(VirExpr::BoolLiteral(false))),
        }),
        ty,
    })
}

/// Desugar `a || b` -> `if a { true } else { b }`.
fn lower_or(
    bin_expr: &vole_frontend::ast::BinaryExpr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let cond = lower_expr(&bin_expr.left, node_map, interner);
    let else_val = lower_expr(&bin_expr.right, node_map, interner);
    Box::new(VirExpr::If {
        cond,
        then_body: VirBody {
            stmts: Vec::new(),
            trailing: Some(Box::new(VirExpr::BoolLiteral(true))),
        },
        else_body: Some(VirBody {
            stmts: Vec::new(),
            trailing: Some(else_val),
        }),
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

/// Lower an `if` expression to `VirExpr::If`.
///
/// The AST `then_branch` and `else_branch` are single expressions, which
/// are wrapped as `VirBody` trailing values (no statements).
fn lower_if_expr(
    if_expr: &vole_frontend::ast::IfExpr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let cond = lower_expr(&if_expr.condition, node_map, interner);
    let then_val = lower_expr(&if_expr.then_branch, node_map, interner);
    let then_body = VirBody {
        stmts: Vec::new(),
        trailing: Some(then_val),
    };
    let else_body = if_expr.else_branch.as_ref().map(|else_branch| {
        let else_val = lower_expr(else_branch, node_map, interner);
        VirBody {
            stmts: Vec::new(),
            trailing: Some(else_val),
        }
    });
    Box::new(VirExpr::If {
        cond,
        then_body,
        else_body,
        ty,
    })
}

/// Lower a block expression to `VirExpr::Block`.
///
/// Lowers each statement via `lower_stmt()` and the optional trailing
/// expression via `lower_expr()`.
fn lower_block_expr(
    block_expr: &vole_frontend::ast::BlockExpr,
    ty: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let stmts: Vec<VirStmt> = block_expr
        .stmts
        .iter()
        .map(|s| lower_stmt(s, node_map, interner))
        .collect();
    let trailing = block_expr
        .trailing_expr
        .as_ref()
        .map(|e| lower_expr(e, node_map, interner));
    Box::new(VirExpr::Block {
        stmts,
        trailing,
        ty,
    })
}

/// Lower a yield expression to `VirExpr::Yield`.
///
/// The yielded value is recursively lowered via `lower_expr`.
fn lower_yield(
    yield_expr: &vole_frontend::ast::YieldExpr,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let value = lower_expr(&yield_expr.value, node_map, interner);
    Box::new(VirExpr::Yield { value })
}

/// Map an AST `BinaryOp` to the VIR `VirBinOp`.
pub(crate) fn map_binary_op(op: BinaryOp) -> VirBinOp {
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

/// Lower a range expression to `VirExpr::Range`.
///
/// Both `start` and `end` sub-expressions are recursively lowered.
fn lower_range(
    range_expr: &vole_frontend::ast::RangeExpr,
    node_map: &NodeMap,
    interner: &mut Interner,
) -> VirRef {
    let start = lower_expr(&range_expr.start, node_map, interner);
    let end = lower_expr(&range_expr.end, node_map, interner);
    Box::new(VirExpr::Range {
        start,
        end,
        inclusive: range_expr.inclusive,
    })
}

/// Map an AST `UnaryOp` to the VIR `VirUnOp`.
pub(crate) fn map_unary_op(op: UnaryOp) -> VirUnOp {
    match op {
        UnaryOp::Neg => VirUnOp::Neg,
        UnaryOp::Not => VirUnOp::Not,
        UnaryOp::BitNot => VirUnOp::BitNot,
    }
}
