// vir_lower/expr.rs
//
// Expression lowering: AST `Expr` → VIR `VirExpr`.
//
// Includes all expression helpers: literal, binary, unary, control flow, yield.

use crate::StringConversion;
use vole_frontend::Expr;
use vole_frontend::ast::{BinaryOp, ExprKind, StringPart, UnaryOp};
use vole_identity::{ImplementMethodMonomorphKey, MonomorphKey, TypeDefId, TypeId, VirTypeId};

use vole_vir::IntrinsicKey;
use vole_vir::calls::{CallTarget, LambdaDefaultsInfo};
use vole_vir::expr::{
    AsCastKind, ComparisonHint, IsCheckResult, VirBinOp, VirCapture, VirCaptureRcKind,
    VirClassMethodMonomorphKey, VirExpr, VirExternalMethodInfo, VirFunctionMonomorphKey,
    VirMetaKind, VirMethodDispatchKind, VirMethodDispatchMeta, VirMethodReceiverCoercion,
    VirResolvedMethod, VirStaticMethodMonomorphKey, VirStringPart, VirUnOp, classify_comparison,
};
use vole_vir::func::VirBody;
use vole_vir::numeric_model::numeric_result_type_v;
use vole_vir::refs::VirRef;
use vole_vir::stmt::VirStmt;

use super::LoweringCtx;
use super::lower_func_body;
use super::pattern::lower_match_expr;
use super::stmt::lower_stmt;

/// Lower an AST expression into a VIR expression.
///
/// All `ExprKind` variants are lowered to concrete `VirExpr` nodes.
/// Grouping parentheses are stripped transparently.
#[deny(clippy::wildcard_enum_match_arm)]
pub fn lower_expr(expr: &Expr, ctx: &mut LoweringCtx<'_>) -> VirRef {
    // Strip grouping parentheses — lower the inner expression directly.
    if let ExprKind::Grouping(inner) = &expr.kind {
        return lower_expr(inner, ctx);
    }

    let ty = ctx.node_map.get_type(expr.id).unwrap_or(TypeId::UNKNOWN);
    match &expr.kind {
        ExprKind::IntLiteral(value, _suffix) => lower_int_literal(*value, ty, ctx),
        ExprKind::FloatLiteral(value, _suffix) => {
            let compat_ty = ctx.compat_ty(ty);
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::FloatLiteral {
                value: *value,
                ty: compat_ty,
                vir_ty,
            })
        }
        ExprKind::BoolLiteral(value) => Box::new(VirExpr::BoolLiteral(*value)),
        ExprKind::StringLiteral(s) => {
            let sym = ctx.interner.intern(s);
            Box::new(VirExpr::StringLiteral(sym))
        }
        ExprKind::Binary(bin_expr) => lower_binary(bin_expr, expr, ty, ctx),
        ExprKind::Unary(un_expr) => lower_unary(un_expr, ty, ctx),
        ExprKind::Call(call_expr) => lower_call(call_expr, expr, ty, ctx),
        ExprKind::If(if_expr) => lower_if_expr(if_expr, ty, ctx),
        ExprKind::Block(block_expr) => lower_block_expr(block_expr, ty, ctx),
        ExprKind::Yield(yield_expr) => lower_yield(yield_expr, ctx),
        ExprKind::Unreachable => Box::new(VirExpr::Unreachable {
            line: expr.span.line,
        }),
        ExprKind::Import(_) => {
            let compat_ty = ctx.compat_ty(ty);
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::Import {
                ty: compat_ty,
                vir_ty,
            })
        }
        ExprKind::TypeLiteral(_) => Box::new(VirExpr::TypeLiteral),
        ExprKind::Range(range_expr) => lower_range(range_expr, ctx),
        ExprKind::Identifier(sym) => {
            let compat_ty = ctx.compat_ty(ty);
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::LocalLoad {
                name: *sym,
                ty: compat_ty,
                vir_ty,
            })
        }
        ExprKind::Assign(assign_expr) => lower_assign(assign_expr, expr, ty, ctx),
        ExprKind::FieldAccess(fa) => lower_field_access(fa, ty, ctx),
        ExprKind::Is(is_expr) => lower_is_check(is_expr, expr, ty, ctx),
        ExprKind::AsCast(as_cast) => lower_as_cast(as_cast, expr, ty, ctx),
        // Remaining variants — explicitly listed so new ExprKind variants
        // cause a compile error rather than silently falling through.
        ExprKind::Grouping(_) => unreachable!("handled above"),
        ExprKind::InterpolatedString(parts) => lower_interpolated_string(parts, ctx),
        ExprKind::CompoundAssign(compound) => lower_compound_assign(compound, expr, ty, ctx),
        ExprKind::Index(idx) => lower_index(idx, expr, ty, ctx),
        ExprKind::MetaAccess(meta_access) => lower_meta_access(meta_access, expr, ty, ctx),
        ExprKind::Lambda(lambda) => lower_lambda(lambda, expr, ty, ctx),
        ExprKind::NullCoalesce(nc) => lower_null_coalesce(nc, expr, ty, ctx),
        ExprKind::OptionalChain(oc) => lower_optional_chain(oc, expr, ty, ctx),
        ExprKind::OptionalMethodCall(omc) => lower_optional_method_call(omc, expr, ty, ctx),
        ExprKind::Try(inner) => lower_try(inner, ty, ctx),
        ExprKind::ArrayLiteral(elements) => lower_array_literal(elements, ty, ctx),
        ExprKind::StructLiteral(struct_lit) => lower_struct_literal(struct_lit, expr, ty, ctx),
        ExprKind::When(when_expr) => lower_when_expr(when_expr, ty, ctx),
        ExprKind::Match(match_expr) => lower_match_expr(match_expr, expr, ty, ctx),
        ExprKind::MethodCall(mc) => {
            let receiver = lower_expr(&mc.object, ctx);
            let args: Vec<VirRef> = mc
                .args
                .iter()
                .map(|a| lower_call_arg(a.expr(), ctx))
                .collect();
            let dispatch = lower_method_dispatch_meta(expr.id, mc.object.id, mc.method, ctx);
            let dispatch_ty = dispatch
                .substituted_return_type
                .or_else(|| {
                    dispatch
                        .resolved_method
                        .as_ref()
                        .map(|r| r.return_type_id())
                })
                .filter(|&t| t != VirTypeId::UNKNOWN);
            let compat_ty = dispatch_ty.unwrap_or_else(|| ctx.compat_ty(ty));
            let vir_ty = dispatch_ty.unwrap_or_else(|| ctx.translate(ty));

            // Pre-resolve float constant and Array.filled static methods.
            if let Some(specialized) =
                try_lower_static_intrinsic(&dispatch, mc.method, &args, compat_ty, vir_ty, ctx)
            {
                return specialized;
            }

            Box::new(VirExpr::MethodCall {
                receiver,
                method: mc.method,
                args,
                dispatch,
                node_id: expr.id,
                ty: compat_ty,
                vir_ty,
            })
        }
        ExprKind::RepeatLiteral { element, count } => {
            let elem = lower_expr(element, ctx);
            let compat_ty = ctx.compat_ty(ty);
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::RepeatLiteral {
                element: elem,
                count: *count,
                ty: compat_ty,
                vir_ty,
            })
        }
    }
}

/// Lower an integer literal, splitting into `WideLiteral` for i128/f128.
fn lower_int_literal(value: i64, ty: TypeId, ctx: &mut LoweringCtx<'_>) -> VirRef {
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    if ty == TypeId::F128 {
        // Integer promoted to f128: convert to f64 first to get a float
        // bit-pattern, then store as the low 64 bits of a wide literal.
        // The high 64 bits are zero so the i128->f128 bitcast in codegen
        // reproduces the same representation as the old int_const(n, f128)
        // path (f64 bits in the low half, zero-extended).
        let f64_bits = (value as f64).to_bits();
        Box::new(VirExpr::WideLiteral {
            low: f64_bits,
            high: 0,
            ty: compat_ty,
            vir_ty,
        })
    } else if ty == TypeId::I128 {
        // Sign-extend i64 to i128 then split into low/high u64.
        let wide = value as i128;
        Box::new(VirExpr::WideLiteral {
            low: wide as u64,
            high: (wide >> 64) as u64,
            ty: compat_ty,
            vir_ty,
        })
    } else {
        Box::new(VirExpr::IntLiteral {
            value,
            ty: compat_ty,
            vir_ty,
        })
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
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    // And/Or: desugar to VirExpr::If for short-circuit evaluation.
    if bin_expr.op == BinaryOp::And {
        return lower_and(bin_expr, ty, ctx);
    }
    if bin_expr.op == BinaryOp::Or {
        return lower_or(bin_expr, ty, ctx);
    }

    let lhs = lower_expr(&bin_expr.left, ctx);
    let rhs = lower_expr(&bin_expr.right, ctx);

    // String concatenation: result type is STRING and op is Add.
    if ty == TypeId::STRING && bin_expr.op == BinaryOp::Add {
        return Box::new(VirExpr::StringConcat {
            parts: vec![lhs, rhs],
        });
    }

    let vir_op = map_binary_op(bin_expr.op);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);

    // Pre-compute optional hints for Eq/Ne comparisons so codegen can
    // dispatch to the nil-comparison path without querying the type table.
    let (lhs_is_optional, rhs_is_optional) =
        if matches!(vir_op, VirBinOp::Eq | VirBinOp::Ne) && !ctx.generic {
            let lhs_opt = ctx
                .node_map
                .get_type(bin_expr.left.id)
                .is_some_and(|t| ctx.type_arena.is_optional(t));
            let rhs_opt = ctx
                .node_map
                .get_type(bin_expr.right.id)
                .is_some_and(|t| ctx.type_arena.is_optional(t));
            (lhs_opt, rhs_opt)
        } else {
            (false, false)
        };

    // Pre-compute signedness hint so codegen can select unsigned
    // Cranelift instructions (udiv, ushr, unsigned icmp) without
    // querying VirTypeId::is_unsigned_int() at compile time.
    let lhs_is_unsigned = if !ctx.generic {
        ctx.node_map
            .get_type(bin_expr.left.id)
            .is_some_and(|t| t.is_unsigned_int())
    } else {
        false
    };

    // Pre-compute the promoted operand type so codegen can read it
    // directly instead of recomputing via numeric_result_type_v.
    // For arithmetic/bitwise ops, vir_ty IS the promoted type.
    // For comparisons (result is BOOL), derive from operand types.
    let promoted_ty = if !ctx.generic && vir_ty == VirTypeId::BOOL {
        match (
            ctx.node_map.get_type(bin_expr.left.id),
            ctx.node_map.get_type(bin_expr.right.id),
        ) {
            (Some(l), Some(r)) => {
                let lv = ctx.translate(l);
                let rv = ctx.translate(r);
                if lv.is_numeric() && rv.is_numeric() {
                    numeric_result_type_v(lv, rv)
                } else {
                    lv
                }
            }
            _ => vir_ty,
        }
    } else {
        vir_ty
    };

    // Pre-compute comparison dispatch hint so codegen can match on a
    // single enum instead of re-detecting types at 5+ dispatch sites.
    let comparison_hint = if !ctx.generic {
        match (
            ctx.node_map.get_type(bin_expr.left.id),
            ctx.node_map.get_type(bin_expr.right.id),
        ) {
            (Some(l), Some(r)) => {
                let lv = ctx.translate(l);
                let rv = ctx.translate(r);
                classify_comparison(vir_op, lv, rv, lhs_is_optional, ctx.type_table)
            }
            _ => ComparisonHint::None,
        }
    } else {
        ComparisonHint::None
    };

    Box::new(VirExpr::BinaryOp {
        op: vir_op,
        lhs,
        rhs,
        ty: compat_ty,
        vir_ty,
        promoted_ty,
        line: expr.span.line,
        lhs_is_optional,
        rhs_is_optional,
        lhs_is_unsigned,
        comparison_hint,
    })
}

/// Desugar `a && b` -> `if a { b } else { false }`.
fn lower_and(
    bin_expr: &vole_frontend::ast::BinaryExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let cond = lower_expr(&bin_expr.left, ctx);
    let then_val = lower_expr(&bin_expr.right, ctx);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
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
        ty: compat_ty,
        vir_ty,
    })
}

/// Desugar `a || b` -> `if a { true } else { b }`.
fn lower_or(
    bin_expr: &vole_frontend::ast::BinaryExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let cond = lower_expr(&bin_expr.left, ctx);
    let else_val = lower_expr(&bin_expr.right, ctx);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
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
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower a unary expression to `VirExpr::UnaryOp`.
fn lower_unary(
    un_expr: &vole_frontend::ast::UnaryExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let operand = lower_expr(&un_expr.operand, ctx);
    let vir_op = map_unary_op(un_expr.op);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::UnaryOp {
        op: vir_op,
        operand,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower an `if` expression to `VirExpr::If`.
///
/// The AST `then_branch` and `else_branch` are single expressions, which
/// are wrapped as `VirBody` trailing values (no statements).
fn lower_if_expr(
    if_expr: &vole_frontend::ast::IfExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let cond = lower_expr(&if_expr.condition, ctx);
    let then_val = lower_expr(&if_expr.then_branch, ctx);
    let then_body = VirBody {
        stmts: Vec::new(),
        trailing: Some(then_val),
    };
    let else_body = if_expr.else_branch.as_ref().map(|else_branch| {
        let else_val = lower_expr(else_branch, ctx);
        VirBody {
            stmts: Vec::new(),
            trailing: Some(else_val),
        }
    });
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::If {
        cond,
        then_body,
        else_body,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower a block expression to `VirExpr::Block`.
///
/// Lowers each statement via `lower_stmt()` and the optional trailing
/// expression via `lower_expr()`.
fn lower_block_expr(
    block_expr: &vole_frontend::ast::BlockExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let stmts: Vec<VirStmt> = block_expr
        .stmts
        .iter()
        .map(|s| lower_stmt(s, ctx))
        .collect();
    let trailing = block_expr
        .trailing_expr
        .as_ref()
        .map(|e| lower_expr(e, ctx));
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Block {
        stmts,
        trailing,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower a yield expression to `VirExpr::Yield`.
///
/// The yielded value is recursively lowered via `lower_expr`.
fn lower_yield(yield_expr: &vole_frontend::ast::YieldExpr, ctx: &mut LoweringCtx<'_>) -> VirRef {
    let value = lower_expr(&yield_expr.value, ctx);
    Box::new(VirExpr::Yield { value })
}

/// Map an AST `BinaryOp` to the VIR `VirBinOp`.
pub fn map_binary_op(op: BinaryOp) -> VirBinOp {
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
fn lower_range(range_expr: &vole_frontend::ast::RangeExpr, ctx: &mut LoweringCtx<'_>) -> VirRef {
    let start = lower_expr(&range_expr.start, ctx);
    let end = lower_expr(&range_expr.end, ctx);
    Box::new(VirExpr::Range {
        start,
        end,
        inclusive: range_expr.inclusive,
    })
}

/// Lower an assignment expression.
///
/// Variable targets (`x = expr`) are lowered to `VirExpr::LocalStore`.
/// Field targets (`obj.field = expr`) are lowered to `VirExpr::FieldStore`.
/// Index targets (`arr[i] = expr`) are lowered to `VirExpr::IndexStore`.
/// Discard targets (`_ = expr`) evaluate the expression for side effects.
fn lower_assign(
    assign_expr: &vole_frontend::ast::AssignExpr,
    expr: &Expr,
    _ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    match &assign_expr.target {
        vole_frontend::AssignTarget::Variable(sym) => {
            let value = lower_expr(&assign_expr.value, ctx);
            Box::new(VirExpr::LocalStore { name: *sym, value })
        }
        vole_frontend::AssignTarget::Field { object, field, .. } => {
            let object_type = ctx.node_map.get_type(object.id).unwrap_or(TypeId::UNKNOWN);
            let narrowed = ctx.is_object_narrowed_from_unknown(object);
            let storage = ctx.resolve_field_storage(object_type, *field, narrowed);
            let obj = lower_expr(object, ctx);
            let value = lower_expr(&assign_expr.value, ctx);
            Box::new(VirExpr::FieldStore {
                object: obj,
                field: *field,
                storage,
                value,
            })
        }
        vole_frontend::AssignTarget::Index { object, index } => {
            let obj = lower_expr(object, ctx);
            let idx = lower_expr(index, ctx);
            let value = lower_expr(&assign_expr.value, ctx);
            let union_storage = ctx.node_map.get_union_storage_kind(expr.id);
            Box::new(VirExpr::IndexStore {
                object: obj,
                index: idx,
                value,
                union_storage,
            })
        }
        // Discard target `_ = expr`: just evaluate the expression for side effects.
        vole_frontend::AssignTarget::Discard => lower_expr(&assign_expr.value, ctx),
    }
}

/// Lower a compound assignment expression.
///
/// Variable targets (`x += expr`) are desugared to:
///   `LocalStore { name, value: BinaryOp { op, lhs: LocalLoad { name, ty }, rhs: lower(expr) } }`
///
/// Field targets (`obj.field += expr`) are desugared to:
///   `FieldStore { object, field, value: BinaryOp { op, lhs: FieldLoad { object, field }, rhs } }`
///
/// Index targets (`arr[i] += expr`) are desugared to:
///   `IndexStore { object, index, value: BinaryOp { op, lhs: Index { object, index }, rhs } }`
///
/// Note: field and index targets lower the object/index sub-expressions
/// twice (once for the load, once for the store). This is safe because
/// Vole assignment targets are always lvalues (variables, field chains,
/// index on a variable), which are side-effect-free to re-evaluate.
///
/// Discard targets (`_ += expr`) are rejected by sema; lowering them
/// would be a compiler bug.
fn lower_compound_assign(
    compound: &vole_frontend::ast::CompoundAssignExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let rhs = lower_expr(&compound.value, ctx);
    let binary_op = map_binary_op(compound.op.to_binary_op());

    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    // For compound assignment, the target (left operand) has the same type
    // as the result, so we can derive signedness from the result type.
    let lhs_is_unsigned = !ctx.generic && ty.is_unsigned_int();

    match &compound.target {
        vole_frontend::AssignTarget::Variable(sym) => {
            let load = Box::new(VirExpr::LocalLoad {
                name: *sym,
                ty: compat_ty,
                vir_ty,
            });
            let binop_result = Box::new(VirExpr::BinaryOp {
                op: binary_op,
                lhs: load,
                rhs,
                ty: compat_ty,
                vir_ty,
                promoted_ty: vir_ty,
                line: expr.span.line,
                lhs_is_optional: false,
                rhs_is_optional: false,
                lhs_is_unsigned,
                comparison_hint: ComparisonHint::None,
            });
            Box::new(VirExpr::LocalStore {
                name: *sym,
                value: binop_result,
            })
        }
        vole_frontend::AssignTarget::Field { object, field, .. } => {
            let object_type = ctx.node_map.get_type(object.id).unwrap_or(TypeId::UNKNOWN);
            let narrowed = ctx.is_object_narrowed_from_unknown(object);
            let storage = ctx.resolve_field_storage(object_type, *field, narrowed);
            let obj_for_load = lower_expr(object, ctx);
            let obj_for_store = lower_expr(object, ctx);
            let load = Box::new(VirExpr::FieldLoad {
                object: obj_for_load,
                field: *field,
                storage,
                ty: compat_ty,
                vir_ty,
            });
            let binop_result = Box::new(VirExpr::BinaryOp {
                op: binary_op,
                lhs: load,
                rhs,
                ty: compat_ty,
                vir_ty,
                promoted_ty: vir_ty,
                line: expr.span.line,
                lhs_is_optional: false,
                rhs_is_optional: false,
                lhs_is_unsigned,
                comparison_hint: ComparisonHint::None,
            });
            Box::new(VirExpr::FieldStore {
                object: obj_for_store,
                field: *field,
                storage,
                value: binop_result,
            })
        }
        vole_frontend::AssignTarget::Index { object, index } => {
            let obj_for_load = lower_expr(object, ctx);
            let idx_for_load = lower_expr(index, ctx);
            let obj_for_store = lower_expr(object, ctx);
            let idx_for_store = lower_expr(index, ctx);
            let union_storage = ctx.node_map.get_union_storage_kind(expr.id);
            let load = Box::new(VirExpr::Index {
                object: obj_for_load,
                index: idx_for_load,
                ty: compat_ty,
                vir_ty,
                union_storage,
            });
            let binop_result = Box::new(VirExpr::BinaryOp {
                op: binary_op,
                lhs: load,
                rhs,
                ty: compat_ty,
                vir_ty,
                promoted_ty: vir_ty,
                line: expr.span.line,
                lhs_is_optional: false,
                rhs_is_optional: false,
                lhs_is_unsigned,
                comparison_hint: ComparisonHint::None,
            });
            Box::new(VirExpr::IndexStore {
                object: obj_for_store,
                index: idx_for_store,
                value: binop_result,
                union_storage,
            })
        }
        vole_frontend::AssignTarget::Discard => {
            // Sema rejects `_ += expr`; this should never be reached.
            unreachable!("INTERNAL: compound assignment to discard should be rejected by sema")
        }
    }
}

/// Lower a field access expression to `VirExpr::FieldLoad`.
///
/// The object sub-expression is recursively lowered.  Storage is resolved
/// to `Direct` (struct) or `Heap` (class) using the object's sema type.
/// Falls back to `ByName` for modules, unknown types, or generic templates.
fn lower_field_access(
    fa: &vole_frontend::ast::FieldAccessExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let object_type = ctx
        .node_map
        .get_type(fa.object.id)
        .unwrap_or(TypeId::UNKNOWN);
    let narrowed = ctx.is_object_narrowed_from_unknown(&fa.object);
    let storage = ctx.resolve_field_storage(object_type, fa.field, narrowed);
    let object = lower_expr(&fa.object, ctx);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::FieldLoad {
        object,
        field: fa.field,
        storage,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower an `is` expression to `VirExpr::IsCheck`.
///
/// Looks up the pre-computed `IsCheckResult` from sema's NodeMap and embeds
/// it directly in the VIR node so codegen never re-derives it.
/// Panics if sema didn't record a result.
fn lower_is_check(
    is_expr: &vole_frontend::ast::IsExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let sema_result = ctx.require_is_check_result(expr.id, expr.span.line);
    let value = lower_expr(&is_expr.value, ctx);
    let mut vir_result = convert_is_check_result(sema_result, ctx);
    // For generic unions, sema may record a tag index from an abstract or
    // differently-instantiated union ordering. Carry the tested type instead of
    // the raw tag so codegen can re-derive the concrete tag with substitutions.
    if matches!(vir_result, IsCheckResult::CheckTag(_)) {
        let scrutinee_ty = ctx
            .node_map
            .get_type(is_expr.value.id)
            .unwrap_or(TypeId::UNKNOWN);
        let tested_ty = recover_tested_type(&vir_result, scrutinee_ty, ctx);
        vir_result = IsCheckResult::CheckUnknown(tested_ty, tested_ty);
    }
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::IsCheck {
        value,
        result: vir_result,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower an `as?`/`as!` cast to `VirExpr::AsCast`.
///
/// Embeds the cast kind (checked/unchecked) and target type, plus the
/// sema-computed `IsCheckResult` so codegen can branch without re-detection.
/// Panics if sema didn't record a result.
fn lower_as_cast(
    as_cast: &vole_frontend::ast::AsCastExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let sema_result = ctx.require_is_check_result(expr.id, expr.span.line);
    let value = lower_expr(&as_cast.value, ctx);
    let kind = match as_cast.kind {
        vole_frontend::ast::AsCastKind::Safe => AsCastKind::Checked,
        vole_frontend::ast::AsCastKind::Unsafe => AsCastKind::Unchecked,
    };
    let vir_result = convert_is_check_result(sema_result, ctx);
    let vir_target_ty = ctx.translate(ty);
    Box::new(VirExpr::AsCast {
        value,
        target_ty: vir_target_ty,
        vir_target_ty,
        kind,
        result: vir_result,
    })
}

/// Convert sema's `IsCheckResult` to VIR's `IsCheckResult`.
///
/// VIR defines its own copy of this enum to avoid circular dependencies
/// and keep the VIR crate dependency-light.
pub(super) fn convert_is_check_result(
    sema: crate::IsCheckResult,
    ctx: &mut LoweringCtx<'_>,
) -> IsCheckResult {
    match sema {
        crate::IsCheckResult::AlwaysTrue => IsCheckResult::AlwaysTrue,
        crate::IsCheckResult::AlwaysFalse => IsCheckResult::AlwaysFalse,
        crate::IsCheckResult::CheckTag(tag) => IsCheckResult::CheckTag(tag),
        crate::IsCheckResult::CheckUnknown(ty) => {
            let compat_ty = ctx.compat_ty(ty);
            let vir_ty = ctx.translate(ty);
            IsCheckResult::CheckUnknown(compat_ty, vir_ty)
        }
    }
}

/// Lower an interpolated string to `VirExpr::InterpolatedString`.
///
/// Each part is lowered to a `VirStringPart`: literal fragments become
/// `VirStringPart::Literal`, and expression fragments carry the
/// sema-annotated `StringConversion` so codegen never re-detects types.
fn lower_interpolated_string(parts: &[StringPart], ctx: &mut LoweringCtx<'_>) -> VirRef {
    let vir_parts: Vec<VirStringPart> = parts
        .iter()
        .map(|part| match part {
            StringPart::Literal(s) => VirStringPart::Literal(ctx.interner.intern(s)),
            StringPart::Expr(expr) => {
                let value = lower_expr(expr, ctx);
                let conversion = if ctx.generic {
                    // In generic mode, check if the expression type contains a
                    // type parameter.  If so, the NodeMap's StringConversion was
                    // derived from abstract TypeParam analysis (which falls
                    // through to I64ToString) and is NOT valid for concrete
                    // instantiations.  Emit StringConversion::Generic so the
                    // VIR monomorphizer re-derives the correct conversion per
                    // instance.
                    let expr_ty = ctx.node_map.get_type(expr.id).unwrap_or(TypeId::UNKNOWN);
                    if ctx.type_arena.contains_type_param(expr_ty) {
                        StringConversion::Generic { type_id: expr_ty }
                    } else {
                        ctx.node_map
                            .get_string_conversion(expr.id)
                            .cloned()
                            .unwrap_or(StringConversion::Generic { type_id: expr_ty })
                    }
                } else {
                    ctx.node_map
                        .get_string_conversion(expr.id)
                        .cloned()
                        .unwrap_or(StringConversion::Identity)
                };
                VirStringPart::Expr { value, conversion }
            }
        })
        .collect();
    Box::new(VirExpr::InterpolatedString { parts: vir_parts })
}

/// Lower an index expression to `VirExpr::Index`.
///
/// The object and index sub-expressions are recursively lowered.
/// `union_storage` is extracted from the NodeMap for dynamic array
/// indexing where the element type is a union.
fn lower_index(
    idx: &vole_frontend::ast::IndexExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let object = lower_expr(&idx.object, ctx);
    let index = lower_expr(&idx.index, ctx);
    let union_storage = ctx.node_map.get_union_storage_kind(expr.id);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Index {
        object,
        index,
        ty: compat_ty,
        vir_ty,
        union_storage,
    })
}

/// Lower a `.@meta` access expression to `VirExpr::MetaAccess`.
///
/// Looks up the `MetaAccessKind` from sema's NodeMap and dispatches:
/// - `Static`: embeds the TypeDefId; carries the lowered object for
///   re-derivation in monomorphized contexts (type-name targets carry `None`).
/// - `Dynamic`: lowers the object expression for vtable dispatch.
/// - `TypeParam`: carries the NameId and lowered object for codegen resolution.
///
/// Panics if sema didn't record a classification.
fn lower_meta_access(
    meta_access: &vole_frontend::ast::MetaAccessExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    use crate::node_map::MetaAccessKind;

    let meta_kind = ctx.require_meta_access(expr.id, expr.span.line);

    let kind = match meta_kind {
        MetaAccessKind::Static { type_def_id } => {
            // Determine whether this is a type-name access (no object needed)
            // or a value-expression access (object needed for re-derivation).
            #[expect(clippy::wildcard_enum_match_arm)] // AST ExprKind, not VIR dispatch
            let object = match &meta_access.object.kind {
                ExprKind::TypeLiteral(_) => None,
                ExprKind::Identifier(_) => {
                    // Could be either a type name or a variable. Always lower
                    // the object so codegen can inspect it for monomorphized
                    // re-derivation. The object won't be compiled in the
                    // non-monomorphized Static path.
                    Some(lower_expr(&meta_access.object, ctx))
                }
                _ => Some(lower_expr(&meta_access.object, ctx)),
            };
            VirMetaKind::Static {
                type_def: type_def_id,
                object,
            }
        }
        MetaAccessKind::Dynamic => {
            let value = lower_expr(&meta_access.object, ctx);
            VirMetaKind::Dynamic { value }
        }
        MetaAccessKind::TypeParam { name_id } => {
            let value = lower_expr(&meta_access.object, ctx);
            VirMetaKind::TypeParam { name_id, value }
        }
    };

    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::MetaAccess {
        kind,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower a lambda expression to `VirExpr::Lambda`.
///
/// Extracts parameter names from the AST, lowers the body to VIR, and
/// collects captures from sema's `LambdaAnalysis`.  Individual parameter
/// types are derived by codegen from the function type `ty` at compile
/// time.
fn lower_lambda(
    lambda: &vole_frontend::ast::LambdaExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let params: Vec<_> = lambda.params.iter().map(|p| p.name).collect();

    // Extract captures from sema's lambda analysis (needed both for the
    // VirExpr::Lambda output and for populating ctx.captures).
    let capture_names: Vec<_> = ctx
        .node_map
        .get_lambda_analysis(expr.id)
        .map(|a| a.captures.iter().map(|c| c.name).collect())
        .unwrap_or_default();

    // Save and restore func_return_type and captures around lambda body
    // lowering.  Without func_return_type save/restore, any `return` inside
    // the lambda would be classified using the outer function's return type.
    // The captures set lets call lowering distinguish CapturedClosure from
    // ClosureVariable for function-typed identifiers.
    let saved_return_type = ctx.func_return_type;
    let saved_captures =
        std::mem::replace(&mut ctx.captures, capture_names.iter().copied().collect());
    if let Some((_, ret, _)) = ctx.type_arena.unwrap_function(ty) {
        ctx.func_return_type = ret;
    }
    let body = lower_func_body(&lambda.body, ctx);
    ctx.func_return_type = saved_return_type;
    ctx.captures = saved_captures;

    // Build VIR captures from the names.
    // Capture types are not tracked in sema's Capture struct, so we use
    // TypeId::UNKNOWN / VirTypeId::UNKNOWN as placeholders.
    let captures = capture_names
        .iter()
        .map(|&name| VirCapture {
            name,
            ty: VirTypeId::UNKNOWN,
            vir_ty: VirTypeId::UNKNOWN,
            by_ref: false,
            rc_kind: VirCaptureRcKind::Unresolved,
        })
        .collect();

    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Lambda {
        params,
        body,
        captures,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower a null coalesce expression (`value ?? default`) to `VirExpr::NullCoalesce`.
///
/// Extracts the sema-computed result type (the non-nil inner type) from the
/// expression's NodeMap entry.  Both `value` and `default` sub-expressions
/// are recursively lowered.
fn lower_null_coalesce(
    nc: &vole_frontend::ast::NullCoalesceExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let value = lower_expr(&nc.value, ctx);
    let default = lower_expr(&nc.default, ctx);
    // The expression type from sema is the non-nil result type (T from T | nil).
    let inner_type = ctx.node_map.get_type(expr.id).unwrap_or(ty);
    let vir_inner_type = ctx.translate(inner_type);
    Box::new(VirExpr::NullCoalesce {
        value,
        default,
        inner_type: vir_inner_type,
        vir_inner_type,
        ty: vir_inner_type,
        vir_ty: vir_inner_type,
    })
}

/// Lower an optional chain field access (`obj?.field`) to `VirExpr::OptionalChain`.
///
/// Extracts `OptionalChainInfo` from sema's NodeMap for the inner/result types.
/// Panics if sema didn't record the info.
fn lower_optional_chain(
    oc: &vole_frontend::ast::OptionalChainExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let info = ctx.require_optional_chain(expr.id, expr.span.line);
    let object = lower_expr(&oc.object, ctx);
    let vir_inner_type = ctx.translate(info.inner_type);
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::OptionalChain {
        object,
        field: oc.field,
        inner_type: vir_inner_type,
        vir_inner_type,
        ty: compat_ty,
        vir_ty,
    })
}

/// Lower an optional method call (`obj?.method(args)`) to `VirExpr::OptionalMethodCall`.
///
/// Extracts `OptionalChainInfo` from sema's NodeMap for the inner/result types.
/// The receiver and arguments are lowered to VIR refs; the original expression's
/// NodeId is preserved for sema method dispatch lookups.
/// Panics if sema didn't record the info.
fn lower_optional_method_call(
    omc: &vole_frontend::ast::OptionalMethodCallExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let info = ctx.require_optional_chain(expr.id, expr.span.line);
    let object = lower_expr(&omc.object, ctx);
    let method_args: Vec<VirRef> = omc
        .args
        .iter()
        .map(|a| lower_call_arg(a.expr(), ctx))
        .collect();
    let vir_inner_type = ctx.translate(info.inner_type);
    let dispatch = lower_method_dispatch_meta(expr.id, omc.object.id, omc.method, ctx);
    // Optional method calls produce an optional result (`Inner?`), not the raw
    // method return type. Keep the expression type from sema (`ty`) and carry
    // method dispatch return info only inside `dispatch`.
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::OptionalMethodCall {
        object,
        method: omc.method,
        method_args,
        dispatch,
        call_node_id: expr.id,
        inner_type: vir_inner_type,
        vir_inner_type,
        ty: compat_ty,
        vir_ty,
    })
}

/// Resolve which `BuiltinMethod` variant a builtin method call corresponds to.
///
/// Uses the receiver's sema type and the method name to select the specific
/// enum variant.  Falls back to `ArrayLength` if the receiver type is
/// unavailable (e.g. in generic templates) — the variant will be corrected
/// after monomorphization when `rederive_method_dispatch_kind` re-derives.
fn resolve_builtin_method(
    receiver_ty: Option<TypeId>,
    method_name: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> vole_vir::BuiltinMethod {
    use vole_identity::TypeId;
    use vole_vir::BuiltinMethod;

    let Some(name) = ctx.interner.try_resolve(method_name) else {
        // Synthetic symbol (e.g. in tests) — rederive will correct.
        return BuiltinMethod::ArrayLength;
    };
    let Some(ty) = receiver_ty else {
        // Generic template — receiver type unknown; rederive will correct.
        return BuiltinMethod::ArrayLength;
    };

    if ctx.type_arena.is_array(ty) {
        return match name {
            "length" => BuiltinMethod::ArrayLength,
            "iter" => BuiltinMethod::ArrayIter,
            "push" => BuiltinMethod::ArrayPush,
            _ => BuiltinMethod::ArrayLength,
        };
    }
    if ty == TypeId::STRING {
        return match name {
            "length" => BuiltinMethod::StringLength,
            "iter" => BuiltinMethod::StringIter,
            _ => BuiltinMethod::StringLength,
        };
    }
    if ty == TypeId::RANGE {
        return match name {
            "iter" => BuiltinMethod::RangeIter,
            _ => BuiltinMethod::RangeIter,
        };
    }
    // Unexpected receiver type for Builtin dispatch — default to ArrayLength.
    BuiltinMethod::ArrayLength
}

/// Lower sema method-dispatch annotations into VIR method metadata.
///
/// The metadata is sema-independent and uses identity types only so downstream
/// passes can consume it without NodeId-indexed map lookups.
fn lower_method_dispatch_meta(
    expr_id: vole_identity::NodeId,
    receiver_node_id: vole_identity::NodeId,
    method_name: vole_identity::Symbol,
    ctx: &mut LoweringCtx<'_>,
) -> VirMethodDispatchMeta {
    let dispatch_kind = ctx
        .node_map
        .get_method_dispatch_kind(expr_id)
        .map(|kind| match kind {
            crate::node_map::MethodDispatchKind::Module(module_id) => {
                VirMethodDispatchKind::Module { module_id }
            }
            crate::node_map::MethodDispatchKind::Builtin => {
                let receiver_ty = ctx.node_map.get_type(receiver_node_id);
                let builtin = resolve_builtin_method(receiver_ty, method_name, ctx);
                VirMethodDispatchKind::Builtin(builtin)
            }
            crate::node_map::MethodDispatchKind::ArrayPush => VirMethodDispatchKind::ArrayPush,
            crate::node_map::MethodDispatchKind::Standard => VirMethodDispatchKind::Standard,
        });

    let receiver_coercion = ctx
        .node_map
        .get_coercion_kind(expr_id)
        .map(|kind| match kind {
            crate::node_map::CoercionKind::IteratorWrap { elem_type } => {
                let vir_elem_type = ctx.translate(elem_type);
                let iterator_interface_type = ctx
                    .name_table
                    .well_known
                    .iterator_type_def
                    .map(|def| {
                        let iface = vole_vir::types::VirType::Interface {
                            def,
                            type_args: vec![vir_elem_type],
                        };
                        ctx.type_table.intern(iface, None)
                    })
                    .unwrap_or(VirTypeId::UNKNOWN);
                VirMethodReceiverCoercion::IteratorWrap {
                    elem_type: vir_elem_type,
                    vir_elem_type,
                    iterator_interface_type,
                }
            }
        });

    let sema_method = ctx.node_map.get_method(expr_id);
    let resolved_method = sema_method.map(|resolved| lower_resolved_method(resolved, ctx));

    let generic_monomorph = ctx
        .node_map
        .get_generic(expr_id)
        .map(|key| VirFunctionMonomorphKey {
            func_name: key.func_name,
            type_keys: key
                .type_keys
                .iter()
                .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                .collect(),
            vir_type_keys: key
                .type_keys
                .iter()
                .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                .collect(),
        });

    let substituted_return_type = ctx
        .node_map
        .get_substituted_return_type(expr_id)
        .map(|ty| ctx.translate(ty));
    let vir_substituted_return_type = substituted_return_type;
    let resolved_call_args = ctx
        .node_map
        .get_resolved_call_args(expr_id)
        .map(|m| m.to_vec());
    let class_method_generic =
        ctx.node_map
            .get_class_method_generic(expr_id)
            .map(|key| VirClassMethodMonomorphKey {
                class_name: key.class_name,
                method_name: key.method_name,
                type_keys: key
                    .type_keys
                    .iter()
                    .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                    .collect(),
                vir_type_keys: key
                    .type_keys
                    .iter()
                    .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                    .collect(),
            });
    let static_method_generic =
        ctx.node_map
            .get_static_method_generic(expr_id)
            .map(|key| VirStaticMethodMonomorphKey {
                class_name: key.class_name,
                method_name: key.method_name,
                class_type_keys: key
                    .class_type_keys
                    .iter()
                    .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                    .collect(),
                vir_class_type_keys: key
                    .class_type_keys
                    .iter()
                    .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                    .collect(),
                method_type_keys: key
                    .method_type_keys
                    .iter()
                    .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                    .collect(),
                vir_method_type_keys: key
                    .method_type_keys
                    .iter()
                    .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                    .collect(),
            });

    // Build implement_method_monomorph key when the resolved method is a
    // DefaultMethod on a type extending a generic interface (e.g., array
    // Iterable defaults like map/filter/count).
    let implement_method_monomorph = if !ctx.generic {
        sema_method.and_then(|resolved| {
            let crate::resolution::ResolvedMethod::DefaultMethod {
                type_def_id: Some(impl_type_def_id),
                interface_type_def_id,
                method_name_id,
                ..
            } = resolved
            else {
                return None;
            };
            let receiver_ty = ctx.node_map.get_type(receiver_node_id)?;
            let elem_ty = ctx.type_arena.unwrap_array(receiver_ty)?;
            let elem_vir_type = ctx.translate(elem_ty);
            Some(ImplementMethodMonomorphKey {
                interface_type_def_id: *interface_type_def_id,
                implementing_type_def_id: *impl_type_def_id,
                method_name: *method_name_id,
                type_keys: vec![elem_vir_type],
            })
        })
    } else {
        None
    };

    // Pre-compute whether the receiver's type is an interface.
    // In generic mode the receiver type may be a type parameter, so default
    // to `false` — rederive will update after monomorphization.
    let receiver_is_interface = if ctx.generic {
        false
    } else {
        ctx.node_map
            .get_type(receiver_node_id)
            .is_some_and(|ty| ctx.type_arena.is_interface(ty))
    };

    // Pre-compute whether the resolved method returns a raw RuntimeIterator
    // pointer (not a boxed Iterator<T> interface).  This is true for:
    // 1. Implemented methods with external binding (runtime FFI)
    // 2. DefaultMethod with external binding OR on Iterable interface
    // 3. InterfaceMethod on Iterator interface (vtable thunks)
    // 4. IteratorWrap receiver coercion
    let returns_raw_iterator = {
        let from_resolved = sema_method.is_some_and(|resolved| match resolved {
            crate::resolution::ResolvedMethod::Implemented { external_info, .. } => {
                external_info.is_some()
            }
            crate::resolution::ResolvedMethod::DefaultMethod {
                external_info,
                interface_type_def_id,
                ..
            } => {
                external_info.is_some()
                    || ctx
                        .name_table
                        .well_known
                        .is_iterable_type_def(*interface_type_def_id)
            }
            crate::resolution::ResolvedMethod::InterfaceMethod {
                interface_type_def_id,
                ..
            } => ctx
                .name_table
                .well_known
                .is_iterator_type_def(*interface_type_def_id),
            _ => false,
        });
        let from_coercion = receiver_coercion
            .as_ref()
            .is_some_and(|c| matches!(c, VirMethodReceiverCoercion::IteratorWrap { .. }));
        from_resolved || from_coercion
    };

    VirMethodDispatchMeta {
        dispatch_kind,
        receiver_coercion,
        resolved_method,
        generic_monomorph,
        substituted_return_type,
        vir_substituted_return_type,
        resolved_call_args,
        class_method_generic,
        static_method_generic,
        implement_method_monomorph,
        receiver_is_interface,
        returns_raw_iterator,
    }
}

fn lower_resolved_method(
    resolved: &crate::resolution::ResolvedMethod,
    ctx: &mut LoweringCtx<'_>,
) -> VirResolvedMethod {
    match resolved {
        crate::resolution::ResolvedMethod::Direct {
            type_def_id,
            func_type_id,
            return_type_id,
            method_id,
            ..
        } => VirResolvedMethod::Direct {
            type_def_id: *type_def_id,
            func_type_id: ctx.translate(*func_type_id),
            vir_func_type_id: ctx.translate(*func_type_id),
            return_type_id: ctx.translate(*return_type_id),
            vir_return_type_id: ctx.translate(*return_type_id),
            method_id: *method_id,
        },
        crate::resolution::ResolvedMethod::Implemented {
            type_def_id,
            func_type_id,
            return_type_id,
            is_builtin,
            external_info,
            concrete_return_hint,
            ..
        } => {
            // Normalize Iterator<T> → RuntimeIterator<T> in the return type
            // for external methods.  Runtime functions return raw iterator
            // pointers, so codegen should see RuntimeIterator<T> directly.
            let ret = ctx.translate(*return_type_id);
            let ret = if external_info.is_some() {
                ctx.normalize_iterator_return(ret)
            } else {
                ret
            };
            VirResolvedMethod::Implemented {
                type_def_id: *type_def_id,
                func_type_id: ctx.translate(*func_type_id),
                vir_func_type_id: ctx.translate(*func_type_id),
                return_type_id: ret,
                vir_return_type_id: ret,
                is_builtin: *is_builtin,
                external_info: external_info.map(|info| VirExternalMethodInfo {
                    module_path: info.module_path,
                    native_name: info.native_name,
                }),
                concrete_return_hint: concrete_return_hint.map(|ty| ctx.translate(ty)),
                vir_concrete_return_hint: concrete_return_hint.map(|ty| ctx.translate(ty)),
            }
        }
        crate::resolution::ResolvedMethod::FunctionalInterface {
            func_type_id,
            return_type_id,
            ..
        } => VirResolvedMethod::FunctionalInterface {
            func_type_id: ctx.translate(*func_type_id),
            vir_func_type_id: ctx.translate(*func_type_id),
            return_type_id: ctx.translate(*return_type_id),
            vir_return_type_id: ctx.translate(*return_type_id),
        },
        crate::resolution::ResolvedMethod::DefaultMethod {
            type_def_id,
            interface_type_def_id,
            func_type_id,
            return_type_id,
            external_info,
            concrete_return_hint,
            ..
        } => {
            // Normalize Iterator<T> → RuntimeIterator<T> for default methods
            // with external bindings (e.g. Iterable default methods like map,
            // filter that call iter() internally and return RuntimeIterator).
            let ret = ctx.translate(*return_type_id);
            let ret = if external_info.is_some() {
                ctx.normalize_iterator_return(ret)
            } else {
                ret
            };
            VirResolvedMethod::DefaultMethod {
                type_def_id: *type_def_id,
                interface_type_def_id: *interface_type_def_id,
                func_type_id: ctx.translate(*func_type_id),
                vir_func_type_id: ctx.translate(*func_type_id),
                return_type_id: ret,
                vir_return_type_id: ret,
                external_info: external_info.map(|info| VirExternalMethodInfo {
                    module_path: info.module_path,
                    native_name: info.native_name,
                }),
                concrete_return_hint: concrete_return_hint.map(|ty| ctx.translate(ty)),
            }
        }
        crate::resolution::ResolvedMethod::InterfaceMethod {
            interface_type_def_id,
            func_type_id,
            return_type_id,
            method_index,
            ..
        } => {
            // Normalize Iterator<T> → RuntimeIterator<T> only for methods on
            // the Iterator interface itself.  Vtable thunks for Iterator wrap
            // results in RuntimeIterator.  Other interfaces returning
            // Iterator<T> return boxed interface pointers — DO NOT normalize.
            let ret = ctx.translate(*return_type_id);
            let ret = if ctx
                .name_table
                .well_known
                .is_iterator_type_def(*interface_type_def_id)
            {
                ctx.normalize_iterator_return(ret)
            } else {
                ret
            };
            VirResolvedMethod::InterfaceMethod {
                interface_type_def_id: *interface_type_def_id,
                func_type_id: ctx.translate(*func_type_id),
                vir_func_type_id: ctx.translate(*func_type_id),
                return_type_id: ret,
                vir_return_type_id: ret,
                method_index: *method_index,
            }
        }
        crate::resolution::ResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type_id,
            return_type_id,
            ..
        } => VirResolvedMethod::Static {
            type_def_id: *type_def_id,
            method_id: *method_id,
            func_type_id: ctx.translate(*func_type_id),
            vir_func_type_id: ctx.translate(*func_type_id),
            return_type_id: ctx.translate(*return_type_id),
            vir_return_type_id: ctx.translate(*return_type_id),
        },
    }
}

/// Lower a try expression (`expr?`) to `VirExpr::Try`.
///
/// The inner fallible expression is recursively lowered.  `success_type` is
/// the sema-computed type of the overall try expression (the unwrapped success
/// type from the fallible).
fn lower_try(inner: &Expr, ty: TypeId, ctx: &mut LoweringCtx<'_>) -> VirRef {
    let value = lower_expr(inner, ctx);
    let vir_success_type = ctx.translate(ty);
    Box::new(VirExpr::Try {
        value,
        success_type: vir_success_type,
        vir_success_type,
    })
}

/// Lower an array literal to `VirExpr::ArrayLiteral`.
///
/// Each element is recursively lowered. `ty` is the sema-inferred overall
/// type (array or tuple); codegen uses `unwrap_array` / `unwrap_tuple` to
/// dispatch between dynamic-array (heap) and tuple (stack) construction.
fn lower_array_literal(elements: &[Expr], ty: TypeId, ctx: &mut LoweringCtx<'_>) -> VirRef {
    let lowered: Vec<VirRef> = elements.iter().map(|e| lower_expr(e, ctx)).collect();
    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    // Compute store strategy for dynamic arrays (not tuples).
    let store_strategy = ctx.type_arena.unwrap_array(ty).map(|elem_ty| {
        let vir_elem = ctx.translate(elem_ty);
        ctx.type_table.array_store_strategy(vir_elem)
    });
    Box::new(VirExpr::ArrayLiteral {
        elements: lowered,
        ty: compat_ty,
        vir_ty,
        store_strategy,
    })
}

/// Lower a struct/class literal to VIR.
///
/// Reads `StructLiteralInfo` from the NodeMap to determine whether to emit
/// `VirExpr::StructLiteral` (stack value type) or `VirExpr::ClassInstance`
/// (heap reference type).
/// Panics if sema didn't record the info.
fn lower_struct_literal(
    sl: &vole_frontend::ast::StructLiteralExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let info = ctx.require_struct_literal_info(expr.id, expr.span.line);

    let fields: Vec<(vole_identity::Symbol, VirRef)> = sl
        .fields
        .iter()
        .map(|f| (f.name, lower_expr(&f.value, ctx)))
        .collect();

    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    if info.is_class {
        let field_coercions = classify_class_field_coercions(sl, info.type_def_id, ctx);
        Box::new(VirExpr::ClassInstance {
            type_def: info.type_def_id,
            fields,
            field_coercions,
            ty: compat_ty,
            vir_ty,
        })
    } else {
        Box::new(VirExpr::StructLiteral {
            type_def: info.type_def_id,
            fields,
            ty: compat_ty,
            vir_ty,
        })
    }
}

/// Pre-compute per-field coercion hints for a class instance literal.
///
/// For each field in the literal, determines the exact coercion needed to
/// store the init value into the field (unknown boxing/copy, union
/// boxing/copy, interface boxing/copy, or none).  Codegen reads the
/// resulting `FieldCoercionHint` with no type queries.
///
/// Returns an empty vec in generic mode (codegen falls back to type queries).
fn classify_class_field_coercions(
    sl: &vole_frontend::ast::StructLiteralExpr,
    type_def_id: TypeDefId,
    ctx: &LoweringCtx<'_>,
) -> Vec<vole_vir::FieldCoercionHint> {
    use vole_vir::FieldCoercionHint;

    if ctx.generic {
        return Vec::new();
    }

    let type_def = ctx.entities.get_type(type_def_id);
    let generic_info = match type_def.generic_info.as_ref() {
        Some(gi) => gi,
        None => return vec![FieldCoercionHint::Unresolved; sl.fields.len()],
    };

    sl.fields
        .iter()
        .map(|f| classify_single_field_coercion(f, generic_info, ctx))
        .collect()
}

/// Classify a single field's coercion hint.
///
/// Determines the exact coercion needed to store the init value into
/// the field: unknown boxing/copy, union boxing/copy, interface
/// boxing/copy, or no coercion.
fn classify_single_field_coercion(
    f: &vole_frontend::ast::StructFieldInit,
    generic_info: &crate::entity_defs::GenericTypeInfo,
    ctx: &LoweringCtx<'_>,
) -> vole_vir::FieldCoercionHint {
    use vole_vir::FieldCoercionHint;

    let field_name_str = ctx.interner.resolve(f.name);
    let field_idx = match generic_info.field_index_by_name(field_name_str, ctx.name_table) {
        Some(idx) => idx,
        None => return FieldCoercionHint::Unresolved,
    };
    let field_ty = generic_info.field_types[field_idx];
    let init_ty = ctx.node_map.get_type(f.value.id).unwrap_or(TypeId::UNKNOWN);

    // When the field or init type contains unsubstituted type parameters
    // (e.g. from `lower_monomorphized_function` which re-lowers generic
    // methods with concrete codegen types but still sees generic sema
    // field types), we cannot classify reliably — fall back to codegen
    // type queries.
    if ctx.type_arena.contains_type_param(field_ty) || ctx.type_arena.contains_type_param(init_ty) {
        return FieldCoercionHint::Unresolved;
    }

    // Unknown field: box concrete values, copy existing unknowns.
    if ctx.type_arena.is_unknown(field_ty) {
        return if ctx.type_arena.is_unknown(init_ty) {
            FieldCoercionHint::UnknownCopy
        } else {
            FieldCoercionHint::UnknownBox
        };
    }

    // Union field: wrap concrete values, copy existing unions.
    if ctx.type_arena.is_union(field_ty) {
        return if ctx.type_arena.is_union(init_ty) {
            FieldCoercionHint::UnionCopy
        } else {
            FieldCoercionHint::UnionBox
        };
    }

    // Interface field: box concrete values, copy existing interfaces.
    if ctx.type_arena.is_interface(field_ty) {
        return if ctx.type_arena.is_interface(init_ty) {
            FieldCoercionHint::InterfaceCopy
        } else {
            FieldCoercionHint::InterfaceBox
        };
    }

    FieldCoercionHint::None
}

/// Lower a call expression to `VirExpr::Call`.
///
/// Classification proceeds through a chain of checks:
///
/// 1. **Indirect calls** (non-identifier callee, e.g. `array[0]()`) are
///    lowered as `CallTarget::Lambda` with the callee prepended as the first
///    arg.  Codegen's `compile_vir_lambda_call` handles these directly.
///
/// 2. **Intrinsics** (`print_char`, `assert`, sema-resolved intrinsic keys)
///    are classified via `resolve_intrinsic_target()`.
///
/// 3. **Direct function calls** (same-module, cross-module, prelude) are
///    classified via `resolve_callee_target()`, which skips functions
///    with interface/union params.  Functions with default parameters
///    are resolved to Direct/Native and their missing args are filled
///    by `fill_default_args()`.
///
/// 4. **Closure/captured/functional-interface variables** are classified via
///    `resolve_closure_variable_target()` using sema's `callee_var_type`.
///
/// 5. **Global closures** are classified via `resolve_global_closure_target()`.
///
/// 6. **Generic calls** (in generic mode) are classified via
///    `generic_call_target()` as `CallTarget::GenericCall`.
///
/// Calls that don't match any of the above become `CallTarget::Unresolved`,
/// which codegen resolves via `call_dispatch()`.  See `CallTarget::Unresolved`
/// for the full list of remaining cases.
fn lower_call(
    call_expr: &vole_frontend::ast::CallExpr,
    expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    // Indirect calls: callee is a non-identifier expression (e.g., `array[0]()`).
    // Lower the callee as the first VIR arg, followed by the actual arguments,
    // and emit CallTarget::Lambda so codegen's compile_vir_lambda_call handles
    // the closure extraction and call directly.
    if !matches!(&call_expr.callee.kind, ExprKind::Identifier(_)) {
        let callee_ref = lower_expr(&call_expr.callee, ctx);
        let mut args = Vec::with_capacity(1 + call_expr.args.len());
        args.push(callee_ref);
        for arg in &call_expr.args {
            args.push(lower_call_arg(arg.expr(), ctx));
        }
        let compat_ty = ctx.compat_ty(ty);
        let vir_ty = ctx.translate(ty);
        let result_is_fallible = !ctx.generic && ctx.type_arena.unwrap_fallible(ty).is_some();
        return Box::new(VirExpr::Call {
            target: CallTarget::Lambda,
            args,
            ty: compat_ty,
            vir_ty,
            result_is_fallible,
        });
    }

    // Extract the callee symbol from the identifier expression.
    let callee_sym = match &call_expr.callee.kind {
        ExprKind::Identifier(sym) => *sym,
        _ => unreachable!("non-identifier callee handled above"),
    };

    // Lower argument expressions to VIR, handling implicit `it` lambdas.
    let mut args: Vec<VirRef> = call_expr
        .args
        .iter()
        .map(|arg| lower_call_arg(arg.expr(), ctx))
        .collect();

    // Grab the resolved named-arg mapping from sema (if any).
    let resolved_call_args = ctx
        .node_map
        .get_resolved_call_args(expr.id)
        .map(|m| m.to_vec());

    // Grab lambda parameter defaults from sema (if any).
    let lambda_defaults = ctx
        .node_map
        .get_lambda_defaults(expr.id)
        .map(|d| LambdaDefaultsInfo {
            required_params: d.required_params,
            lambda_node_id: d.lambda_node_id,
        });

    // In generic mode, check if this call has a MonomorphKey — that means
    // it targets another generic function.  Emit GenericCall so the VIR
    // monomorphization pass can resolve it to a concrete callee later.
    //
    // The sema-side key has raw-preserved VirTypeIds (from_type_id).
    // Translate them to proper VirTypeTable indices so the key matches
    // what VirProgram stores.
    let monomorph_key = ctx.node_map.get_generic(expr.id).map(|key| {
        MonomorphKey::new(
            key.func_name,
            key.type_keys
                .iter()
                .map(|&ty| ctx.translate(ty.to_type_id_raw()))
                .collect(),
        )
    });
    // Grab the raw sema-side type keys from the MonomorphKey (before VIR
    // type table translation) for generic external function resolution.
    let sema_type_keys: Option<Vec<_>> = ctx
        .node_map
        .get_generic(expr.id)
        .map(|key| key.type_keys.clone());

    let make_unresolved = |rca, ld, mk| CallTarget::Unresolved {
        callee_sym,
        call_node_id: expr.id,
        line: expr.span.line,
        resolved_call_args: rca,
        lambda_defaults: ld,
        monomorph_key: mk,
    };
    let target = if ctx.generic {
        if let Some(generic) = generic_call_target(expr, ctx) {
            generic
        } else if let Some(intrinsic) = resolve_intrinsic_target(expr, callee_sym, ctx) {
            intrinsic
        } else if let Some(closure_target) = resolve_closure_variable_target(
            expr.id,
            callee_sym,
            &resolved_call_args,
            &lambda_defaults,
            ctx,
        ) {
            closure_target
        } else if let Some(global_target) = resolve_global_closure_target(
            callee_sym,
            &resolved_call_args,
            &lambda_defaults,
            &monomorph_key,
            ctx,
        ) {
            global_target
        } else if let Some(target) = ctx.resolve_callee_target(callee_sym) {
            match target {
                CallTarget::Intrinsic { key, .. } => CallTarget::Intrinsic {
                    key,
                    line: expr.span.line,
                },
                other => other,
            }
        } else {
            make_unresolved(resolved_call_args, lambda_defaults, monomorph_key)
        }
    } else if let Some(intrinsic) = resolve_intrinsic_target(expr, callee_sym, ctx) {
        intrinsic
    } else if let Some(target) = ctx.resolve_callee_target(callee_sym) {
        // Fix up the line number for intrinsic targets (resolve_callee_target
        // returns line: 0 since it doesn't have span context).
        match target {
            CallTarget::Intrinsic { key, .. } => CallTarget::Intrinsic {
                key,
                line: expr.span.line,
            },
            other => other,
        }
    } else if let Some(ref sema_keys) = sema_type_keys
        && let Some(target) =
            ctx.resolve_generic_external_callee(callee_sym, sema_keys, expr.span.line)
    {
        target
    } else if let Some(closure_target) = resolve_closure_variable_target(
        expr.id,
        callee_sym,
        &resolved_call_args,
        &lambda_defaults,
        ctx,
    ) {
        closure_target
    } else if let Some(global_target) = resolve_global_closure_target(
        callee_sym,
        &resolved_call_args,
        &lambda_defaults,
        &monomorph_key,
        ctx,
    ) {
        global_target
    } else {
        make_unresolved(resolved_call_args, lambda_defaults, monomorph_key)
    };

    // For Direct and Native calls to functions with default parameters,
    // fill missing args by lowering the default expressions from the
    // entity registry.  This ensures the VIR Call node always has
    // the full argument list — codegen never needs to look up defaults.
    if matches!(
        &target,
        CallTarget::Direct { .. } | CallTarget::Native { .. } | CallTarget::Intrinsic { .. }
    ) {
        fill_default_args(callee_sym, &mut args, expr.id, ctx);
    }

    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);

    // Normalize Iterator<T> → RuntimeIterator<T> for native calls.
    // Native (FFI) runtime functions always return raw iterator pointers,
    // never boxed interface values.  Normalizing here eliminates the need
    // for codegen to re-detect this conversion.
    let (compat_ty, vir_ty) = if matches!(&target, CallTarget::Native { .. }) {
        let norm = ctx.normalize_iterator_return(vir_ty);
        (norm, norm)
    } else {
        (compat_ty, vir_ty)
    };

    let result_is_fallible = !ctx.generic && ctx.type_arena.unwrap_fallible(ty).is_some();
    Box::new(VirExpr::Call {
        target,
        args,
        ty: compat_ty,
        vir_ty,
        result_is_fallible,
    })
}

/// Fill missing default arguments for a resolved call.
///
/// When a function has default parameters and the call provides fewer
/// arguments than the function expects, this fills in the missing args
/// by lowering the default expressions from `FunctionDef.param_defaults`.
///
/// Handles two cases:
/// - **Positional calls** (no `resolved_call_args`): appends defaults for
///   the missing trailing slots.
/// - **Named-arg calls** (with `resolved_call_args`): rebuilds the full
///   positional arg list, using the mapping to reorder provided args and
///   filling `None` slots with defaults.
fn fill_default_args(
    callee_sym: vole_identity::Symbol,
    args: &mut Vec<VirRef>,
    call_node_id: vole_identity::NodeId,
    ctx: &mut LoweringCtx<'_>,
) {
    // Resolve the callee symbol to a FunctionId by walking same-module,
    // cross-module, and prelude namespaces.
    let func_id = find_function_id_for_callee(callee_sym, ctx);
    let Some(func_id) = func_id else { return };
    let func_def = ctx.entities.get_function(func_id);
    let expected_params = func_def.signature.params_id.len();

    // Check for named-arg mapping from sema.
    let resolved_call_args = ctx
        .node_map
        .get_resolved_call_args(call_node_id)
        .map(|m| m.to_vec());

    if let Some(mapping) = resolved_call_args {
        // Named-arg reordering (with possible defaults): rebuild the
        // full positional arg list even if all args are provided, since
        // the call-site order may differ from parameter order.
        // mapping[slot] = Some(j) means use the j-th call-site arg;
        // None means use the default expression.
        let original_args = std::mem::take(args);
        for (slot, opt) in mapping.iter().enumerate() {
            if let Some(&call_idx) = opt.as_ref() {
                if call_idx < original_args.len() {
                    // Clone the VirRef (Box<VirExpr>) — each arg is used
                    // at most once in a valid mapping.
                    args.push(original_args[call_idx].clone());
                }
            } else if let Some(Some(default_expr)) = func_def.param_defaults.get(slot)
                && ctx.node_map.get_type(default_expr.id).is_some()
            {
                args.push(lower_expr(default_expr, ctx));
            }
        }
    } else if args.len() < expected_params {
        // Simple positional case: append defaults for the missing
        // trailing slots.
        for slot in args.len()..expected_params {
            if let Some(Some(default_expr)) = func_def.param_defaults.get(slot)
                && ctx.node_map.get_type(default_expr.id).is_some()
            {
                args.push(lower_expr(default_expr, ctx));
            }
        }
    }
}

/// Resolve a callee symbol to a `FunctionId`, searching same-module,
/// cross-module, and prelude namespaces.
///
/// Returns `None` when the symbol doesn't map to a known function.
fn find_function_id_for_callee(
    callee_sym: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> Option<vole_identity::FunctionId> {
    let callee_name = ctx.interner.try_resolve(callee_sym)?;

    // Stage 1: same-module lookup.
    if let Some(name_id) = ctx
        .name_table
        .name_id(ctx.module_id, &[callee_sym], ctx.interner)
        && let Some(func_id) = ctx.entities.function_by_name(name_id)
    {
        return Some(func_id);
    }

    // Stage 2: cross-module lookup via destructured import bindings.
    if let Some(&(source_module_id, _export_sym)) =
        ctx.cross_module.module_bindings.get(&callee_sym)
        && let Some(source_name_id) = ctx.name_table.name_id_raw(source_module_id, &[callee_name])
        && let Some(func_id) = ctx.entities.function_by_name(source_name_id)
    {
        return Some(func_id);
    }

    // Stage 3: prelude module lookup.
    for &prelude_module_id in &ctx.cross_module.prelude_module_ids {
        if let Some(prelude_name_id) = ctx
            .name_table
            .name_id_raw(prelude_module_id, &[callee_name])
            && let Some(func_id) = ctx.entities.function_by_name(prelude_name_id)
        {
            return Some(func_id);
        }
    }

    None
}

/// Try to build a `CallTarget::GenericCall` from the MonomorphKey on a call
/// node.  Returns `None` when the node has no MonomorphKey or when the
/// target function cannot be resolved to a `FunctionId`.
fn generic_call_target(expr: &Expr, ctx: &mut LoweringCtx<'_>) -> Option<CallTarget> {
    let key = ctx.node_map.get_generic(expr.id)?;
    let function_id = ctx.entities.function_by_name(key.func_name)?;
    let type_args: Vec<VirTypeId> = key
        .type_keys
        .iter()
        .map(|&ty| ctx.translate(ty.to_type_id_raw()))
        .collect();
    Some(CallTarget::GenericCall {
        function_id,
        type_args,
    })
}

/// Try to classify a call as a builtin or compiler intrinsic.
///
/// Checks two sources:
/// 1. Hardcoded builtin names (`print_char`, `assert`) that codegen handles
///    with special inline emission.
/// 2. NodeMap `intrinsic_key` set by sema for generic external calls whose
///    type arguments resolve to a concrete intrinsic (e.g. `sqrt(2.0)` ->
///    `f64_sqrt`).  Only used when the call has NO MonomorphKey (which would
///    indicate a generic call needing full monomorphization/ambiguity checking).
///
/// Returns `Some(CallTarget::Intrinsic { key, line })` when the call can be
/// classified, `None` otherwise.
fn resolve_intrinsic_target(
    expr: &Expr,
    callee_sym: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> Option<CallTarget> {
    let line = expr.span.line;
    // 1. Check hardcoded builtins by callee name.
    let callee_name = ctx.interner.try_resolve(callee_sym)?;
    match callee_name {
        "print_char" => {
            return Some(CallTarget::Intrinsic {
                key: IntrinsicKey::PrintChar,
                line,
            });
        }
        "assert" => {
            return Some(CallTarget::Intrinsic {
                key: IntrinsicKey::Assert,
                line,
            });
        }
        _ => {}
    }
    // 2. Check NodeMap for a sema-resolved intrinsic key (generic externals).
    //    Skip when a MonomorphKey is present — that indicates a generic call
    //    that needs the full monomorphization path (which also checks for
    //    ambiguous where-clause mappings).
    if ctx.node_map.get_generic(expr.id).is_some() {
        return None;
    }
    let key_str = ctx.node_map.get_intrinsic_key(expr.id)?;
    let key = IntrinsicKey::try_from_name(key_str)?;
    Some(CallTarget::Intrinsic { key, line })
}

/// Try to classify a call as a closure variable, captured closure, or
/// functional interface call.
///
/// When sema has annotated the call node with `callee_var_type` (indicating
/// the callee is a function-typed or interface-typed variable rather than a
/// declared function), returns the appropriate `CallTarget` variant:
/// - `FunctionalInterface`: callee has a single-method interface type
/// - `CapturedClosure`: callee symbol is in the current function's captures
/// - `ClosureVariable`: callee is a local variable with function type
///
/// Returns `None` when sema did not annotate this call as a variable call.
fn resolve_closure_variable_target(
    call_expr_id: vole_identity::NodeId,
    callee_sym: vole_identity::Symbol,
    resolved_call_args: &Option<Vec<Option<usize>>>,
    lambda_defaults: &Option<LambdaDefaultsInfo>,
    ctx: &mut LoweringCtx<'_>,
) -> Option<CallTarget> {
    let callee_type = ctx.node_map.get_callee_var_type(call_expr_id)?;
    let vir_type = ctx.translate(callee_type);

    // Module-level globals should be handled by `resolve_global_closure_target()`,
    // not classified as local closure variables or functional interfaces.
    let is_global = ctx
        .name_table
        .name_id(ctx.module_id, &[callee_sym], ctx.interner)
        .and_then(|nid| ctx.entities.global_by_name(nid))
        .is_some();
    if is_global {
        return None;
    }

    // Check if the callee is a functional interface (single-method interface).
    // Sema sets callee_var_type to the interface type for these.
    if let Some((type_def_id, _)) = ctx.type_arena.unwrap_interface(callee_type)
        && let Some(method_id) = ctx.entities.is_functional(type_def_id)
    {
        return Some(CallTarget::FunctionalInterface {
            var_name: callee_sym,
            vir_type,
            interface_type_def_id: type_def_id,
            method_id,
        });
    }

    if ctx.captures.contains(&callee_sym) {
        Some(CallTarget::CapturedClosure {
            var_name: callee_sym,
            vir_type,
            resolved_call_args: resolved_call_args.clone(),
            lambda_defaults: *lambda_defaults,
        })
    } else {
        Some(CallTarget::ClosureVariable {
            var_name: callee_sym,
            vir_type,
            resolved_call_args: resolved_call_args.clone(),
            lambda_defaults: *lambda_defaults,
        })
    }
}

/// Try to classify a call as a global closure or global functional interface.
///
/// When the callee symbol maps to a registered global variable (via the
/// entity registry), returns `CallTarget::GlobalClosure`.  Codegen will
/// compile the global's VIR initializer and dispatch as closure or
/// functional interface depending on the global's declared type.
///
/// Returns `None` when the callee is not a global variable.
fn resolve_global_closure_target(
    callee_sym: vole_identity::Symbol,
    resolved_call_args: &Option<Vec<Option<usize>>>,
    lambda_defaults: &Option<LambdaDefaultsInfo>,
    monomorph_key: &Option<MonomorphKey>,
    ctx: &LoweringCtx<'_>,
) -> Option<CallTarget> {
    // Guard: bail if symbol can't be resolved (e.g. UNKNOWN in tests).
    let _callee_name = ctx.interner.try_resolve(callee_sym)?;
    let name_id = ctx
        .name_table
        .name_id(ctx.module_id, &[callee_sym], ctx.interner)?;
    let _global_id = ctx.entities.global_by_name(name_id)?;
    Some(CallTarget::GlobalClosure {
        var_name: callee_sym,
        resolved_call_args: resolved_call_args.clone(),
        lambda_defaults: *lambda_defaults,
        monomorph_key: monomorph_key.clone(),
    })
}

/// Map an AST `UnaryOp` to the VIR `VirUnOp`.
pub fn map_unary_op(op: UnaryOp) -> VirUnOp {
    match op {
        UnaryOp::Neg => VirUnOp::Neg,
        UnaryOp::Not => VirUnOp::Not,
        UnaryOp::BitNot => VirUnOp::BitNot,
    }
}

/// Lower a `when` expression by desugaring to a chain of `VirExpr::If`.
///
/// `when { c1 => r1, c2 => r2, _ => def }` becomes:
///   `if c1 { r1 } else { if c2 { r2 } else { def } }`
///
/// The wildcard arm (condition = None) becomes the innermost else body.
/// Non-wildcard arms form nested if-else chains.
fn lower_when_expr(
    when_expr: &vole_frontend::ast::WhenExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    // Separate conditional arms from the wildcard arm.
    let mut cond_arms: Vec<&vole_frontend::ast::WhenArm> = Vec::new();
    let mut wildcard_arm: Option<&vole_frontend::ast::WhenArm> = None;

    for arm in &when_expr.arms {
        if arm.condition.is_none() {
            wildcard_arm = Some(arm);
        } else {
            cond_arms.push(arm);
        }
    }

    // Build the else body from the wildcard arm (or void if none).
    let else_body = wildcard_arm.map(|arm| {
        let body = lower_expr(&arm.body, ctx);
        VirBody {
            stmts: Vec::new(),
            trailing: Some(body),
        }
    });

    // Build the if-else chain from back to front.
    // Start with the last conditional arm and nest inward.
    let mut result_else = else_body;

    for arm in cond_arms.iter().rev() {
        let cond = lower_expr(
            arm.condition
                .as_ref()
                .expect("INTERNAL: when arm: non-wildcard arm has no condition"),
            ctx,
        );
        let then_val = lower_expr(&arm.body, ctx);
        let then_body = VirBody {
            stmts: Vec::new(),
            trailing: Some(then_val),
        };

        let compat_ty = ctx.compat_ty(ty);
        let vir_ty = ctx.translate(ty);
        result_else = Some(VirBody {
            stmts: Vec::new(),
            trailing: Some(Box::new(VirExpr::If {
                cond,
                then_body,
                else_body: result_else,
                ty: compat_ty,
                vir_ty,
            })),
        });
    }

    // The outermost result is in result_else's trailing expression.
    match result_else {
        Some(body) => body.trailing.expect("INTERNAL: when expr: empty chain"),
        None => {
            // No arms at all (shouldn't happen with well-formed when, but handle gracefully).
            Box::new(VirExpr::NilLiteral)
        }
    }
}

/// Recover the tested type from an `IsCheckResult` and the scrutinee type.
///
/// For monomorphized generic recomputation, codegen needs the tested type to
/// call `compute_is_check_result(value_type, tested_type)` with substituted
/// types. This function recovers the tested type from the IsCheckResult:
/// - `CheckTag(tag)`: the type at union variant index `tag`
/// - `CheckUnknown(ty)`: the type is directly embedded
/// - `AlwaysTrue`: the tested type equals the scrutinee type
/// - `AlwaysFalse`: unrecoverable; uses `VirTypeId::UNKNOWN` as placeholder
pub(super) fn recover_tested_type(
    result: &IsCheckResult,
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirTypeId {
    match result {
        IsCheckResult::CheckTag(tag) => ctx
            .type_arena
            .unwrap_union(scrutinee_ty)
            .and_then(|variants| variants.get(*tag as usize).copied())
            .map(|ty| ctx.translate(ty))
            .unwrap_or(VirTypeId::UNKNOWN),
        IsCheckResult::CheckUnknown(ty, _) => *ty,
        IsCheckResult::AlwaysTrue => ctx.translate(scrutinee_ty),
        IsCheckResult::AlwaysFalse => VirTypeId::UNKNOWN,
    }
}

/// Conservative `it`-usage check for lowering-time reconstruction.
///
/// Guarding on this avoids reconstructing a synthetic `it` lambda from stale
/// `ItLambdaInfo` data that does not actually belong to `arg_expr`.
fn expr_contains_it_for_lower(expr: &Expr, it_sym: vole_identity::Symbol) -> bool {
    match &expr.kind {
        ExprKind::Identifier(sym) => *sym == it_sym,
        ExprKind::Binary(bin) => {
            expr_contains_it_for_lower(&bin.left, it_sym)
                || expr_contains_it_for_lower(&bin.right, it_sym)
        }
        ExprKind::Unary(un) => expr_contains_it_for_lower(&un.operand, it_sym),
        ExprKind::Call(call) => {
            expr_contains_it_for_lower(&call.callee, it_sym)
                || call
                    .args
                    .iter()
                    .any(|a| expr_contains_it_for_lower(a.expr(), it_sym))
        }
        ExprKind::Grouping(inner) => expr_contains_it_for_lower(inner, it_sym),
        ExprKind::Index(idx) => {
            expr_contains_it_for_lower(&idx.object, it_sym)
                || expr_contains_it_for_lower(&idx.index, it_sym)
        }
        ExprKind::ArrayLiteral(elems) => {
            elems.iter().any(|e| expr_contains_it_for_lower(e, it_sym))
        }
        ExprKind::NullCoalesce(nc) => {
            expr_contains_it_for_lower(&nc.value, it_sym)
                || expr_contains_it_for_lower(&nc.default, it_sym)
        }
        ExprKind::Is(is_expr) => expr_contains_it_for_lower(&is_expr.value, it_sym),
        ExprKind::AsCast(as_cast) => expr_contains_it_for_lower(&as_cast.value, it_sym),
        ExprKind::StructLiteral(sl) => sl
            .fields
            .iter()
            .any(|f| expr_contains_it_for_lower(&f.value, it_sym)),
        ExprKind::InterpolatedString(parts) => parts.iter().any(|p| {
            if let StringPart::Expr(e) = p {
                expr_contains_it_for_lower(e, it_sym)
            } else {
                false
            }
        }),
        ExprKind::MethodCall(mc) => {
            expr_contains_it_for_lower(&mc.object, it_sym)
                || mc
                    .args
                    .iter()
                    .any(|a| expr_contains_it_for_lower(a.expr(), it_sym))
        }
        ExprKind::FieldAccess(fa) => expr_contains_it_for_lower(&fa.object, it_sym),
        ExprKind::OptionalChain(oc) => expr_contains_it_for_lower(&oc.object, it_sym),
        ExprKind::OptionalMethodCall(omc) => {
            expr_contains_it_for_lower(&omc.object, it_sym)
                || omc
                    .args
                    .iter()
                    .any(|a| expr_contains_it_for_lower(a.expr(), it_sym))
        }
        ExprKind::Range(r) => {
            expr_contains_it_for_lower(&r.start, it_sym)
                || expr_contains_it_for_lower(&r.end, it_sym)
        }
        ExprKind::Try(inner) => expr_contains_it_for_lower(inner, it_sym),
        ExprKind::Assign(assign) => expr_contains_it_for_lower(&assign.value, it_sym),
        ExprKind::CompoundAssign(ca) => expr_contains_it_for_lower(&ca.value, it_sym),
        ExprKind::Lambda(_) => false,
        _ => false,
    }
}

/// Lower a method/optional-method call argument, handling implicit `it` lambdas.
///
/// When sema has synthesized an implicit `it => expr` lambda for this argument
/// (detectable via `ItLambdaInfo` on the expression's NodeId), the expression
/// is wrapped into a `VirExpr::Lambda` with `it` as the single parameter and
/// the original expression as the body.  Otherwise, the argument is lowered
/// normally via `lower_expr`.
fn lower_call_arg(arg_expr: &Expr, ctx: &mut LoweringCtx<'_>) -> VirRef {
    // Check if sema marked this argument as an implicit `it` lambda.
    let it_info = ctx.node_map.get_it_lambda_info(arg_expr.id).copied();
    if let Some(info) = it_info {
        // Resolve the `it` symbol (must exist -- sema already verified it).
        let Some(it_sym) = ctx.interner.lookup("it") else {
            return lower_expr(arg_expr, ctx);
        };
        if !expr_contains_it_for_lower(arg_expr, it_sym) {
            return lower_expr(arg_expr, ctx);
        }

        // Reconstruct the synthesized lambda function type from the `it` param
        // and return types sema recorded for this argument.
        let param_types: crate::type_arena::TypeIdVec = [info.param_type].into_iter().collect();
        let func_ty = ctx
            .type_arena
            .lookup_function(param_types.clone(), info.return_type, false)
            .or_else(|| {
                ctx.type_arena
                    .lookup_function(param_types, info.return_type, true)
            })
            .or_else(|| ctx.node_map.get_type(arg_expr.id))
            .unwrap_or(TypeId::UNKNOWN);

        // Lower the body expression (the original `it * 2`, `it > 0`, etc.).
        let body_ref = lower_expr(arg_expr, ctx);
        let body = if ctx.type_arena.is_void(info.return_type) {
            // Void return: wrap as a statement body (no trailing expression).
            VirBody {
                stmts: vec![VirStmt::Expr { value: body_ref }],
                trailing: None,
            }
        } else {
            // Non-void: the expression is the trailing return value.
            VirBody {
                stmts: Vec::new(),
                trailing: Some(body_ref),
            }
        };

        // Extract captures from sema's lambda analysis.
        // Capture types are not tracked in sema's Capture struct, so we use
        // TypeId::UNKNOWN / VirTypeId::UNKNOWN as placeholders.
        let captures = ctx
            .node_map
            .get_lambda_analysis(arg_expr.id)
            .map(|analysis| {
                analysis
                    .captures
                    .iter()
                    .map(|c| VirCapture {
                        name: c.name,
                        ty: VirTypeId::UNKNOWN,
                        vir_ty: VirTypeId::UNKNOWN,
                        by_ref: false,
                        rc_kind: VirCaptureRcKind::Unresolved,
                    })
                    .collect()
            })
            .unwrap_or_default();

        let compat_ty = ctx.compat_ty(func_ty);
        let vir_ty = ctx.translate(func_ty);
        return Box::new(VirExpr::Lambda {
            params: vec![it_sym],
            body,
            captures,
            ty: compat_ty,
            vir_ty,
        });
    }

    // No `it` lambda -- lower normally.
    lower_expr(arg_expr, ctx)
}

/// Try to pre-resolve a static method call into a specialized VIR node.
///
/// Returns `Some(VirRef)` for:
/// - Float constants (`f32.nan()`, `f64.infinity()`, etc.) → `FloatLiteral`
/// - `Array.filled<T>(count, value)` → `ArrayFilled`
///
/// Returns `None` for all other static methods (fallback to `MethodCall`).
fn try_lower_static_intrinsic(
    dispatch: &VirMethodDispatchMeta,
    method_sym: vole_identity::Symbol,
    args: &[VirRef],
    compat_ty: VirTypeId,
    vir_ty: VirTypeId,
    ctx: &mut LoweringCtx<'_>,
) -> Option<VirRef> {
    let type_def_id = match &dispatch.resolved_method {
        Some(VirResolvedMethod::Static { type_def_id, .. }) => *type_def_id,
        _ => return None,
    };

    let type_name_id = ctx.entities.name_id(type_def_id);
    let method_name = ctx.interner.resolve(method_sym);

    // Float constants: f32.nan(), f64.infinity(), etc.
    if args.is_empty()
        && let Some(expr) = try_lower_float_constant(type_name_id, method_name, ctx)
    {
        return Some(expr);
    }

    // Array.filled<T>(count, value)
    if args.len() == 2
        && ctx.name_table.last_segment_str(type_name_id).as_deref() == Some("Array")
        && method_name == "filled"
    {
        return try_lower_array_filled(args, compat_ty, vir_ty, ctx);
    }

    None
}

/// Lower a float constant static method (`f32.nan()`, `f64.epsilon()`, etc.)
/// to a `VirExpr::FloatLiteral`.
fn try_lower_float_constant(
    type_name_id: vole_identity::NameId,
    method_name: &str,
    ctx: &LoweringCtx<'_>,
) -> Option<VirRef> {
    let prims = &ctx.name_table.primitives;
    let is_f32 = type_name_id == prims.f32;
    let is_f64 = type_name_id == prims.f64;
    if !is_f32 && !is_f64 {
        return None;
    }

    let (value, ty) = match (method_name, is_f32) {
        ("nan", true) => (f32::NAN as f64, VirTypeId::F32),
        ("nan", false) => (f64::NAN, VirTypeId::F64),
        ("infinity", true) => (f32::INFINITY as f64, VirTypeId::F32),
        ("infinity", false) => (f64::INFINITY, VirTypeId::F64),
        ("neg_infinity", true) => (f32::NEG_INFINITY as f64, VirTypeId::F32),
        ("neg_infinity", false) => (f64::NEG_INFINITY, VirTypeId::F64),
        ("epsilon", true) => (f32::EPSILON as f64, VirTypeId::F32),
        ("epsilon", false) => (f64::EPSILON, VirTypeId::F64),
        _ => return None,
    };

    Some(Box::new(VirExpr::FloatLiteral {
        value,
        ty,
        vir_ty: ty,
    }))
}

/// Lower `Array.filled<T>(count, value)` to `VirExpr::ArrayFilled`.
///
/// The element type is extracted from the return type `[T]` by unwrapping
/// the array wrapper.
fn try_lower_array_filled(
    args: &[VirRef],
    compat_ty: VirTypeId,
    vir_ty: VirTypeId,
    ctx: &mut LoweringCtx<'_>,
) -> Option<VirRef> {
    // Unwrap [T] → T from the return type.
    let elem_type = ctx.type_table.unwrap_array(compat_ty)?;
    let count = args[0].clone();
    let value = args[1].clone();
    Some(Box::new(VirExpr::ArrayFilled {
        count,
        value,
        elem_type,
        ty: compat_ty,
        vir_ty,
    }))
}
