// vir_lower/expr.rs
//
// Expression lowering: AST `Expr` → VIR `VirExpr`.
//
// Includes all expression helpers: literal, binary, unary, control flow, yield.

use vole_frontend::Expr;
use vole_frontend::ast::{BinaryOp, ExprKind, StringPart, UnaryOp};
use vole_identity::{TypeId, VirTypeId};
use vole_sema::{StringConversion, TypeArena};

use vole_vir::calls::CallTarget;
use vole_vir::expr::{
    AsCastKind, FieldStorage, IsCheckResult, VirBinOp, VirCapture, VirErrorFieldBinding,
    VirErrorPatternKind, VirExpr, VirMatchArm, VirMetaKind, VirPattern, VirRecordFieldBinding,
    VirStringPart, VirTupleBinding, VirUnOp,
};
use vole_vir::func::VirBody;
use vole_vir::refs::VirRef;
use vole_vir::stmt::VirStmt;

use super::LoweringCtx;
use super::lower_func_body;
use super::stmt::lower_stmt;

/// Lower an AST expression into a VIR expression.
///
/// All `ExprKind` variants are lowered to concrete `VirExpr` nodes.
/// Grouping parentheses are stripped transparently.
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn lower_expr(expr: &Expr, ctx: &mut LoweringCtx<'_>) -> VirRef {
    // Strip grouping parentheses — lower the inner expression directly.
    if let ExprKind::Grouping(inner) = &expr.kind {
        return lower_expr(inner, ctx);
    }

    let ty = ctx.node_map.get_type(expr.id).unwrap_or(TypeId::UNKNOWN);
    match &expr.kind {
        ExprKind::IntLiteral(value, _suffix) => lower_int_literal(*value, ty, ctx),
        ExprKind::FloatLiteral(value, _suffix) => {
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::FloatLiteral {
                value: *value,
                ty,
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
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::Import { ty, vir_ty })
        }
        ExprKind::TypeLiteral(_) => Box::new(VirExpr::TypeLiteral),
        ExprKind::Range(range_expr) => lower_range(range_expr, ctx),
        ExprKind::Identifier(sym) => {
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::LocalLoad {
                name: *sym,
                ty,
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
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::MethodCall {
                receiver,
                method: mc.method,
                args,
                node_id: expr.id,
                ty,
                vir_ty,
            })
        }
        ExprKind::RepeatLiteral { element, count } => {
            let elem = lower_expr(element, ctx);
            let vir_ty = ctx.translate(ty);
            Box::new(VirExpr::RepeatLiteral {
                element: elem,
                count: *count,
                ty,
                vir_ty,
            })
        }
    }
}

/// Lower an integer literal, splitting into `WideLiteral` for i128/f128.
fn lower_int_literal(value: i64, ty: TypeId, ctx: &mut LoweringCtx<'_>) -> VirRef {
    let vir_ty = ctx.translate(ty);
    if ty == TypeId::F128 {
        // Integer promoted to f128: convert to f64 first to get a float
        // bit-pattern, then store as the low 64 bits of a wide literal.
        // The high 64 bits are zero so the i128→f128 bitcast in codegen
        // reproduces the same representation as the old int_const(n, f128)
        // path (f64 bits in the low half, zero-extended).
        let f64_bits = (value as f64).to_bits();
        Box::new(VirExpr::WideLiteral {
            low: f64_bits,
            high: 0,
            ty,
            vir_ty,
        })
    } else if ty == TypeId::I128 {
        // Sign-extend i64 to i128 then split into low/high u64.
        let wide = value as i128;
        Box::new(VirExpr::WideLiteral {
            low: wide as u64,
            high: (wide >> 64) as u64,
            ty,
            vir_ty,
        })
    } else {
        Box::new(VirExpr::IntLiteral { value, ty, vir_ty })
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
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::BinaryOp {
        op: vir_op,
        lhs,
        rhs,
        ty,
        vir_ty,
        line: expr.span.line,
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
        ty,
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
        ty,
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
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::UnaryOp {
        op: vir_op,
        operand,
        ty,
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
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::If {
        cond,
        then_body,
        else_body,
        ty,
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
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Block {
        stmts,
        trailing,
        ty,
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
            let obj = lower_expr(object, ctx);
            let value = lower_expr(&assign_expr.value, ctx);
            Box::new(VirExpr::FieldStore {
                object: obj,
                field: *field,
                storage: FieldStorage::ByName,
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

    let vir_ty = ctx.translate(ty);

    match &compound.target {
        vole_frontend::AssignTarget::Variable(sym) => {
            let load = Box::new(VirExpr::LocalLoad {
                name: *sym,
                ty,
                vir_ty,
            });
            let binop_result = Box::new(VirExpr::BinaryOp {
                op: binary_op,
                lhs: load,
                rhs,
                ty,
                vir_ty,
                line: expr.span.line,
            });
            Box::new(VirExpr::LocalStore {
                name: *sym,
                value: binop_result,
            })
        }
        vole_frontend::AssignTarget::Field { object, field, .. } => {
            let obj_for_load = lower_expr(object, ctx);
            let obj_for_store = lower_expr(object, ctx);
            let load = Box::new(VirExpr::FieldLoad {
                object: obj_for_load,
                field: *field,
                storage: FieldStorage::ByName,
                ty,
                vir_ty,
            });
            let binop_result = Box::new(VirExpr::BinaryOp {
                op: binary_op,
                lhs: load,
                rhs,
                ty,
                vir_ty,
                line: expr.span.line,
            });
            Box::new(VirExpr::FieldStore {
                object: obj_for_store,
                field: *field,
                storage: FieldStorage::ByName,
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
                ty,
                vir_ty,
                union_storage,
            });
            let binop_result = Box::new(VirExpr::BinaryOp {
                op: binary_op,
                lhs: load,
                rhs,
                ty,
                vir_ty,
                line: expr.span.line,
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
/// The object sub-expression is recursively lowered.  Storage resolution
/// (`Direct` vs `Heap`) is deferred to codegen via `FieldStorage::ByName`
/// because field layout is not yet resolved during lowering.
fn lower_field_access(
    fa: &vole_frontend::ast::FieldAccessExpr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let object = lower_expr(&fa.object, ctx);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::FieldLoad {
        object,
        field: fa.field,
        storage: FieldStorage::ByName,
        ty,
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
    let sema_result = ctx
        .node_map
        .get_is_check_result(expr.id)
        .unwrap_or_else(|| {
            panic!(
                "VIR lower: missing sema is_check_result for NodeId {:?} (line {})",
                expr.id, expr.span.line
            )
        });
    let value = lower_expr(&is_expr.value, ctx);
    let vir_result = convert_is_check_result(sema_result, ctx);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::IsCheck {
        value,
        result: vir_result,
        ty,
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
    let sema_result = ctx
        .node_map
        .get_is_check_result(expr.id)
        .unwrap_or_else(|| {
            panic!(
                "VIR lower: missing sema is_check_result for as_cast NodeId {:?} (line {})",
                expr.id, expr.span.line
            )
        });
    let value = lower_expr(&as_cast.value, ctx);
    let kind = match as_cast.kind {
        vole_frontend::ast::AsCastKind::Safe => AsCastKind::Checked,
        vole_frontend::ast::AsCastKind::Unsafe => AsCastKind::Unchecked,
    };
    let vir_result = convert_is_check_result(sema_result, ctx);
    let vir_target_ty = ctx.translate(ty);
    Box::new(VirExpr::AsCast {
        value,
        target_ty: ty,
        vir_target_ty,
        kind,
        result: vir_result,
    })
}

/// Convert sema's `IsCheckResult` to VIR's `IsCheckResult`.
///
/// VIR defines its own copy of this enum to avoid circular dependencies
/// and keep the VIR crate dependency-light.
fn convert_is_check_result(
    sema: vole_sema::IsCheckResult,
    ctx: &mut LoweringCtx<'_>,
) -> IsCheckResult {
    match sema {
        vole_sema::IsCheckResult::AlwaysTrue => IsCheckResult::AlwaysTrue,
        vole_sema::IsCheckResult::AlwaysFalse => IsCheckResult::AlwaysFalse,
        vole_sema::IsCheckResult::CheckTag(tag) => IsCheckResult::CheckTag(tag),
        vole_sema::IsCheckResult::CheckUnknown(ty) => {
            let vir_ty = ctx.translate(ty);
            IsCheckResult::CheckUnknown(ty, vir_ty)
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
                let conversion = ctx
                    .node_map
                    .get_string_conversion(expr.id)
                    .cloned()
                    .unwrap_or(StringConversion::Identity);
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
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Index {
        object,
        index,
        ty,
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
    use vole_sema::node_map::MetaAccessKind;

    let Some(meta_kind) = ctx.node_map.get_meta_access(expr.id) else {
        panic!(
            "VIR lower: missing sema meta_access for NodeId {:?} (line {})",
            expr.id, expr.span.line
        )
    };

    let kind = match meta_kind {
        MetaAccessKind::Static { type_def_id } => {
            // Determine whether this is a type-name access (no object needed)
            // or a value-expression access (object needed for re-derivation).
            #[allow(clippy::wildcard_enum_match_arm)] // AST ExprKind, not VIR dispatch
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

    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::MetaAccess { kind, ty, vir_ty })
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
    let body = lower_func_body(&lambda.body, ctx);

    // Extract captures from sema's lambda analysis.
    // Capture types are not tracked in sema's Capture struct, so we use
    // TypeId::UNKNOWN / VirTypeId::UNKNOWN as placeholders.
    let captures = ctx
        .node_map
        .get_lambda_analysis(expr.id)
        .map(|analysis| {
            analysis
                .captures
                .iter()
                .map(|c| VirCapture {
                    name: c.name,
                    ty: TypeId::UNKNOWN,
                    vir_ty: VirTypeId::UNKNOWN,
                    by_ref: false,
                })
                .collect()
        })
        .unwrap_or_default();

    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Lambda {
        params,
        body,
        captures,
        ty,
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
        inner_type,
        vir_inner_type,
        ty: inner_type,
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
    let info = ctx.node_map.get_optional_chain(expr.id).unwrap_or_else(|| {
        panic!(
            "VIR lower: missing sema optional_chain for NodeId {:?} (line {})",
            expr.id, expr.span.line
        )
    });
    let object = lower_expr(&oc.object, ctx);
    let vir_inner_type = ctx.translate(info.inner_type);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::OptionalChain {
        object,
        field: oc.field,
        inner_type: info.inner_type,
        vir_inner_type,
        ty,
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
    let info = ctx.node_map.get_optional_chain(expr.id).unwrap_or_else(|| {
        panic!(
            "VIR lower: missing sema optional_chain for optional_method_call NodeId {:?} (line {})",
            expr.id, expr.span.line
        )
    });
    let object = lower_expr(&omc.object, ctx);
    let method_args: Vec<VirRef> = omc
        .args
        .iter()
        .map(|a| lower_call_arg(a.expr(), ctx))
        .collect();
    let vir_inner_type = ctx.translate(info.inner_type);
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::OptionalMethodCall {
        object,
        method: omc.method,
        method_args,
        call_node_id: expr.id,
        inner_type: info.inner_type,
        vir_inner_type,
        ty,
        vir_ty,
    })
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
        success_type: ty,
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
    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::ArrayLiteral {
        elements: lowered,
        ty,
        vir_ty,
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
    let info = ctx
        .node_map
        .get_struct_literal_info(expr.id)
        .unwrap_or_else(|| {
            panic!(
                "VIR lower: missing sema struct_literal_info for NodeId {:?} (line {})",
                expr.id, expr.span.line
            )
        });

    let fields: Vec<(vole_identity::Symbol, VirRef)> = sl
        .fields
        .iter()
        .map(|f| (f.name, lower_expr(&f.value, ctx)))
        .collect();

    let vir_ty = ctx.translate(ty);
    if info.is_class {
        Box::new(VirExpr::ClassInstance {
            type_def: info.type_def_id,
            fields,
            ty,
            vir_ty,
        })
    } else {
        Box::new(VirExpr::StructLiteral {
            type_def: info.type_def_id,
            fields,
            ty,
            vir_ty,
        })
    }
}

/// Lower a call expression to `VirExpr::Call`.
///
/// Call dispatch is complex because sema does not annotate a "call dispatch
/// kind" on Call nodes.  The full 15+ path dispatch requires the function
/// registry, variable table, and module context — none of which are available
/// during lowering.
///
/// The lowering emits `CallTarget::Unresolved` which carries the callee
/// symbol, call NodeId, and source line.  Codegen's `call_dispatch()` uses
/// these plus the VIR-lowered `args` (compiled via `ArgSource::Vir`) to
/// perform the full 15+ path dispatch.
///
/// **Indirect calls** (non-identifier callee, e.g. `array[0]()`) are lowered
/// as `CallTarget::Lambda` with the callee prepended as the first arg.
/// Codegen's `compile_vir_lambda_call` handles these directly, so they bypass
/// the `call_dispatch()` dispatcher entirely.
///
/// Over time, specific call patterns will be promoted from Unresolved to
/// concrete `CallTarget` variants (Direct, Lambda, Intrinsic, etc.) as sema
/// gains call classification annotations.
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
        let vir_ty = ctx.translate(ty);
        return Box::new(VirExpr::Call {
            target: CallTarget::Lambda,
            args,
            ty,
            vir_ty,
        });
    }

    // Extract the callee symbol from the identifier expression.
    let callee_sym = match &call_expr.callee.kind {
        ExprKind::Identifier(sym) => *sym,
        _ => unreachable!("non-identifier callee handled above"),
    };

    // Lower argument expressions to VIR, handling implicit `it` lambdas.
    let args: Vec<VirRef> = call_expr
        .args
        .iter()
        .map(|arg| lower_call_arg(arg.expr(), ctx))
        .collect();

    let target = CallTarget::Unresolved {
        callee_sym,
        call_node_id: expr.id,
        line: expr.span.line,
    };

    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Call {
        target,
        args,
        ty,
        vir_ty,
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

        let vir_ty = ctx.translate(ty);
        result_else = Some(VirBody {
            stmts: Vec::new(),
            trailing: Some(Box::new(VirExpr::If {
                cond,
                then_body,
                else_body: result_else,
                ty,
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

/// Lower a `match` expression to `VirExpr::Match`.
///
/// The scrutinee is recursively lowered. All patterns are lowered to
/// concrete `VirPattern` variants (Wildcard, Binding, TypeCheck, Literal,
/// Val, Success, Error, Tuple, Record). Guards and bodies are recursively
/// lowered.
fn lower_match_expr(
    match_expr: &vole_frontend::ast::MatchExpr,
    _expr: &Expr,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirRef {
    let scrutinee = lower_expr(&match_expr.scrutinee, ctx);
    let scrutinee_ty = ctx
        .node_map
        .get_type(match_expr.scrutinee.id)
        .unwrap_or(TypeId::UNKNOWN);

    let arms: Vec<VirMatchArm> = match_expr
        .arms
        .iter()
        .map(|arm| {
            let pattern = lower_pattern(&arm.pattern, scrutinee_ty, ctx);
            let guard = arm.guard.as_ref().map(|g| lower_expr(g, ctx));
            let body_ref = lower_expr(&arm.body, ctx);
            let arm_ty = ctx
                .node_map
                .get_type(arm.body.id)
                .unwrap_or(TypeId::UNKNOWN);
            let vir_ty = ctx.translate(arm_ty);
            VirMatchArm {
                pattern,
                guard,
                body: VirBody {
                    stmts: Vec::new(),
                    trailing: Some(body_ref),
                },
                ty: arm_ty,
                vir_ty,
            }
        })
        .collect();

    let vir_ty = ctx.translate(ty);
    Box::new(VirExpr::Match {
        scrutinee,
        arms,
        ty,
        vir_ty,
    })
}

/// Lower an AST `Pattern` to a `VirPattern`.
///
/// All pattern kinds are lowered to concrete VIR variants:
/// - `Wildcard` -> `VirPattern::Wildcard`
/// - `Identifier` with sema `IsCheckResult` -> `VirPattern::TypeCheck`
/// - `Identifier` without `IsCheckResult` -> `VirPattern::Binding`
/// - `Type { .. }` -> `VirPattern::TypeCheck`
/// - `Literal(..)` -> `VirPattern::Literal`
/// - `Val { .. }` -> `VirPattern::Val`
/// - `Success { .. }` -> `VirPattern::Success`
/// - `Error { .. }` -> `VirPattern::Error`
/// - `Tuple { .. }` -> `VirPattern::Tuple`
/// - `Record { .. }` -> `VirPattern::Record`
fn lower_pattern(
    pattern: &vole_frontend::Pattern,
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    use vole_frontend::PatternKind;

    match &pattern.kind {
        PatternKind::Wildcard => VirPattern::Wildcard,

        PatternKind::Identifier { name } => {
            // Sema records IsCheckResult on the pattern's NodeId when the
            // identifier resolves to a type name. Its absence means a
            // plain variable binding.
            if let Some(sema_result) = ctx.node_map.get_is_check_result(pattern.id) {
                let result = convert_is_check_result(sema_result, ctx);
                let tested_type = recover_tested_type(&result, scrutinee_ty, ctx.type_arena);
                let vir_tested_type = ctx.translate(tested_type);
                VirPattern::TypeCheck {
                    result,
                    tested_type,
                    vir_tested_type,
                    binding: None,
                }
            } else {
                let vir_ty = ctx.translate(scrutinee_ty);
                VirPattern::Binding {
                    name: *name,
                    ty: scrutinee_ty,
                    vir_ty,
                }
            }
        }

        PatternKind::Type { .. } => {
            let sema_result = ctx
                .node_map
                .get_is_check_result(pattern.id)
                .unwrap_or_else(|| {
                    panic!(
                        "VIR lower: missing sema is_check_result for Type pattern NodeId {:?}",
                        pattern.id
                    )
                });
            let result = convert_is_check_result(sema_result, ctx);
            let tested_type = recover_tested_type(&result, scrutinee_ty, ctx.type_arena);
            let vir_tested_type = ctx.translate(tested_type);
            VirPattern::TypeCheck {
                result,
                tested_type,
                vir_tested_type,
                binding: None,
            }
        }

        PatternKind::Literal(lit_expr) => {
            let value = lower_expr(lit_expr, ctx);
            let vir_scrutinee_ty = ctx.translate(scrutinee_ty);
            VirPattern::Literal {
                value,
                scrutinee_ty,
                vir_scrutinee_ty,
            }
        }

        PatternKind::Val { name } => VirPattern::Val { name: *name },

        PatternKind::Success { inner } => lower_success_pattern(inner, scrutinee_ty, ctx),

        PatternKind::Error { inner } => lower_error_pattern(inner, scrutinee_ty, ctx),

        PatternKind::Tuple { elements } => lower_tuple_pattern(elements, scrutinee_ty, ctx),

        PatternKind::Record { type_name, fields } => {
            lower_record_pattern(pattern, type_name.as_ref(), fields, scrutinee_ty, ctx)
        }
    }
}

/// Lower a `success` pattern to `VirPattern::Success`.
///
/// Pre-resolves the success type from `TypeArena::unwrap_fallible`.
/// If an inner pattern is present, it is recursively lowered with the
/// success type as the new scrutinee type.
fn lower_success_pattern(
    inner: &Option<Box<vole_frontend::Pattern>>,
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    let fallible = ctx.type_arena.unwrap_fallible(scrutinee_ty);
    let success_type = fallible.map(|(s, _)| s).unwrap_or(TypeId::UNKNOWN);

    let inner_pat = inner.as_ref().map(|pat| {
        let lowered = lower_pattern(pat, success_type, ctx);
        Box::new(lowered)
    });

    let vir_success_type = ctx.translate(success_type);
    VirPattern::Success {
        inner: inner_pat,
        success_type,
        vir_success_type,
    }
}

/// Lower an `error` pattern to `VirPattern::Error`.
///
/// Classifies the error sub-pattern into one of four kinds:
/// - Bare `error`: no inner pattern
/// - Catch-all `error e`: identifier not matching an error type
/// - Specific `error DivByZero`: identifier matching an error type
/// - Record `error DivByZero { msg }`: error type with field destructuring
fn lower_error_pattern(
    inner: &Option<Box<vole_frontend::Pattern>>,
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    use vole_frontend::PatternKind;

    let Some(inner_pat) = inner else {
        return VirPattern::Error {
            kind: VirErrorPatternKind::Bare,
        };
    };

    match &inner_pat.kind {
        PatternKind::Identifier { name } => {
            lower_error_identifier_pattern(*name, scrutinee_ty, ctx)
        }
        PatternKind::Record {
            type_name: Some(type_expr),
            fields,
        } => lower_error_record_pattern(type_expr, fields, scrutinee_ty, ctx),
        // Other inner patterns (wildcard, etc.) → bare error match
        _ => VirPattern::Error {
            kind: VirErrorPatternKind::Bare,
        },
    }
}

/// Lower a tuple destructuring pattern to `VirPattern::Tuple`.
///
/// Pre-resolves element types from `TypeArena::unwrap_tuple(scrutinee_ty)`.
/// Each element pattern is recursively lowered with the corresponding
/// element type as the new scrutinee type.  If the scrutinee type is not
/// a tuple (or element count mismatches), element types fall back to
/// `TypeId::UNKNOWN`.
fn lower_tuple_pattern(
    elements: &[vole_frontend::Pattern],
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    let elem_types = ctx.type_arena.unwrap_tuple(scrutinee_ty).cloned();

    let bindings: Vec<VirTupleBinding> = elements
        .iter()
        .enumerate()
        .map(|(i, pat)| {
            let elem_ty = elem_types
                .as_ref()
                .and_then(|types| types.get(i).copied())
                .unwrap_or(TypeId::UNKNOWN);
            let inner = lower_pattern(pat, elem_ty, ctx);
            let vir_ty = ctx.translate(elem_ty);
            VirTupleBinding {
                pattern: inner,
                element_index: i,
                ty: elem_ty,
                vir_ty,
            }
        })
        .collect();

    VirPattern::Tuple { bindings }
}

/// Lower an identifier inside an `error` pattern.
///
/// Determines whether the identifier is an error type name (→ Specific)
/// or a catch-all binding (→ CatchAll) by checking the fallible's error
/// union for a matching error type name.
fn lower_error_identifier_pattern(
    name: vole_identity::Symbol,
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    let fallible = ctx.type_arena.unwrap_fallible(scrutinee_ty);
    let error_tag = fallible.and_then(|(_, error_ty)| compute_error_tag(error_ty, name, ctx));

    if let Some(tag) = error_tag {
        // Identifier matches an error type → specific error pattern
        VirPattern::Error {
            kind: VirErrorPatternKind::Specific { error_tag: tag },
        }
    } else {
        // Identifier is a catch-all binding (error e => ...)
        let error_ty = fallible.map(|(_, e)| e).unwrap_or(TypeId::UNKNOWN);
        let vir_error_ty = ctx.translate(error_ty);
        VirPattern::Error {
            kind: VirErrorPatternKind::CatchAll {
                name,
                error_ty,
                vir_error_ty,
            },
        }
    }
}

/// Lower a record pattern inside an `error` pattern.
///
/// Resolves the error type's tag and TypeDefId, then extracts field
/// bindings for the destructure.
fn lower_error_record_pattern(
    type_expr: &vole_frontend::TypeExpr,
    fields: &[vole_frontend::ast::RecordFieldPattern],
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    use vole_frontend::TypeExprKind;

    let type_name_sym = match &type_expr.kind {
        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => Some(*sym),
        TypeExprKind::QualifiedPath { segments, .. } => segments.last().copied(),
        _ => None,
    };

    let Some(name) = type_name_sym else {
        return VirPattern::Error {
            kind: VirErrorPatternKind::Bare,
        };
    };

    let fallible = ctx.type_arena.unwrap_fallible(scrutinee_ty);
    let error_tag = fallible.and_then(|(_, error_ty)| compute_error_tag(error_ty, name, ctx));

    let type_def = fallible.and_then(|(_, error_ty)| find_error_type_def(error_ty, name, ctx));

    match (error_tag, type_def) {
        (Some(tag), Some(def_id)) => {
            let vir_fields: Vec<VirErrorFieldBinding> = fields
                .iter()
                .map(|f| VirErrorFieldBinding {
                    field_name: f.field_name,
                    binding: f.binding,
                })
                .collect();
            VirPattern::Error {
                kind: VirErrorPatternKind::SpecificRecord {
                    error_tag: tag,
                    type_def: def_id,
                    fields: vir_fields,
                },
            }
        }
        _ => VirPattern::Error {
            kind: VirErrorPatternKind::Bare,
        },
    }
}

/// Compute the numeric error tag for a named error type within a fallible's
/// error union.
///
/// Mirrors `fallible_error_tag_by_id` from codegen, using the lowering
/// context's `TypeArena`, `Interner`, `NameTable`, and `EntityRegistry`.
fn compute_error_tag(
    error_type_id: TypeId,
    error_name: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> Option<i64> {
    let error_name_str = ctx.interner.resolve(error_name);

    // Check if error_type_id is a single Error type
    if let Some(type_def_id) = ctx.type_arena.unwrap_error(error_type_id) {
        let info_name = ctx
            .name_table
            .last_segment_str(ctx.entities.name_id(type_def_id));
        if info_name.as_deref() == Some(error_name_str) {
            return Some(1); // Single error type always gets tag 1
        }
        return None;
    }

    // Check if error_type_id is a Union of error types
    if let Some(variants) = ctx.type_arena.unwrap_union(error_type_id) {
        for (idx, &variant) in variants.iter().enumerate() {
            if let Some(type_def_id) = ctx.type_arena.unwrap_error(variant) {
                let info_name = ctx
                    .name_table
                    .last_segment_str(ctx.entities.name_id(type_def_id));
                if info_name.as_deref() == Some(error_name_str) {
                    return Some((idx + 1) as i64);
                }
            }
        }
        return None;
    }

    None
}

/// Find the `TypeDefId` for a named error type in a fallible's error union.
///
/// Used for record destructuring patterns where codegen needs the TypeDefId
/// to look up field layout.
fn find_error_type_def(
    error_type_id: TypeId,
    error_name: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> Option<vole_identity::TypeDefId> {
    let error_name_str = ctx.interner.resolve(error_name);

    // Single error type
    if let Some(type_def_id) = ctx.type_arena.unwrap_error(error_type_id) {
        let info_name = ctx
            .name_table
            .last_segment_str(ctx.entities.name_id(type_def_id));
        if info_name.as_deref() == Some(error_name_str) {
            return Some(type_def_id);
        }
        return None;
    }

    // Union of error types
    if let Some(variants) = ctx.type_arena.unwrap_union(error_type_id) {
        for &variant in variants {
            if let Some(type_def_id) = ctx.type_arena.unwrap_error(variant) {
                let info_name = ctx
                    .name_table
                    .last_segment_str(ctx.entities.name_id(type_def_id));
                if info_name.as_deref() == Some(error_name_str) {
                    return Some(type_def_id);
                }
            }
        }
    }

    None
}

/// Lower a record destructuring pattern to `VirPattern::Record`.
///
/// Pre-resolves:
/// - `IsCheckResult` from the NodeMap (for typed patterns like `Point { x, y }`)
/// - `source_ty`: the narrowed record type after union payload extraction
/// - `is_union_payload`: whether the scrutinee is a union
/// - `is_struct`: whether the source type is a value-type struct
/// - Field slots and types from `EntityRegistry`
fn lower_record_pattern(
    pattern: &vole_frontend::Pattern,
    type_name: Option<&vole_frontend::TypeExpr>,
    fields: &[vole_frontend::ast::RecordFieldPattern],
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    // Typed record pattern: look up IsCheckResult and derive source_ty
    let (type_check, tested_type, source_ty) = if type_name.is_some() {
        let sema_result = ctx.node_map.get_is_check_result(pattern.id);
        let (check, tested) = match sema_result {
            Some(sr) => {
                let check = convert_is_check_result(sr, ctx);
                let tested = recover_tested_type(&check, scrutinee_ty, ctx.type_arena);
                (Some(check), Some(tested))
            }
            None => (None, None),
        };
        // source_ty is the narrowed variant type (if typed union record) or scrutinee
        let src = record_source_type(&check, scrutinee_ty, ctx);
        (check, tested, src)
    } else {
        // Anonymous record: no type check, use scrutinee type directly
        (None, None, scrutinee_ty)
    };

    let is_union = ctx.type_arena.is_union(scrutinee_ty);
    let is_union_payload = is_union && type_check.is_some();
    let is_struct = ctx.type_arena.is_struct(source_ty);

    // Resolve field bindings from EntityRegistry
    let vir_fields = resolve_record_field_bindings(fields, source_ty, ctx);

    let vir_tested_type = tested_type.map(|t| ctx.translate(t));
    let vir_source_ty = ctx.translate(source_ty);

    VirPattern::Record {
        type_check,
        tested_type,
        vir_tested_type,
        fields: vir_fields,
        source_ty,
        vir_source_ty,
        is_union_payload,
        is_struct,
    }
}

/// Determine the source type for a record pattern's field extraction.
///
/// For typed patterns in a union scrutinee, the source is the narrowed variant type.
/// Falls back to the scrutinee type if no narrowing is available.
fn record_source_type(
    check: &Option<IsCheckResult>,
    scrutinee_ty: TypeId,
    ctx: &LoweringCtx<'_>,
) -> TypeId {
    if let Some(result) = check {
        match result {
            IsCheckResult::CheckTag(tag) => {
                if let Some(variants) = ctx.type_arena.unwrap_union(scrutinee_ty)
                    && let Some(&variant) = variants.get(*tag as usize)
                    && is_record_type(variant, ctx.type_arena)
                {
                    return variant;
                }
            }
            IsCheckResult::AlwaysTrue => {
                if is_record_type(scrutinee_ty, ctx.type_arena) {
                    return scrutinee_ty;
                }
            }
            IsCheckResult::AlwaysFalse | IsCheckResult::CheckUnknown(..) => {}
        }
    }
    scrutinee_ty
}

/// Check whether a type is a class, struct, or error type (i.e. a record type).
fn is_record_type(ty: TypeId, arena: &TypeArena) -> bool {
    arena.unwrap_nominal(ty).is_some_and(|(_, _, kind)| {
        kind.is_class_or_struct() || matches!(kind, vole_sema::type_arena::NominalKind::Error)
    })
}

/// Resolve record field bindings from the EntityRegistry.
///
/// For each field in the pattern, looks up the field's slot index and type
/// from the type definition.  Falls back to slot=0 and ty=UNKNOWN if the
/// source type is not a nominal type or the field is not found.
fn resolve_record_field_bindings(
    fields: &[vole_frontend::ast::RecordFieldPattern],
    source_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> Vec<VirRecordFieldBinding> {
    let type_def_id = ctx
        .type_arena
        .unwrap_nominal(source_ty)
        .map(|(def_id, _, _)| def_id);

    fields
        .iter()
        .map(|f| {
            let (slot, ty) = type_def_id
                .and_then(|def_id| find_field_slot(def_id, f.field_name, ctx))
                .unwrap_or((0, TypeId::UNKNOWN));
            let vir_ty = ctx.translate(ty);
            VirRecordFieldBinding {
                field_name: f.field_name,
                binding_name: f.binding,
                field_slot: slot as u32,
                ty,
                vir_ty,
            }
        })
        .collect()
}

/// Find a field's slot index and type in a type definition.
fn find_field_slot(
    type_def_id: vole_identity::TypeDefId,
    field_name: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> Option<(usize, TypeId)> {
    let field_name_str = ctx.interner.resolve(field_name);
    for field_id in ctx.entities.fields_on_type(type_def_id) {
        let field = ctx.entities.get_field(field_id);
        let name = ctx.name_table.last_segment_str(field.name_id);
        if name.as_deref() == Some(field_name_str) {
            return Some((field.slot, field.ty));
        }
    }
    None
}

/// Recover the tested type from an `IsCheckResult` and the scrutinee type.
///
/// For monomorphized generic recomputation, codegen needs the tested type to
/// call `compute_is_check_result(value_type, tested_type)` with substituted
/// types. This function recovers the tested type from the IsCheckResult:
/// - `CheckTag(tag)`: the type at union variant index `tag`
/// - `CheckUnknown(ty)`: the type is directly embedded
/// - `AlwaysTrue`: the tested type equals the scrutinee type
/// - `AlwaysFalse`: unrecoverable; uses `TypeId::UNKNOWN` as placeholder
fn recover_tested_type(
    result: &IsCheckResult,
    scrutinee_ty: TypeId,
    type_arena: &TypeArena,
) -> TypeId {
    match result {
        IsCheckResult::CheckTag(tag) => type_arena
            .unwrap_union(scrutinee_ty)
            .and_then(|variants| variants.get(*tag as usize).copied())
            .unwrap_or(TypeId::UNKNOWN),
        IsCheckResult::CheckUnknown(ty, _) => *ty,
        IsCheckResult::AlwaysTrue => scrutinee_ty,
        IsCheckResult::AlwaysFalse => TypeId::UNKNOWN,
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
        // Resolve the `it` symbol (must exist — sema already verified it).
        let it_sym = ctx
            .interner
            .lookup("it")
            .expect("VIR lower: `it` symbol must be interned for it-lambda");

        // The function type for the synthesized lambda is the type sema assigned
        // to this expression node (e.g. `(i64) -> i64`).
        let func_ty = ctx
            .node_map
            .get_type(arg_expr.id)
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
                        ty: TypeId::UNKNOWN,
                        vir_ty: VirTypeId::UNKNOWN,
                        by_ref: false,
                    })
                    .collect()
            })
            .unwrap_or_default();

        let vir_ty = ctx.translate(func_ty);
        return Box::new(VirExpr::Lambda {
            params: vec![it_sym],
            body,
            captures,
            ty: func_ty,
            vir_ty,
        });
    }

    // No `it` lambda — lower normally.
    lower_expr(arg_expr, ctx)
}
