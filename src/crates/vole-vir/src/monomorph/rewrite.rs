// rewrite.rs
//
// VIR tree rewrite: clone a VirFunction body and remap all VirTypeId fields
// using the type mapping produced by `substitute_types`.
//
// This is the second step of monomorphization. After `substitute_types` builds
// the old->new VirTypeId mapping, `rewrite_function` walks the tree and applies
// it to every VirTypeId field.

use rustc_hash::FxHashMap;
use vole_identity::VirTypeId;

use crate::calls::CallTarget;
use crate::expr::{
    CoerceKind, ComparisonHint, IsCheckResult, VirCapture, VirErrorPatternKind, VirExpr,
    VirMatchArm, VirMetaKind, VirMethodDispatchMeta, VirPattern, VirRecordFieldBinding,
    VirStringPart, VirTupleBinding,
};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::{
    DestructureTupleKind, LetStorageHint, UnionTagHint, VirDestructureElement, VirDestructureField,
    VirDestructurePattern, VirFor, VirIterKind, VirModuleBinding, VirStmt,
};

/// Remap context carrying old->new VirTypeId mapping.
///
/// All VirTypeId fields are remapped during rewrite.
pub struct RewriteCtx {
    vir_type_map: FxHashMap<VirTypeId, VirTypeId>,
}

impl RewriteCtx {
    /// Create a new rewrite context from a VirTypeId mapping.
    pub fn new(vir_type_map: FxHashMap<VirTypeId, VirTypeId>) -> Self {
        Self { vir_type_map }
    }

    /// Look up a VirTypeId in the mapping, falling back to identity.
    fn remap(&self, vir_ty: VirTypeId) -> VirTypeId {
        self.vir_type_map.get(&vir_ty).copied().unwrap_or(vir_ty)
    }
}

/// Clone a VirFunction body with all VirTypeId fields remapped.
pub fn rewrite_function(func: &VirFunction, ctx: &RewriteCtx) -> VirFunction {
    let params = func
        .params
        .iter()
        .map(|(sym, ty, vir_ty)| (*sym, ctx.remap(*ty), ctx.remap(*vir_ty)))
        .collect();

    VirFunction {
        id: func.id,
        name: func.name.clone(),
        params,
        return_type: ctx.remap(func.return_type),
        vir_return_type: ctx.remap(func.vir_return_type),
        // Carry forward the template's return_abi; rederive_decisions will
        // recompute it from the now-concrete vir_return_type.
        return_abi: func.return_abi,
        body: rewrite_body(&func.body, ctx),
        mangled_name_id: func.mangled_name_id,
        method_id: func.method_id,
        type_params: func.type_params.clone(),
    }
}

/// Rewrite a VirBody (statement list + optional trailing expression).
fn rewrite_body(body: &VirBody, ctx: &RewriteCtx) -> VirBody {
    VirBody {
        stmts: body.stmts.iter().map(|s| rewrite_stmt(s, ctx)).collect(),
        trailing: body.trailing.as_ref().map(|r| rewrite_ref(r, ctx)),
    }
}

/// Rewrite a boxed VirExpr reference.
fn rewrite_ref(r: &VirRef, ctx: &RewriteCtx) -> VirRef {
    Box::new(rewrite_expr(r, ctx))
}

// ---------------------------------------------------------------------------
// Expression rewriting
// ---------------------------------------------------------------------------

/// Rewrite a VirExpr, remapping all VirTypeId fields.
///
/// Delegates to category-specific helpers to stay under the line limit.
fn rewrite_expr(expr: &VirExpr, ctx: &RewriteCtx) -> VirExpr {
    match expr {
        // Literals & construction
        VirExpr::IntLiteral { .. }
        | VirExpr::WideLiteral { .. }
        | VirExpr::FloatLiteral { .. }
        | VirExpr::BoolLiteral(_)
        | VirExpr::StringLiteral(_)
        | VirExpr::NilLiteral
        | VirExpr::Unreachable { .. }
        | VirExpr::Import { .. }
        | VirExpr::TypeLiteral
        | VirExpr::Range { .. }
        | VirExpr::ArrayLiteral { .. }
        | VirExpr::RepeatLiteral { .. }
        | VirExpr::StructLiteral { .. }
        | VirExpr::ClassInstance { .. } => rewrite_expr_literal(expr, ctx),

        // Operators, strings, calls, fields, indexing, RC, coercion
        VirExpr::BinaryOp { .. }
        | VirExpr::UnaryOp { .. }
        | VirExpr::StringConcat { .. }
        | VirExpr::InterpolatedString { .. }
        | VirExpr::Call { .. }
        | VirExpr::MethodCall { .. }
        | VirExpr::FieldLoad { .. }
        | VirExpr::FieldStore { .. }
        | VirExpr::Index { .. }
        | VirExpr::IndexStore { .. }
        | VirExpr::RcInc { .. }
        | VirExpr::RcDec { .. }
        | VirExpr::RcMove { .. }
        | VirExpr::Coerce { .. }
        | VirExpr::ArrayFilled { .. } => rewrite_expr_operation(expr, ctx),

        // Control flow, type ops, reflection, variables, lambda
        VirExpr::If { .. }
        | VirExpr::Match { .. }
        | VirExpr::Block { .. }
        | VirExpr::IsCheck { .. }
        | VirExpr::AsCast { .. }
        | VirExpr::MetaAccess { .. }
        | VirExpr::LocalLoad { .. }
        | VirExpr::LocalStore { .. }
        | VirExpr::Lambda { .. } => rewrite_expr_control(expr, ctx),

        // Optional, null, try, generator
        VirExpr::NullCoalesce { .. }
        | VirExpr::OptionalChain { .. }
        | VirExpr::OptionalMethodCall { .. }
        | VirExpr::Try { .. }
        | VirExpr::Yield { .. } => rewrite_expr_optional(expr, ctx),
    }
}

/// Rewrite literal and construction expressions.
fn rewrite_expr_literal(expr: &VirExpr, ctx: &RewriteCtx) -> VirExpr {
    match expr {
        VirExpr::IntLiteral { value, ty, vir_ty } => VirExpr::IntLiteral {
            value: *value,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::WideLiteral {
            low,
            high,
            ty,
            vir_ty,
        } => VirExpr::WideLiteral {
            low: *low,
            high: *high,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::FloatLiteral { value, ty, vir_ty } => VirExpr::FloatLiteral {
            value: *value,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::BoolLiteral(v) => VirExpr::BoolLiteral(*v),
        VirExpr::StringLiteral(s) => VirExpr::StringLiteral(*s),
        VirExpr::NilLiteral => VirExpr::NilLiteral,
        VirExpr::Unreachable { line } => VirExpr::Unreachable { line: *line },
        VirExpr::Import { ty, vir_ty } => VirExpr::Import {
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::TypeLiteral => VirExpr::TypeLiteral,
        VirExpr::Range {
            start,
            end,
            inclusive,
        } => VirExpr::Range {
            start: rewrite_ref(start, ctx),
            end: rewrite_ref(end, ctx),
            inclusive: *inclusive,
        },
        VirExpr::ArrayLiteral {
            elements,
            ty,
            vir_ty,
            store_strategy,
        } => VirExpr::ArrayLiteral {
            elements: elements.iter().map(|e| rewrite_ref(e, ctx)).collect(),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
            store_strategy: *store_strategy,
        },
        VirExpr::RepeatLiteral {
            element,
            count,
            ty,
            vir_ty,
        } => VirExpr::RepeatLiteral {
            element: rewrite_ref(element, ctx),
            count: *count,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::StructLiteral {
            type_def,
            fields,
            ty,
            vir_ty,
        } => VirExpr::StructLiteral {
            type_def: *type_def,
            fields: rewrite_named_refs(fields, ctx),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::ClassInstance {
            type_def,
            fields,
            field_coercions,
            ty,
            vir_ty,
        } => VirExpr::ClassInstance {
            type_def: *type_def,
            fields: rewrite_named_refs(fields, ctx),
            field_coercions: field_coercions.clone(),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        _ => unreachable!("rewrite_expr_literal called with non-literal"),
    }
}

/// Rewrite operator, call, field, index, RC, and coercion expressions.
fn rewrite_expr_operation(expr: &VirExpr, ctx: &RewriteCtx) -> VirExpr {
    match expr {
        VirExpr::BinaryOp {
            op,
            lhs,
            rhs,
            ty,
            vir_ty,
            promoted_ty,
            line,
            ..
        } => VirExpr::BinaryOp {
            op: *op,
            lhs: rewrite_ref(lhs, ctx),
            rhs: rewrite_ref(rhs, ctx),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
            promoted_ty: ctx.remap(*promoted_ty),
            line: *line,
            // Rederive will recompute from concrete types after monomorphization.
            lhs_is_optional: false,
            rhs_is_optional: false,
            lhs_is_unsigned: false,
            comparison_hint: ComparisonHint::None,
        },
        VirExpr::UnaryOp {
            op,
            operand,
            ty,
            vir_ty,
        } => VirExpr::UnaryOp {
            op: *op,
            operand: rewrite_ref(operand, ctx),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::StringConcat { parts } => VirExpr::StringConcat {
            parts: parts.iter().map(|p| rewrite_ref(p, ctx)).collect(),
        },
        VirExpr::InterpolatedString { parts } => VirExpr::InterpolatedString {
            parts: parts.iter().map(|p| rewrite_string_part(p, ctx)).collect(),
        },
        VirExpr::Call {
            target,
            args,
            ty,
            vir_ty,
            ..
        } => VirExpr::Call {
            target: rewrite_call_target(target, ctx),
            args: args.iter().map(|a| rewrite_ref(a, ctx)).collect(),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
            // Rederive will recompute from concrete types after monomorphization.
            result_is_fallible: false,
        },
        VirExpr::MethodCall {
            receiver,
            method,
            args,
            dispatch,
            node_id,
            ty,
            vir_ty,
        } => VirExpr::MethodCall {
            receiver: rewrite_ref(receiver, ctx),
            method: *method,
            args: args.iter().map(|a| rewrite_ref(a, ctx)).collect(),
            dispatch: rewrite_method_dispatch_meta(dispatch, ctx),
            node_id: *node_id,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::FieldLoad {
            object,
            field,
            storage,
            ty,
            vir_ty,
        } => VirExpr::FieldLoad {
            object: rewrite_ref(object, ctx),
            field: *field,
            storage: *storage,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::FieldStore {
            object,
            field,
            storage,
            value,
        } => VirExpr::FieldStore {
            object: rewrite_ref(object, ctx),
            field: *field,
            storage: *storage,
            value: rewrite_ref(value, ctx),
        },
        VirExpr::Index {
            object,
            index,
            ty,
            vir_ty,
            union_storage,
        } => VirExpr::Index {
            object: rewrite_ref(object, ctx),
            index: rewrite_ref(index, ctx),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
            union_storage: *union_storage,
        },
        VirExpr::IndexStore {
            object,
            index,
            value,
            union_storage,
        } => VirExpr::IndexStore {
            object: rewrite_ref(object, ctx),
            index: rewrite_ref(index, ctx),
            value: rewrite_ref(value, ctx),
            union_storage: *union_storage,
        },
        VirExpr::RcInc { value, cleanup } => VirExpr::RcInc {
            value: rewrite_ref(value, ctx),
            cleanup: *cleanup,
        },
        VirExpr::RcDec { value, cleanup } => VirExpr::RcDec {
            value: rewrite_ref(value, ctx),
            cleanup: *cleanup,
        },
        VirExpr::RcMove { value } => VirExpr::RcMove {
            value: rewrite_ref(value, ctx),
        },
        VirExpr::Coerce {
            value,
            from,
            to,
            vir_from,
            vir_to,
            kind,
        } => VirExpr::Coerce {
            value: rewrite_ref(value, ctx),
            from: ctx.remap(*from),
            to: ctx.remap(*to),
            vir_from: ctx.remap(*vir_from),
            vir_to: ctx.remap(*vir_to),
            kind: rewrite_coerce_kind(kind, ctx),
        },
        VirExpr::ArrayFilled {
            count,
            value,
            elem_type,
            ty,
            vir_ty,
        } => VirExpr::ArrayFilled {
            count: rewrite_ref(count, ctx),
            value: rewrite_ref(value, ctx),
            elem_type: ctx.remap(*elem_type),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        _ => unreachable!("rewrite_expr_operation called with non-operation"),
    }
}

/// Remap VirTypeIds inside enriched `CoerceKind` variants.
fn rewrite_coerce_kind(kind: &CoerceKind, ctx: &RewriteCtx) -> CoerceKind {
    match kind {
        CoerceKind::InterfaceBox {
            interface_type_def,
            interface_type_args,
        } => CoerceKind::InterfaceBox {
            interface_type_def: *interface_type_def,
            interface_type_args: interface_type_args.iter().map(|t| ctx.remap(*t)).collect(),
        },
        // Numeric coercions and Unbox carry no VirTypeIds to remap.
        other => other.clone(),
    }
}

/// Remap VirTypeIds inside `LetStorageHint::Union { tag_hint }`.
///
/// Non-Union variants carry no VirTypeIds and are returned as-is.
fn rewrite_let_storage(storage: &LetStorageHint, ctx: &RewriteCtx) -> LetStorageHint {
    match storage {
        LetStorageHint::Union {
            tag_hint: Some(hint),
            init_is_union,
        } => LetStorageHint::Union {
            tag_hint: Some(UnionTagHint {
                tag: hint.tag,
                is_rc: hint.is_rc,
                variant_type: ctx.remap(hint.variant_type),
            }),
            init_is_union: *init_is_union,
        },
        other => *other,
    }
}

/// Rewrite control flow, type operations, reflection, variables, and lambda.
fn rewrite_expr_control(expr: &VirExpr, ctx: &RewriteCtx) -> VirExpr {
    match expr {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ty,
            vir_ty,
        } => VirExpr::If {
            cond: rewrite_ref(cond, ctx),
            then_body: rewrite_body(then_body, ctx),
            else_body: else_body.as_ref().map(|b| rewrite_body(b, ctx)),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::Match {
            scrutinee,
            arms,
            ty,
            vir_ty,
            result_is_union,
        } => VirExpr::Match {
            scrutinee: rewrite_ref(scrutinee, ctx),
            arms: arms.iter().map(|a| rewrite_match_arm(a, ctx)).collect(),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
            result_is_union: *result_is_union,
        },
        VirExpr::Block {
            stmts,
            trailing,
            ty,
            vir_ty,
        } => VirExpr::Block {
            stmts: stmts.iter().map(|s| rewrite_stmt(s, ctx)).collect(),
            trailing: trailing.as_ref().map(|r| rewrite_ref(r, ctx)),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::IsCheck {
            value,
            result,
            ty,
            vir_ty,
        } => VirExpr::IsCheck {
            value: rewrite_ref(value, ctx),
            result: rewrite_is_check_result(result, ctx),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::AsCast {
            value,
            target_ty,
            vir_target_ty,
            kind,
            result,
        } => VirExpr::AsCast {
            value: rewrite_ref(value, ctx),
            target_ty: ctx.remap(*target_ty),
            vir_target_ty: ctx.remap(*vir_target_ty),
            kind: *kind,
            result: rewrite_is_check_result(result, ctx),
        },
        VirExpr::MetaAccess { kind, ty, vir_ty } => VirExpr::MetaAccess {
            kind: rewrite_meta_kind(kind, ctx),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::LocalLoad { name, ty, vir_ty } => VirExpr::LocalLoad {
            name: *name,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::LocalStore { name, value } => VirExpr::LocalStore {
            name: *name,
            value: rewrite_ref(value, ctx),
        },
        VirExpr::Lambda {
            params,
            body,
            captures,
            ty,
            vir_ty,
        } => VirExpr::Lambda {
            params: params.clone(),
            body: rewrite_body(body, ctx),
            captures: captures.iter().map(|c| rewrite_capture(c, ctx)).collect(),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        _ => unreachable!("rewrite_expr_control called with non-control"),
    }
}

/// Rewrite optional/null operations, try, and generator expressions.
fn rewrite_expr_optional(expr: &VirExpr, ctx: &RewriteCtx) -> VirExpr {
    match expr {
        VirExpr::NullCoalesce {
            value,
            default,
            inner_type,
            vir_inner_type,
            ty,
            vir_ty,
        } => VirExpr::NullCoalesce {
            value: rewrite_ref(value, ctx),
            default: rewrite_ref(default, ctx),
            inner_type: ctx.remap(*inner_type),
            vir_inner_type: ctx.remap(*vir_inner_type),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::OptionalChain {
            object,
            field,
            inner_type,
            vir_inner_type,
            ty,
            vir_ty,
        } => VirExpr::OptionalChain {
            object: rewrite_ref(object, ctx),
            field: *field,
            inner_type: ctx.remap(*inner_type),
            vir_inner_type: ctx.remap(*vir_inner_type),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::OptionalMethodCall {
            object,
            method,
            method_args,
            dispatch,
            call_node_id,
            inner_type,
            vir_inner_type,
            ty,
            vir_ty,
        } => VirExpr::OptionalMethodCall {
            object: rewrite_ref(object, ctx),
            method: *method,
            method_args: method_args.iter().map(|a| rewrite_ref(a, ctx)).collect(),
            dispatch: rewrite_method_dispatch_meta(dispatch, ctx),
            call_node_id: *call_node_id,
            inner_type: ctx.remap(*inner_type),
            vir_inner_type: ctx.remap(*vir_inner_type),
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::Try {
            value,
            success_type,
            vir_success_type,
        } => VirExpr::Try {
            value: rewrite_ref(value, ctx),
            success_type: ctx.remap(*success_type),
            vir_success_type: ctx.remap(*vir_success_type),
        },
        VirExpr::Yield { value } => VirExpr::Yield {
            value: rewrite_ref(value, ctx),
        },
        _ => unreachable!("rewrite_expr_optional called with non-optional"),
    }
}

// ---------------------------------------------------------------------------
// Statement rewriting
// ---------------------------------------------------------------------------

/// Rewrite a VirStmt, remapping all VirTypeId fields.
fn rewrite_stmt(stmt: &VirStmt, ctx: &RewriteCtx) -> VirStmt {
    match stmt {
        VirStmt::Let {
            name,
            value,
            mutable,
            ty,
            vir_ty,
            storage,
            declared_type,
            needs_struct_copy,
            init_coercion,
        } => VirStmt::Let {
            name: *name,
            value: rewrite_ref(value, ctx),
            mutable: *mutable,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
            storage: rewrite_let_storage(storage, ctx),
            declared_type: declared_type.map(|dt| ctx.remap(dt)),
            needs_struct_copy: *needs_struct_copy,
            init_coercion: init_coercion.as_ref().map(|c| rewrite_coerce_kind(c, ctx)),
        },
        VirStmt::LetTuple {
            pattern,
            value,
            init_ty,
            vir_init_ty,
        } => VirStmt::LetTuple {
            pattern: rewrite_destructure_pattern(pattern, ctx),
            value: rewrite_ref(value, ctx),
            init_ty: ctx.remap(*init_ty),
            vir_init_ty: ctx.remap(*vir_init_ty),
        },
        VirStmt::Assign { target, value } => VirStmt::Assign {
            target: rewrite_assign_target(target, ctx),
            value: rewrite_ref(value, ctx),
        },
        VirStmt::Expr { value } => VirStmt::Expr {
            value: rewrite_ref(value, ctx),
        },
        VirStmt::While { cond, body } => VirStmt::While {
            cond: rewrite_ref(cond, ctx),
            body: rewrite_body(body, ctx),
        },
        VirStmt::For(vir_for) => VirStmt::For(rewrite_for(vir_for, ctx)),
        VirStmt::Return {
            value,
            convention,
            return_coercion,
        } => VirStmt::Return {
            value: value.as_ref().map(|v| rewrite_ref(v, ctx)),
            convention: *convention,
            return_coercion: return_coercion
                .as_ref()
                .map(|c| rewrite_coerce_kind(c, ctx)),
        },
        VirStmt::Break => VirStmt::Break,
        VirStmt::Continue => VirStmt::Continue,
        VirStmt::Raise { error_name, fields } => VirStmt::Raise {
            error_name: *error_name,
            fields: rewrite_named_refs(fields, ctx),
        },
        VirStmt::RcInc { value, cleanup } => VirStmt::RcInc {
            value: rewrite_ref(value, ctx),
            cleanup: *cleanup,
        },
        VirStmt::RcDec { value, cleanup } => VirStmt::RcDec {
            value: rewrite_ref(value, ctx),
            cleanup: *cleanup,
        },
        VirStmt::Noop => VirStmt::Noop,
    }
}

// ---------------------------------------------------------------------------
// Pattern rewriting (match arms)
// ---------------------------------------------------------------------------

/// Rewrite a VirPattern, remapping all VirTypeId fields.
fn rewrite_pattern(pat: &VirPattern, ctx: &RewriteCtx) -> VirPattern {
    match pat {
        VirPattern::Wildcard => VirPattern::Wildcard,
        VirPattern::Binding { name, ty, vir_ty } => VirPattern::Binding {
            name: *name,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirPattern::TypeCheck {
            result,
            tested_type,
            vir_tested_type,
            binding,
        } => VirPattern::TypeCheck {
            result: rewrite_is_check_result(result, ctx),
            tested_type: ctx.remap(*tested_type),
            vir_tested_type: ctx.remap(*vir_tested_type),
            binding: binding
                .as_ref()
                .map(|(sym, ty, vir_ty)| (*sym, ctx.remap(*ty), ctx.remap(*vir_ty))),
        },
        VirPattern::Literal {
            value,
            scrutinee_ty,
            vir_scrutinee_ty,
        } => VirPattern::Literal {
            value: rewrite_ref(value, ctx),
            scrutinee_ty: ctx.remap(*scrutinee_ty),
            vir_scrutinee_ty: ctx.remap(*vir_scrutinee_ty),
        },
        VirPattern::Val { name } => VirPattern::Val { name: *name },
        VirPattern::Success {
            inner,
            success_type,
            vir_success_type,
        } => VirPattern::Success {
            inner: inner.as_ref().map(|p| Box::new(rewrite_pattern(p, ctx))),
            success_type: ctx.remap(*success_type),
            vir_success_type: ctx.remap(*vir_success_type),
        },
        VirPattern::Error { kind } => VirPattern::Error {
            kind: rewrite_error_pattern_kind(kind, ctx),
        },
        VirPattern::Tuple { bindings } => VirPattern::Tuple {
            bindings: bindings
                .iter()
                .map(|b| rewrite_tuple_binding(b, ctx))
                .collect(),
        },
        VirPattern::Record {
            type_check,
            tested_type,
            vir_tested_type,
            fields,
            source_ty,
            vir_source_ty,
            is_union_payload,
            is_struct,
        } => VirPattern::Record {
            type_check: type_check.as_ref().map(|r| rewrite_is_check_result(r, ctx)),
            tested_type: tested_type.map(|ty| ctx.remap(ty)),
            vir_tested_type: vir_tested_type.map(|v| ctx.remap(v)),
            fields: fields
                .iter()
                .map(|f| rewrite_record_field_binding(f, ctx))
                .collect(),
            source_ty: ctx.remap(*source_ty),
            vir_source_ty: ctx.remap(*vir_source_ty),
            is_union_payload: *is_union_payload,
            is_struct: *is_struct,
        },
    }
}

// ---------------------------------------------------------------------------
// Supporting type rewriters
// ---------------------------------------------------------------------------

/// Rewrite a VirMatchArm.
fn rewrite_match_arm(arm: &VirMatchArm, ctx: &RewriteCtx) -> VirMatchArm {
    VirMatchArm {
        pattern: rewrite_pattern(&arm.pattern, ctx),
        guard: arm.guard.as_ref().map(|g| rewrite_ref(g, ctx)),
        body: rewrite_body(&arm.body, ctx),
        ty: ctx.remap(arm.ty),
        vir_ty: ctx.remap(arm.vir_ty),
    }
}

/// Rewrite an IsCheckResult (only CheckUnknown carries a VirTypeId).
fn rewrite_is_check_result(result: &IsCheckResult, ctx: &RewriteCtx) -> IsCheckResult {
    match result {
        IsCheckResult::CheckUnknown(ty, vir_ty) => {
            IsCheckResult::CheckUnknown(ctx.remap(*ty), ctx.remap(*vir_ty))
        }
        other => *other,
    }
}

/// Rewrite a VirCapture.
fn rewrite_capture(cap: &VirCapture, ctx: &RewriteCtx) -> VirCapture {
    VirCapture {
        name: cap.name,
        ty: ctx.remap(cap.ty),
        vir_ty: ctx.remap(cap.vir_ty),
        by_ref: cap.by_ref,
        // Preserve the existing rc_kind; the rederive pass will
        // reclassify it once concrete types are available.
        rc_kind: cap.rc_kind,
    }
}

/// Rewrite a VirStringPart.
fn rewrite_string_part(part: &VirStringPart, ctx: &RewriteCtx) -> VirStringPart {
    match part {
        VirStringPart::Literal(s) => VirStringPart::Literal(*s),
        VirStringPart::Expr { value, conversion } => VirStringPart::Expr {
            value: rewrite_ref(value, ctx),
            conversion: conversion.clone(),
        },
    }
}

/// Rewrite a VirMetaKind.
fn rewrite_meta_kind(kind: &VirMetaKind, ctx: &RewriteCtx) -> VirMetaKind {
    match kind {
        VirMetaKind::Static { type_def, object } => VirMetaKind::Static {
            type_def: *type_def,
            object: object.as_ref().map(|o| rewrite_ref(o, ctx)),
        },
        VirMetaKind::Dynamic { value } => VirMetaKind::Dynamic {
            value: rewrite_ref(value, ctx),
        },
        VirMetaKind::TypeParam { name_id, value } => VirMetaKind::TypeParam {
            name_id: *name_id,
            value: rewrite_ref(value, ctx),
        },
    }
}

/// Rewrite a CallTarget (GenericCall carries Vec<VirTypeId>).
fn rewrite_call_target(target: &CallTarget, ctx: &RewriteCtx) -> CallTarget {
    match target {
        CallTarget::GenericCall {
            function_id,
            type_args,
        } => CallTarget::GenericCall {
            function_id: *function_id,
            type_args: type_args.iter().map(|t| ctx.remap(*t)).collect(),
        },
        CallTarget::ClosureVariable {
            var_name,
            vir_type,
            resolved_call_args,
            lambda_defaults,
        } => CallTarget::ClosureVariable {
            var_name: *var_name,
            vir_type: ctx.remap(*vir_type),
            resolved_call_args: resolved_call_args.clone(),
            lambda_defaults: *lambda_defaults,
        },
        CallTarget::CapturedClosure {
            var_name,
            vir_type,
            resolved_call_args,
            lambda_defaults,
        } => CallTarget::CapturedClosure {
            var_name: *var_name,
            vir_type: ctx.remap(*vir_type),
            resolved_call_args: resolved_call_args.clone(),
            lambda_defaults: *lambda_defaults,
        },
        CallTarget::FunctionalInterface {
            var_name,
            vir_type,
            interface_type_def_id,
            method_id,
        } => CallTarget::FunctionalInterface {
            var_name: *var_name,
            vir_type: ctx.remap(*vir_type),
            interface_type_def_id: *interface_type_def_id,
            method_id: *method_id,
        },
        other => other.clone(),
    }
}

/// Rewrite method dispatch metadata (remaps VirTypeId fields).
fn rewrite_method_dispatch_meta(
    meta: &VirMethodDispatchMeta,
    ctx: &RewriteCtx,
) -> VirMethodDispatchMeta {
    VirMethodDispatchMeta {
        dispatch_kind: meta.dispatch_kind,
        resolved_method: meta
            .resolved_method
            .as_ref()
            .map(|resolved| rewrite_resolved_method(resolved, ctx)),
        generic_monomorph: meta
            .generic_monomorph
            .as_ref()
            .map(|key| rewrite_function_monomorph_key(key, ctx)),
        substituted_return_type: meta.substituted_return_type.map(|ty| ctx.remap(ty)),
        vir_substituted_return_type: meta
            .vir_substituted_return_type
            .map(|vir_ty| ctx.remap(vir_ty)),
        resolved_call_args: meta.resolved_call_args.clone(),
        class_method_generic: meta.class_method_generic.as_ref().map(|key| {
            crate::expr::VirClassMethodMonomorphKey {
                class_name: key.class_name,
                method_name: key.method_name,
                type_keys: key.type_keys.iter().map(|t| ctx.remap(*t)).collect(),
                vir_type_keys: key.vir_type_keys.iter().map(|t| ctx.remap(*t)).collect(),
            }
        }),
        static_method_generic: meta
            .static_method_generic
            .as_ref()
            .map(|key| rewrite_static_method_monomorph_key(key, ctx)),
        implement_method_monomorph: meta.implement_method_monomorph.as_ref().map(|key| {
            vole_identity::ImplementMethodMonomorphKey {
                interface_type_def_id: key.interface_type_def_id,
                implementing_type_def_id: key.implementing_type_def_id,
                method_name: key.method_name,
                type_keys: key.type_keys.iter().map(|t| ctx.remap(*t)).collect(),
            }
        }),
        // Copied as-is; rederive_decisions will update from the now-concrete
        // receiver type after substitution.
        receiver_is_interface: meta.receiver_is_interface,
    }
}

fn rewrite_function_monomorph_key(
    key: &crate::expr::VirFunctionMonomorphKey,
    ctx: &RewriteCtx,
) -> crate::expr::VirFunctionMonomorphKey {
    crate::expr::VirFunctionMonomorphKey {
        func_name: key.func_name,
        type_keys: key.type_keys.iter().map(|t| ctx.remap(*t)).collect(),
        vir_type_keys: key.vir_type_keys.iter().map(|t| ctx.remap(*t)).collect(),
    }
}

fn rewrite_static_method_monomorph_key(
    key: &crate::expr::VirStaticMethodMonomorphKey,
    ctx: &RewriteCtx,
) -> crate::expr::VirStaticMethodMonomorphKey {
    crate::expr::VirStaticMethodMonomorphKey {
        class_name: key.class_name,
        method_name: key.method_name,
        class_type_keys: key.class_type_keys.iter().map(|t| ctx.remap(*t)).collect(),
        vir_class_type_keys: key
            .vir_class_type_keys
            .iter()
            .map(|t| ctx.remap(*t))
            .collect(),
        method_type_keys: key.method_type_keys.iter().map(|t| ctx.remap(*t)).collect(),
        vir_method_type_keys: key
            .vir_method_type_keys
            .iter()
            .map(|t| ctx.remap(*t))
            .collect(),
    }
}

fn rewrite_resolved_method(
    resolved: &crate::expr::VirResolvedMethod,
    ctx: &RewriteCtx,
) -> crate::expr::VirResolvedMethod {
    use crate::expr::VirResolvedMethod;

    match resolved {
        VirResolvedMethod::Direct {
            type_def_id,
            func_type_id,
            vir_func_type_id,
            return_type_id,
            vir_return_type_id,
            method_id,
        } => VirResolvedMethod::Direct {
            type_def_id: *type_def_id,
            func_type_id: ctx.remap(*func_type_id),
            vir_func_type_id: ctx.remap(*vir_func_type_id),
            return_type_id: ctx.remap(*return_type_id),
            vir_return_type_id: ctx.remap(*vir_return_type_id),
            method_id: *method_id,
        },
        VirResolvedMethod::Implemented {
            type_def_id,
            func_type_id,
            vir_func_type_id,
            return_type_id,
            vir_return_type_id,
            is_builtin,
            external_info,
            concrete_return_hint,
            vir_concrete_return_hint,
        } => VirResolvedMethod::Implemented {
            type_def_id: *type_def_id,
            func_type_id: ctx.remap(*func_type_id),
            vir_func_type_id: ctx.remap(*vir_func_type_id),
            return_type_id: ctx.remap(*return_type_id),
            vir_return_type_id: ctx.remap(*vir_return_type_id),
            is_builtin: *is_builtin,
            external_info: *external_info,
            concrete_return_hint: concrete_return_hint.map(|ty| ctx.remap(ty)),
            vir_concrete_return_hint: vir_concrete_return_hint.map(|t| ctx.remap(t)),
        },
        VirResolvedMethod::FunctionalInterface {
            func_type_id,
            vir_func_type_id,
            return_type_id,
            vir_return_type_id,
        } => VirResolvedMethod::FunctionalInterface {
            func_type_id: ctx.remap(*func_type_id),
            vir_func_type_id: ctx.remap(*vir_func_type_id),
            return_type_id: ctx.remap(*return_type_id),
            vir_return_type_id: ctx.remap(*vir_return_type_id),
        },
        VirResolvedMethod::DefaultMethod {
            type_def_id,
            interface_type_def_id,
            func_type_id,
            vir_func_type_id,
            return_type_id,
            vir_return_type_id,
            external_info,
            concrete_return_hint,
        } => VirResolvedMethod::DefaultMethod {
            type_def_id: *type_def_id,
            interface_type_def_id: *interface_type_def_id,
            func_type_id: ctx.remap(*func_type_id),
            vir_func_type_id: ctx.remap(*vir_func_type_id),
            return_type_id: ctx.remap(*return_type_id),
            vir_return_type_id: ctx.remap(*vir_return_type_id),
            external_info: *external_info,
            concrete_return_hint: concrete_return_hint.map(|v| ctx.remap(v)),
        },
        VirResolvedMethod::InterfaceMethod {
            interface_type_def_id,
            func_type_id,
            vir_func_type_id,
            return_type_id,
            vir_return_type_id,
            method_index,
        } => VirResolvedMethod::InterfaceMethod {
            interface_type_def_id: *interface_type_def_id,
            func_type_id: ctx.remap(*func_type_id),
            vir_func_type_id: ctx.remap(*vir_func_type_id),
            return_type_id: ctx.remap(*return_type_id),
            vir_return_type_id: ctx.remap(*vir_return_type_id),
            method_index: *method_index,
        },
        VirResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type_id,
            vir_func_type_id,
            return_type_id,
            vir_return_type_id,
        } => VirResolvedMethod::Static {
            type_def_id: *type_def_id,
            method_id: *method_id,
            func_type_id: ctx.remap(*func_type_id),
            vir_func_type_id: ctx.remap(*vir_func_type_id),
            return_type_id: ctx.remap(*return_type_id),
            vir_return_type_id: ctx.remap(*vir_return_type_id),
        },
    }
}

/// Rewrite a VirTupleBinding (match pattern).
fn rewrite_tuple_binding(binding: &VirTupleBinding, ctx: &RewriteCtx) -> VirTupleBinding {
    VirTupleBinding {
        pattern: rewrite_pattern(&binding.pattern, ctx),
        element_index: binding.element_index,
        ty: ctx.remap(binding.ty),
        vir_ty: ctx.remap(binding.vir_ty),
    }
}

/// Rewrite a VirRecordFieldBinding (match pattern).
fn rewrite_record_field_binding(
    binding: &VirRecordFieldBinding,
    ctx: &RewriteCtx,
) -> VirRecordFieldBinding {
    VirRecordFieldBinding {
        field_name: binding.field_name,
        binding_name: binding.binding_name,
        field_slot: binding.field_slot,
        ty: ctx.remap(binding.ty),
        vir_ty: ctx.remap(binding.vir_ty),
    }
}

/// Rewrite a VirErrorPatternKind.
fn rewrite_error_pattern_kind(kind: &VirErrorPatternKind, ctx: &RewriteCtx) -> VirErrorPatternKind {
    match kind {
        VirErrorPatternKind::Bare => VirErrorPatternKind::Bare,
        VirErrorPatternKind::CatchAll {
            name,
            error_ty,
            vir_error_ty,
        } => VirErrorPatternKind::CatchAll {
            name: *name,
            error_ty: ctx.remap(*error_ty),
            vir_error_ty: ctx.remap(*vir_error_ty),
        },
        VirErrorPatternKind::Specific { error_tag } => VirErrorPatternKind::Specific {
            error_tag: *error_tag,
        },
        VirErrorPatternKind::SpecificRecord {
            error_tag,
            type_def,
            fields,
        } => VirErrorPatternKind::SpecificRecord {
            error_tag: *error_tag,
            type_def: *type_def,
            fields: fields.clone(),
        },
    }
}

/// Rewrite a VirFor loop.
fn rewrite_for(vir_for: &VirFor, ctx: &RewriteCtx) -> VirFor {
    VirFor {
        var_name: vir_for.var_name,
        var_type: ctx.remap(vir_for.var_type),
        vir_var_type: ctx.remap(vir_for.vir_var_type),
        iterable: rewrite_ref(&vir_for.iterable, ctx),
        body: rewrite_body(&vir_for.body, ctx),
        kind: rewrite_iter_kind(&vir_for.kind, ctx),
    }
}

/// Rewrite a VirIterKind.
fn rewrite_iter_kind(kind: &VirIterKind, ctx: &RewriteCtx) -> VirIterKind {
    match kind {
        VirIterKind::Range => VirIterKind::Range,
        VirIterKind::Array {
            elem_type,
            vir_elem_type,
            union_storage,
            store_strategy,
            elem_conversion,
        } => VirIterKind::Array {
            elem_type: ctx.remap(*elem_type),
            vir_elem_type: ctx.remap(*vir_elem_type),
            union_storage: *union_storage,
            store_strategy: *store_strategy,
            elem_conversion: *elem_conversion,
        },
        VirIterKind::Iterator {
            elem_type,
            vir_elem_type,
            elem_conversion,
        } => VirIterKind::Iterator {
            elem_type: ctx.remap(*elem_type),
            vir_elem_type: ctx.remap(*vir_elem_type),
            elem_conversion: *elem_conversion,
        },
    }
}

/// Rewrite an AssignTarget.
fn rewrite_assign_target(
    target: &crate::stmt::AssignTarget,
    ctx: &RewriteCtx,
) -> crate::stmt::AssignTarget {
    use crate::stmt::AssignTarget;
    match target {
        AssignTarget::Local(sym) => AssignTarget::Local(*sym),
        AssignTarget::Field {
            object,
            field,
            storage,
        } => AssignTarget::Field {
            object: rewrite_ref(object, ctx),
            field: *field,
            storage: *storage,
        },
        AssignTarget::Index { array, index } => AssignTarget::Index {
            array: rewrite_ref(array, ctx),
            index: rewrite_ref(index, ctx),
        },
    }
}

// ---------------------------------------------------------------------------
// Destructure pattern rewriting (LetTuple)
// ---------------------------------------------------------------------------

/// Rewrite a VirDestructurePattern.
fn rewrite_destructure_pattern(
    pat: &VirDestructurePattern,
    ctx: &RewriteCtx,
) -> VirDestructurePattern {
    match pat {
        VirDestructurePattern::Bind { name, ty, vir_ty } => VirDestructurePattern::Bind {
            name: *name,
            ty: ctx.remap(*ty),
            vir_ty: ctx.remap(*vir_ty),
        },
        VirDestructurePattern::Wildcard => VirDestructurePattern::Wildcard,
        VirDestructurePattern::Tuple { elements, kind } => VirDestructurePattern::Tuple {
            elements: elements
                .iter()
                .map(|e| rewrite_destructure_element(e, ctx))
                .collect(),
            kind: rewrite_destructure_tuple_kind(kind, ctx),
        },
        VirDestructurePattern::Record {
            fields,
            source_ty,
            vir_source_ty,
        } => VirDestructurePattern::Record {
            fields: fields
                .iter()
                .map(|f| rewrite_destructure_field(f, ctx))
                .collect(),
            source_ty: ctx.remap(*source_ty),
            vir_source_ty: ctx.remap(*vir_source_ty),
        },
        VirDestructurePattern::Module {
            bindings,
            module_id,
        } => VirDestructurePattern::Module {
            bindings: bindings
                .iter()
                .map(|b| rewrite_module_binding(b, ctx))
                .collect(),
            module_id: *module_id,
        },
    }
}

/// Rewrite a DestructureTupleKind.
fn rewrite_destructure_tuple_kind(
    kind: &DestructureTupleKind,
    ctx: &RewriteCtx,
) -> DestructureTupleKind {
    match kind {
        DestructureTupleKind::Tuple => DestructureTupleKind::Tuple,
        DestructureTupleKind::FixedArray {
            elem_ty,
            vir_elem_ty,
        } => DestructureTupleKind::FixedArray {
            elem_ty: ctx.remap(*elem_ty),
            vir_elem_ty: ctx.remap(*vir_elem_ty),
        },
    }
}

/// Rewrite a VirDestructureElement.
fn rewrite_destructure_element(
    elem: &VirDestructureElement,
    ctx: &RewriteCtx,
) -> VirDestructureElement {
    VirDestructureElement {
        pattern: rewrite_destructure_pattern(&elem.pattern, ctx),
        ty: ctx.remap(elem.ty),
        vir_ty: ctx.remap(elem.vir_ty),
    }
}

/// Rewrite a VirDestructureField.
fn rewrite_destructure_field(field: &VirDestructureField, ctx: &RewriteCtx) -> VirDestructureField {
    VirDestructureField {
        field_name: field.field_name,
        binding: field.binding,
        slot: field.slot,
        ty: ctx.remap(field.ty),
        vir_ty: ctx.remap(field.vir_ty),
        storage: field.storage,
    }
}

/// Rewrite a VirModuleBinding.
fn rewrite_module_binding(binding: &VirModuleBinding, ctx: &RewriteCtx) -> VirModuleBinding {
    VirModuleBinding {
        export_name: binding.export_name,
        binding: binding.binding,
        export_ty: ctx.remap(binding.export_ty),
        vir_export_ty: ctx.remap(binding.vir_export_ty),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Rewrite a list of `(Symbol, VirRef)` pairs (struct/class fields, raise fields).
fn rewrite_named_refs(fields: &[(Symbol, VirRef)], ctx: &RewriteCtx) -> Vec<(Symbol, VirRef)> {
    fields
        .iter()
        .map(|(sym, r)| (*sym, rewrite_ref(r, ctx)))
        .collect()
}

// We need Symbol in scope for rewrite_named_refs.
use vole_identity::Symbol;

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{VirCaptureRcKind, VirClassMethodMonomorphKey};
    use crate::func::VirBody;
    use crate::monomorph::substitute::{TypeSubstitution, substitute_types};
    use crate::type_table::VirTypeTable;
    use crate::types::VirType;
    use vole_identity::{
        ArrayStoreStrategy, FunctionId, NameId, NodeId, UnionStorageKind, VirElemConversion,
        VirTypeId,
    };

    /// Helper: create a NameId for testing.
    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    /// Helper: create a VirTypeId for testing.
    fn type_id(n: u32) -> VirTypeId {
        VirTypeId::from_raw(n)
    }

    /// Helper: create a Symbol for testing.
    fn sym(n: u32) -> Symbol {
        Symbol::new_for_test(n)
    }

    #[test]
    fn rewrite_simple_function_params_and_return() {
        // Build a source type table with a Param(T).
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        // Substitute T -> I64.
        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        // Build a generic function: fn foo(x: T) -> T { x }
        let func = VirFunction {
            id: FunctionId::new(1),
            name: "foo".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(10),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        // Params should be remapped.
        assert_eq!(result.params[0].2, VirTypeId::I64);
        // Return type should be remapped.
        assert_eq!(result.vir_return_type, VirTypeId::I64);
        // Trailing expression should be remapped.
        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::LocalLoad { vir_ty, .. } => assert_eq!(*vir_ty, VirTypeId::I64),
            other => panic!("expected LocalLoad, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_let_stmt_and_binary_op() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::F64);
        let mapping = substitute_types(&source, &mut target, &subs);

        // fn add(a: T, b: T) -> T { let r = a + b; r }
        let func = VirFunction {
            id: FunctionId::new(2),
            name: "add".to_string(),
            params: vec![
                (sym(1), type_id(10), param_id),
                (sym(2), type_id(10), param_id),
            ],
            return_type: type_id(10),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![VirStmt::Let {
                    name: sym(3),
                    value: Box::new(VirExpr::BinaryOp {
                        op: crate::expr::VirBinOp::Add,
                        lhs: Box::new(VirExpr::LocalLoad {
                            name: sym(1),
                            ty: type_id(10),
                            vir_ty: param_id,
                        }),
                        rhs: Box::new(VirExpr::LocalLoad {
                            name: sym(2),
                            ty: type_id(10),
                            vir_ty: param_id,
                        }),
                        ty: type_id(10),
                        vir_ty: param_id,
                        promoted_ty: param_id,
                        line: 1,
                        lhs_is_optional: false,
                        rhs_is_optional: false,
                        lhs_is_unsigned: false,
                        comparison_hint: crate::expr::ComparisonHint::None,
                    }),
                    mutable: false,
                    ty: type_id(10),
                    vir_ty: param_id,
                    storage: crate::stmt::LetStorageHint::Scalar,
                    declared_type: None,
                    needs_struct_copy: false,
                    init_coercion: None,
                }],
                trailing: Some(Box::new(VirExpr::LocalLoad {
                    name: sym(3),
                    ty: type_id(10),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        // Check the Let statement.
        match &result.body.stmts[0] {
            VirStmt::Let { vir_ty, value, .. } => {
                assert_eq!(*vir_ty, VirTypeId::F64);
                match value.as_ref() {
                    VirExpr::BinaryOp {
                        vir_ty, lhs, rhs, ..
                    } => {
                        assert_eq!(*vir_ty, VirTypeId::F64);
                        match lhs.as_ref() {
                            VirExpr::LocalLoad { vir_ty, .. } => {
                                assert_eq!(*vir_ty, VirTypeId::F64)
                            }
                            other => panic!("expected LocalLoad, got {other:?}"),
                        }
                        match rhs.as_ref() {
                            VirExpr::LocalLoad { vir_ty, .. } => {
                                assert_eq!(*vir_ty, VirTypeId::F64)
                            }
                            other => panic!("expected LocalLoad, got {other:?}"),
                        }
                    }
                    other => panic!("expected BinaryOp, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_if_expression() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::STRING);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(3),
            name: "choose".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(10),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::If {
                    cond: Box::new(VirExpr::BoolLiteral(true)),
                    then_body: VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::LocalLoad {
                            name: sym(1),
                            ty: type_id(10),
                            vir_ty: param_id,
                        })),
                    },
                    else_body: Some(VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::LocalLoad {
                            name: sym(1),
                            ty: type_id(10),
                            vir_ty: param_id,
                        })),
                    }),
                    ty: type_id(10),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::If {
                vir_ty,
                then_body,
                else_body,
                ..
            } => {
                assert_eq!(*vir_ty, VirTypeId::STRING);
                match then_body.trailing.as_ref().unwrap().as_ref() {
                    VirExpr::LocalLoad { vir_ty, .. } => {
                        assert_eq!(*vir_ty, VirTypeId::STRING)
                    }
                    other => panic!("expected LocalLoad, got {other:?}"),
                }
                match else_body
                    .as_ref()
                    .unwrap()
                    .trailing
                    .as_ref()
                    .unwrap()
                    .as_ref()
                {
                    VirExpr::LocalLoad { vir_ty, .. } => {
                        assert_eq!(*vir_ty, VirTypeId::STRING)
                    }
                    other => panic!("expected LocalLoad, got {other:?}"),
                }
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_coerce_remaps_both_types() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let u_name = name(200);
        let t_id = source.intern(VirType::Param { name: t_name }, None);
        let u_id = source.intern(VirType::Param { name: u_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I32);
        subs.insert(u_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(4),
            name: "widen".to_string(),
            params: vec![(sym(1), type_id(10), t_id)],
            return_type: type_id(20),
            vir_return_type: u_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Coerce {
                    value: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: t_id,
                    }),
                    from: type_id(10),
                    to: type_id(20),
                    vir_from: t_id,
                    vir_to: u_id,
                    kind: crate::expr::CoerceKind::IntExtend,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Coerce {
                vir_from, vir_to, ..
            } => {
                assert_eq!(*vir_from, VirTypeId::I32);
                assert_eq!(*vir_to, VirTypeId::I64);
            }
            other => panic!("expected Coerce, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_match_with_binding_pattern() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(5),
            name: "m".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(10),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Match {
                    scrutinee: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    }),
                    arms: vec![VirMatchArm {
                        pattern: VirPattern::Binding {
                            name: sym(2),
                            ty: type_id(10),
                            vir_ty: param_id,
                        },
                        guard: None,
                        body: VirBody {
                            stmts: vec![],
                            trailing: Some(Box::new(VirExpr::LocalLoad {
                                name: sym(2),
                                ty: type_id(10),
                                vir_ty: param_id,
                            })),
                        },
                        ty: type_id(10),
                        vir_ty: param_id,
                    }],
                    ty: type_id(10),
                    vir_ty: param_id,
                    result_is_union: false,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Match { vir_ty, arms, .. } => {
                assert_eq!(*vir_ty, VirTypeId::I64);
                assert_eq!(arms[0].vir_ty, VirTypeId::I64);
                match &arms[0].pattern {
                    VirPattern::Binding { vir_ty, .. } => {
                        assert_eq!(*vir_ty, VirTypeId::I64)
                    }
                    other => panic!("expected Binding, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_for_loop_remaps_iter_kind() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::STRING);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(6),
            name: "loop_over".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![VirStmt::For(VirFor {
                    var_name: sym(1),
                    var_type: type_id(10),
                    vir_var_type: param_id,
                    iterable: Box::new(VirExpr::NilLiteral),
                    body: VirBody {
                        stmts: vec![],
                        trailing: None,
                    },
                    kind: VirIterKind::Iterator {
                        elem_type: type_id(10),
                        vir_elem_type: param_id,
                        elem_conversion: VirElemConversion::Unresolved,
                    },
                })],
                trailing: None,
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        match &result.body.stmts[0] {
            VirStmt::For(vir_for) => {
                assert_eq!(vir_for.vir_var_type, VirTypeId::STRING);
                match &vir_for.kind {
                    VirIterKind::Iterator { vir_elem_type, .. } => {
                        assert_eq!(*vir_elem_type, VirTypeId::STRING)
                    }
                    other => panic!("expected Iterator, got {other:?}"),
                }
            }
            other => panic!("expected For, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_for_loop_array_iter_kind_remaps_elem_type() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(11),
            name: "array_loop".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![VirStmt::For(VirFor {
                    var_name: sym(1),
                    var_type: type_id(10),
                    vir_var_type: param_id,
                    iterable: Box::new(VirExpr::NilLiteral),
                    body: VirBody {
                        stmts: vec![],
                        trailing: None,
                    },
                    kind: VirIterKind::Array {
                        elem_type: type_id(10),
                        vir_elem_type: param_id,
                        union_storage: Some(UnionStorageKind::Inline),
                        store_strategy: Some(ArrayStoreStrategy::UnionInline),
                        elem_conversion: Some(VirElemConversion::Identity),
                    },
                })],
                trailing: None,
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        match &result.body.stmts[0] {
            VirStmt::For(vir_for) => match &vir_for.kind {
                VirIterKind::Array {
                    vir_elem_type,
                    union_storage,
                    ..
                } => {
                    assert_eq!(*vir_elem_type, VirTypeId::I64);
                    assert_eq!(*union_storage, Some(UnionStorageKind::Inline));
                }
                other => panic!("expected Array iter kind, got {other:?}"),
            },
            other => panic!("expected For, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_optional_chain_remaps_optional_chain_info_types() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::STRING);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(12),
            name: "optional_chain".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(20),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::OptionalChain {
                    object: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    }),
                    field: sym(2),
                    inner_type: type_id(20),
                    vir_inner_type: param_id,
                    ty: type_id(30),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::OptionalChain {
                object,
                vir_inner_type,
                vir_ty,
                ..
            } => {
                assert_eq!(*vir_inner_type, VirTypeId::STRING);
                assert_eq!(*vir_ty, VirTypeId::STRING);
                match object.as_ref() {
                    VirExpr::LocalLoad { vir_ty, .. } => assert_eq!(*vir_ty, VirTypeId::STRING),
                    other => panic!("expected LocalLoad object, got {other:?}"),
                }
            }
            other => panic!("expected OptionalChain, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_optional_method_call_remaps_inner_and_substituted_return_types() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::BOOL);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(13),
            name: "optional_method".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(20),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::OptionalMethodCall {
                    object: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    }),
                    method: sym(3),
                    method_args: vec![Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    })],
                    dispatch: VirMethodDispatchMeta::default(),
                    call_node_id: NodeId::new_for_test(42),
                    inner_type: type_id(20),
                    vir_inner_type: param_id,
                    ty: type_id(30),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::OptionalMethodCall {
                method_args,
                call_node_id,
                vir_inner_type,
                vir_ty,
                ..
            } => {
                assert_eq!(*call_node_id, NodeId::new_for_test(42));
                assert_eq!(*vir_inner_type, VirTypeId::BOOL);
                assert_eq!(
                    *vir_ty,
                    VirTypeId::BOOL,
                    "vir_ty carries substituted method return type and must remap"
                );
                match method_args[0].as_ref() {
                    VirExpr::LocalLoad { vir_ty, .. } => assert_eq!(*vir_ty, VirTypeId::BOOL),
                    other => panic!("expected LocalLoad arg, got {other:?}"),
                }
            }
            other => panic!("expected OptionalMethodCall, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_is_check_unknown_remaps_vir_ty() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(7),
            name: "check".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::BOOL,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::IsCheck {
                    value: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    }),
                    result: IsCheckResult::CheckUnknown(type_id(20), param_id),
                    ty: type_id(30),
                    vir_ty: VirTypeId::BOOL,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IsCheck { result, .. } => match result {
                IsCheckResult::CheckUnknown(_, vir_ty) => {
                    assert_eq!(*vir_ty, VirTypeId::I64)
                }
                other => panic!("expected CheckUnknown, got {other:?}"),
            },
            other => panic!("expected IsCheck, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_identity_when_no_param_types() {
        // Function with only concrete VirTypeIds: rewrite should be identity.
        let func = VirFunction {
            id: FunctionId::new(8),
            name: "concrete".to_string(),
            params: vec![(sym(1), type_id(10), VirTypeId::I64)],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::IntLiteral {
                    value: 42,
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        // Empty mapping.
        let ctx = RewriteCtx::new(FxHashMap::default());
        let result = rewrite_function(&func, &ctx);

        assert_eq!(result.params[0].2, VirTypeId::I64);
        assert_eq!(result.vir_return_type, VirTypeId::I64);
        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IntLiteral { vir_ty, .. } => assert_eq!(*vir_ty, VirTypeId::I64),
            other => panic!("expected IntLiteral, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_lambda_remaps_captures() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::STRING);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(9),
            name: "with_lambda".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Lambda {
                    params: vec![sym(1)],
                    body: VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::LocalLoad {
                            name: sym(2),
                            ty: type_id(10),
                            vir_ty: param_id,
                        })),
                    },
                    captures: vec![VirCapture {
                        name: sym(2),
                        ty: type_id(10),
                        vir_ty: param_id,
                        by_ref: false,
                        rc_kind: VirCaptureRcKind::Unresolved,
                    }],
                    ty: type_id(20),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Lambda {
                captures, vir_ty, ..
            } => {
                assert_eq!(*vir_ty, VirTypeId::STRING);
                assert_eq!(captures[0].vir_ty, VirTypeId::STRING);
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_generic_call_remaps_type_args() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(10),
            name: "call_generic".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::GenericCall {
                        function_id: FunctionId::new(99),
                        type_args: vec![param_id, VirTypeId::BOOL],
                    },
                    args: vec![],
                    ty: type_id(10),
                    vir_ty: param_id,
                    result_is_fallible: false,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Call { target, vir_ty, .. } => {
                assert_eq!(*vir_ty, VirTypeId::I64);
                match target {
                    CallTarget::GenericCall { type_args, .. } => {
                        assert_eq!(type_args[0], VirTypeId::I64);
                        assert_eq!(type_args[1], VirTypeId::BOOL);
                    }
                    other => panic!("expected GenericCall, got {other:?}"),
                }
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_method_dispatch_metadata_remaps_vir_type_ids() {
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let func = VirFunction {
            id: FunctionId::new(11),
            name: "method_dispatch_meta".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(20),
            vir_return_type: param_id,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::MethodCall {
                    receiver: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    }),
                    method: sym(2),
                    args: vec![],
                    dispatch: VirMethodDispatchMeta {
                        dispatch_kind: None,
                        resolved_method: Some(crate::expr::VirResolvedMethod::Implemented {
                            type_def_id: Some(vole_identity::TypeDefId::new(7)),
                            func_type_id: type_id(21),
                            vir_func_type_id: param_id,
                            return_type_id: type_id(22),
                            vir_return_type_id: param_id,
                            is_builtin: false,
                            external_info: None,
                            concrete_return_hint: Some(type_id(23)),
                            vir_concrete_return_hint: Some(param_id),
                        }),
                        generic_monomorph: Some(crate::expr::VirFunctionMonomorphKey {
                            func_name: name(30),
                            type_keys: vec![type_id(10)],
                            vir_type_keys: vec![param_id],
                        }),
                        substituted_return_type: Some(type_id(20)),
                        vir_substituted_return_type: Some(param_id),
                        resolved_call_args: Some(vec![Some(0)]),
                        class_method_generic: Some(VirClassMethodMonomorphKey {
                            class_name: name(10),
                            method_name: name(20),
                            type_keys: vec![type_id(10)],
                            vir_type_keys: vec![param_id, VirTypeId::BOOL],
                        }),
                        static_method_generic: Some(crate::expr::VirStaticMethodMonomorphKey {
                            class_name: name(40),
                            method_name: name(41),
                            class_type_keys: vec![type_id(10)],
                            vir_class_type_keys: vec![param_id],
                            method_type_keys: vec![type_id(11)],
                            vir_method_type_keys: vec![param_id],
                        }),
                        implement_method_monomorph: Some(
                            vole_identity::ImplementMethodMonomorphKey {
                                interface_type_def_id: vole_identity::TypeDefId::new(50),
                                implementing_type_def_id: vole_identity::TypeDefId::new(51),
                                method_name: name(60),
                                type_keys: vec![param_id],
                            },
                        ),
                        receiver_is_interface: false,
                    },
                    node_id: NodeId::new_for_test(7),
                    ty: type_id(20),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::MethodCall {
                dispatch, vir_ty, ..
            } => {
                assert_eq!(*vir_ty, VirTypeId::I64);
                assert_eq!(dispatch.vir_substituted_return_type, Some(VirTypeId::I64));
                let resolved = dispatch
                    .resolved_method
                    .as_ref()
                    .expect("missing resolved method");
                assert_eq!(resolved.func_type_id(), type_id(21));
                assert_eq!(resolved.return_type_id(), type_id(22));
                let resolved_hint = match resolved {
                    crate::expr::VirResolvedMethod::Implemented {
                        vir_concrete_return_hint,
                        ..
                    } => *vir_concrete_return_hint,
                    other => panic!("expected Implemented resolved method, got {other:?}"),
                };
                assert_eq!(resolved_hint, Some(VirTypeId::I64));
                let generic_key = dispatch
                    .generic_monomorph
                    .as_ref()
                    .expect("missing function key");
                assert_eq!(generic_key.vir_type_keys, vec![VirTypeId::I64]);
                let key = dispatch
                    .class_method_generic
                    .as_ref()
                    .expect("missing class key");
                assert_eq!(key.vir_type_keys, vec![VirTypeId::I64, VirTypeId::BOOL]);
                let static_key = dispatch
                    .static_method_generic
                    .as_ref()
                    .expect("missing static key");
                assert_eq!(static_key.vir_class_type_keys, vec![VirTypeId::I64]);
                assert_eq!(static_key.vir_method_type_keys, vec![VirTypeId::I64]);
                let impl_key = dispatch
                    .implement_method_monomorph
                    .as_ref()
                    .expect("missing implement method key");
                assert_eq!(
                    impl_key.interface_type_def_id,
                    vole_identity::TypeDefId::new(50)
                );
                assert_eq!(
                    impl_key.implementing_type_def_id,
                    vole_identity::TypeDefId::new(51)
                );
                assert_eq!(impl_key.method_name, name(60));
                assert_eq!(impl_key.type_keys, vec![VirTypeId::I64]);
            }
            other => panic!("expected MethodCall, got {other:?}"),
        }
    }
}
