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
    IsCheckResult, VirCapture, VirErrorPatternKind, VirExpr, VirMatchArm, VirMetaKind, VirPattern,
    VirRecordFieldBinding, VirStringPart, VirTupleBinding,
};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::{
    DestructureTupleKind, VirDestructureElement, VirDestructureField, VirDestructurePattern,
    VirFor, VirIterKind, VirModuleBinding, VirStmt,
};

/// Remap context carrying old->new VirTypeId mapping.
///
/// TypeId fields are left as-is during rewrite (they will be removed in Phase E).
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
        .map(|(sym, ty, vir_ty)| (*sym, *ty, ctx.remap(*vir_ty)))
        .collect();

    VirFunction {
        id: func.id,
        name: func.name.clone(),
        params,
        return_type: func.return_type,
        vir_return_type: ctx.remap(func.vir_return_type),
        body: rewrite_body(&func.body, ctx),
        mangled_name_id: func.mangled_name_id,
        method_id: func.method_id,
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
        | VirExpr::Coerce { .. } => rewrite_expr_operation(expr, ctx),

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
            ty: *ty,
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
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::FloatLiteral { value, ty, vir_ty } => VirExpr::FloatLiteral {
            value: *value,
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::BoolLiteral(v) => VirExpr::BoolLiteral(*v),
        VirExpr::StringLiteral(s) => VirExpr::StringLiteral(*s),
        VirExpr::NilLiteral => VirExpr::NilLiteral,
        VirExpr::Unreachable { line } => VirExpr::Unreachable { line: *line },
        VirExpr::Import { ty, vir_ty } => VirExpr::Import {
            ty: *ty,
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
        } => VirExpr::ArrayLiteral {
            elements: elements.iter().map(|e| rewrite_ref(e, ctx)).collect(),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::RepeatLiteral {
            element,
            count,
            ty,
            vir_ty,
        } => VirExpr::RepeatLiteral {
            element: rewrite_ref(element, ctx),
            count: *count,
            ty: *ty,
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
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::ClassInstance {
            type_def,
            fields,
            ty,
            vir_ty,
        } => VirExpr::ClassInstance {
            type_def: *type_def,
            fields: rewrite_named_refs(fields, ctx),
            ty: *ty,
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
            line,
        } => VirExpr::BinaryOp {
            op: *op,
            lhs: rewrite_ref(lhs, ctx),
            rhs: rewrite_ref(rhs, ctx),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
            line: *line,
        },
        VirExpr::UnaryOp {
            op,
            operand,
            ty,
            vir_ty,
        } => VirExpr::UnaryOp {
            op: *op,
            operand: rewrite_ref(operand, ctx),
            ty: *ty,
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
        } => VirExpr::Call {
            target: rewrite_call_target(target, ctx),
            args: args.iter().map(|a| rewrite_ref(a, ctx)).collect(),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::MethodCall {
            receiver,
            method,
            args,
            node_id,
            ty,
            vir_ty,
        } => VirExpr::MethodCall {
            receiver: rewrite_ref(receiver, ctx),
            method: *method,
            args: args.iter().map(|a| rewrite_ref(a, ctx)).collect(),
            node_id: *node_id,
            ty: *ty,
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
            ty: *ty,
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
            ty: *ty,
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
        VirExpr::RcInc { value } => VirExpr::RcInc {
            value: rewrite_ref(value, ctx),
        },
        VirExpr::RcDec { value } => VirExpr::RcDec {
            value: rewrite_ref(value, ctx),
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
            from: *from,
            to: *to,
            vir_from: ctx.remap(*vir_from),
            vir_to: ctx.remap(*vir_to),
            kind: *kind,
        },
        _ => unreachable!("rewrite_expr_operation called with non-operation"),
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
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::Match {
            scrutinee,
            arms,
            ty,
            vir_ty,
        } => VirExpr::Match {
            scrutinee: rewrite_ref(scrutinee, ctx),
            arms: arms.iter().map(|a| rewrite_match_arm(a, ctx)).collect(),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::Block {
            stmts,
            trailing,
            ty,
            vir_ty,
        } => VirExpr::Block {
            stmts: stmts.iter().map(|s| rewrite_stmt(s, ctx)).collect(),
            trailing: trailing.as_ref().map(|r| rewrite_ref(r, ctx)),
            ty: *ty,
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
            ty: *ty,
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
            target_ty: *target_ty,
            vir_target_ty: ctx.remap(*vir_target_ty),
            kind: *kind,
            result: rewrite_is_check_result(result, ctx),
        },
        VirExpr::MetaAccess { kind, ty, vir_ty } => VirExpr::MetaAccess {
            kind: rewrite_meta_kind(kind, ctx),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::LocalLoad { name, ty, vir_ty } => VirExpr::LocalLoad {
            name: *name,
            ty: *ty,
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
            ty: *ty,
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
            inner_type: *inner_type,
            vir_inner_type: ctx.remap(*vir_inner_type),
            ty: *ty,
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
            inner_type: *inner_type,
            vir_inner_type: ctx.remap(*vir_inner_type),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::OptionalMethodCall {
            object,
            method,
            method_args,
            call_node_id,
            inner_type,
            vir_inner_type,
            ty,
            vir_ty,
        } => VirExpr::OptionalMethodCall {
            object: rewrite_ref(object, ctx),
            method: *method,
            method_args: method_args.iter().map(|a| rewrite_ref(a, ctx)).collect(),
            call_node_id: *call_node_id,
            inner_type: *inner_type,
            vir_inner_type: ctx.remap(*vir_inner_type),
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirExpr::Try {
            value,
            success_type,
            vir_success_type,
        } => VirExpr::Try {
            value: rewrite_ref(value, ctx),
            success_type: *success_type,
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
        } => VirStmt::Let {
            name: *name,
            value: rewrite_ref(value, ctx),
            mutable: *mutable,
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirStmt::LetTuple {
            pattern,
            value,
            init_ty,
            vir_init_ty,
        } => VirStmt::LetTuple {
            pattern: rewrite_destructure_pattern(pattern, ctx),
            value: rewrite_ref(value, ctx),
            init_ty: *init_ty,
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
        VirStmt::Return { value } => VirStmt::Return {
            value: value.as_ref().map(|v| rewrite_ref(v, ctx)),
        },
        VirStmt::Break => VirStmt::Break,
        VirStmt::Continue => VirStmt::Continue,
        VirStmt::Raise { error_name, fields } => VirStmt::Raise {
            error_name: *error_name,
            fields: rewrite_named_refs(fields, ctx),
        },
        VirStmt::RcInc { value } => VirStmt::RcInc {
            value: rewrite_ref(value, ctx),
        },
        VirStmt::RcDec { value } => VirStmt::RcDec {
            value: rewrite_ref(value, ctx),
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
            ty: *ty,
            vir_ty: ctx.remap(*vir_ty),
        },
        VirPattern::TypeCheck {
            result,
            tested_type,
            vir_tested_type,
            binding,
        } => VirPattern::TypeCheck {
            result: rewrite_is_check_result(result, ctx),
            tested_type: *tested_type,
            vir_tested_type: ctx.remap(*vir_tested_type),
            binding: binding
                .as_ref()
                .map(|(sym, ty, vir_ty)| (*sym, *ty, ctx.remap(*vir_ty))),
        },
        VirPattern::Literal {
            value,
            scrutinee_ty,
            vir_scrutinee_ty,
        } => VirPattern::Literal {
            value: rewrite_ref(value, ctx),
            scrutinee_ty: *scrutinee_ty,
            vir_scrutinee_ty: ctx.remap(*vir_scrutinee_ty),
        },
        VirPattern::Val { name } => VirPattern::Val { name: *name },
        VirPattern::Success {
            inner,
            success_type,
            vir_success_type,
        } => VirPattern::Success {
            inner: inner.as_ref().map(|p| Box::new(rewrite_pattern(p, ctx))),
            success_type: *success_type,
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
            tested_type: *tested_type,
            vir_tested_type: vir_tested_type.map(|v| ctx.remap(v)),
            fields: fields
                .iter()
                .map(|f| rewrite_record_field_binding(f, ctx))
                .collect(),
            source_ty: *source_ty,
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
        ty: arm.ty,
        vir_ty: ctx.remap(arm.vir_ty),
    }
}

/// Rewrite an IsCheckResult (only CheckUnknown carries a VirTypeId).
fn rewrite_is_check_result(result: &IsCheckResult, ctx: &RewriteCtx) -> IsCheckResult {
    match result {
        IsCheckResult::CheckUnknown(ty, vir_ty) => {
            IsCheckResult::CheckUnknown(*ty, ctx.remap(*vir_ty))
        }
        other => *other,
    }
}

/// Rewrite a VirCapture.
fn rewrite_capture(cap: &VirCapture, ctx: &RewriteCtx) -> VirCapture {
    VirCapture {
        name: cap.name,
        ty: cap.ty,
        vir_ty: ctx.remap(cap.vir_ty),
        by_ref: cap.by_ref,
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
        other => other.clone(),
    }
}

/// Rewrite a VirTupleBinding (match pattern).
fn rewrite_tuple_binding(binding: &VirTupleBinding, ctx: &RewriteCtx) -> VirTupleBinding {
    VirTupleBinding {
        pattern: rewrite_pattern(&binding.pattern, ctx),
        element_index: binding.element_index,
        ty: binding.ty,
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
        ty: binding.ty,
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
            error_ty: *error_ty,
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
        var_type: vir_for.var_type,
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
        } => VirIterKind::Array {
            elem_type: *elem_type,
            vir_elem_type: ctx.remap(*vir_elem_type),
            union_storage: *union_storage,
        },
        VirIterKind::String => VirIterKind::String,
        VirIterKind::IteratorInterface {
            elem_type,
            vir_elem_type,
        } => VirIterKind::IteratorInterface {
            elem_type: *elem_type,
            vir_elem_type: ctx.remap(*vir_elem_type),
        },
        VirIterKind::CustomIterator {
            elem_type,
            vir_elem_type,
        } => VirIterKind::CustomIterator {
            elem_type: *elem_type,
            vir_elem_type: ctx.remap(*vir_elem_type),
        },
        VirIterKind::CustomIterable {
            elem_type,
            vir_elem_type,
        } => VirIterKind::CustomIterable {
            elem_type: *elem_type,
            vir_elem_type: ctx.remap(*vir_elem_type),
        },
        VirIterKind::Generic {
            elem_type,
            vir_elem_type,
        } => VirIterKind::Generic {
            elem_type: *elem_type,
            vir_elem_type: ctx.remap(*vir_elem_type),
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
            ty: *ty,
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
            is_struct,
        } => VirDestructurePattern::Record {
            fields: fields
                .iter()
                .map(|f| rewrite_destructure_field(f, ctx))
                .collect(),
            source_ty: *source_ty,
            vir_source_ty: ctx.remap(*vir_source_ty),
            is_struct: *is_struct,
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
            elem_ty: *elem_ty,
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
        ty: elem.ty,
        vir_ty: ctx.remap(elem.vir_ty),
    }
}

/// Rewrite a VirDestructureField.
fn rewrite_destructure_field(field: &VirDestructureField, ctx: &RewriteCtx) -> VirDestructureField {
    VirDestructureField {
        field_name: field.field_name,
        binding: field.binding,
        slot: field.slot,
        ty: field.ty,
        vir_ty: ctx.remap(field.vir_ty),
    }
}

/// Rewrite a VirModuleBinding.
fn rewrite_module_binding(binding: &VirModuleBinding, ctx: &RewriteCtx) -> VirModuleBinding {
    VirModuleBinding {
        export_name: binding.export_name,
        binding: binding.binding,
        export_ty: binding.export_ty,
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
    use crate::func::VirBody;
    use crate::monomorph::substitute::{TypeSubstitution, substitute_types};
    use crate::type_table::VirTypeTable;
    use crate::types::VirType;
    use vole_identity::{FunctionId, NameId, TypeId, VirTypeId};

    /// Helper: create a NameId for testing.
    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    /// Helper: create a TypeId for testing.
    fn type_id(n: u32) -> TypeId {
        TypeId::from_raw(n)
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
                        line: 1,
                    }),
                    mutable: false,
                    ty: type_id(10),
                    vir_ty: param_id,
                }],
                trailing: Some(Box::new(VirExpr::LocalLoad {
                    name: sym(3),
                    ty: type_id(10),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
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
                })),
            },
            mangled_name_id: None,
            method_id: None,
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
            return_type: TypeId::VOID,
            vir_return_type: VirTypeId::VOID,
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
                    kind: VirIterKind::Generic {
                        elem_type: type_id(10),
                        vir_elem_type: param_id,
                    },
                })],
                trailing: None,
            },
            mangled_name_id: None,
            method_id: None,
        };

        let ctx = RewriteCtx::new(mapping);
        let result = rewrite_function(&func, &ctx);

        match &result.body.stmts[0] {
            VirStmt::For(vir_for) => {
                assert_eq!(vir_for.vir_var_type, VirTypeId::STRING);
                match &vir_for.kind {
                    VirIterKind::Generic { vir_elem_type, .. } => {
                        assert_eq!(*vir_elem_type, VirTypeId::STRING)
                    }
                    other => panic!("expected Generic, got {other:?}"),
                }
            }
            other => panic!("expected For, got {other:?}"),
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
            return_type: TypeId::VOID,
            vir_return_type: VirTypeId::BOOL,
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
            return_type: TypeId::VOID,
            vir_return_type: VirTypeId::VOID,
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
                    }],
                    ty: type_id(20),
                    vir_ty: param_id,
                })),
            },
            mangled_name_id: None,
            method_id: None,
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
            return_type: TypeId::VOID,
            vir_return_type: VirTypeId::VOID,
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
                })),
            },
            mangled_name_id: None,
            method_id: None,
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
}
