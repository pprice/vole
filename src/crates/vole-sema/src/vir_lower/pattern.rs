// vir_lower/pattern.rs
//
// Pattern lowering: AST `Pattern` → VIR `VirPattern`.
//
// All match-expression and pattern-matching lowering lives here.
// `lower_match_expr` is the public entry point, called from expr.rs.

use crate::TypeArena;
use vole_frontend::Expr;
use vole_identity::{TypeDefId, TypeId};

use vole_vir::expr::{
    IsCheckResult, VirErrorFieldBinding, VirErrorPatternKind, VirExpr, VirMatchArm, VirPattern,
    VirRecordFieldBinding, VirTupleBinding,
};
use vole_vir::func::VirBody;
use vole_vir::refs::VirRef;

use super::LoweringCtx;
use super::expr::{convert_is_check_result, lower_expr, recover_tested_type};

/// Lower a `match` expression to `VirExpr::Match`.
///
/// The scrutinee is recursively lowered. All patterns are lowered to
/// concrete `VirPattern` variants (Wildcard, Binding, TypeCheck, Literal,
/// Val, Success, Error, Tuple, Record). Guards and bodies are recursively
/// lowered.
pub(super) fn lower_match_expr(
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
            let compat_ty = ctx.compat_ty(arm_ty);
            let vir_ty = ctx.translate(arm_ty);
            VirMatchArm {
                pattern,
                guard,
                body: VirBody {
                    stmts: Vec::new(),
                    trailing: Some(body_ref),
                },
                ty: compat_ty,
                vir_ty,
            }
        })
        .collect();

    let compat_ty = ctx.compat_ty(ty);
    let vir_ty = ctx.translate(ty);
    let result_is_union = !ctx.generic && ctx.type_arena.is_union(ty);
    Box::new(VirExpr::Match {
        scrutinee,
        arms,
        ty: compat_ty,
        vir_ty,
        result_is_union,
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
                let tested_type = recover_tested_type(&result, scrutinee_ty, ctx);
                let vir_tested_type = tested_type;
                VirPattern::TypeCheck {
                    result,
                    tested_type,
                    vir_tested_type,
                    binding: None,
                }
            } else {
                let compat_ty = ctx.compat_ty(scrutinee_ty);
                let vir_ty = ctx.translate(scrutinee_ty);
                VirPattern::Binding {
                    name: *name,
                    ty: compat_ty,
                    vir_ty,
                }
            }
        }

        PatternKind::Type { .. } => {
            let sema_result = ctx.require_is_check_result(pattern.id, 0);
            let result = convert_is_check_result(sema_result, ctx);
            let tested_type = recover_tested_type(&result, scrutinee_ty, ctx);
            let vir_tested_type = tested_type;
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
                scrutinee_ty: vir_scrutinee_ty,
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
        success_type: vir_success_type,
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
        // Other inner patterns (wildcard, etc.) -> bare error match
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
            let compat_ty = ctx.compat_ty(elem_ty);
            let vir_ty = ctx.translate(elem_ty);
            VirTupleBinding {
                pattern: inner,
                element_index: i,
                ty: compat_ty,
                vir_ty,
            }
        })
        .collect();

    VirPattern::Tuple { bindings }
}

/// Lower an identifier inside an `error` pattern.
///
/// Determines whether the identifier is an error type name (-> Specific)
/// or a catch-all binding (-> CatchAll) by checking the fallible's error
/// union for a matching error type name.
fn lower_error_identifier_pattern(
    name: vole_identity::Symbol,
    scrutinee_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirPattern {
    let fallible = ctx.type_arena.unwrap_fallible(scrutinee_ty);
    let error_tag = fallible.and_then(|(_, error_ty)| compute_error_tag(error_ty, name, ctx));

    if let Some(tag) = error_tag {
        // Identifier matches an error type -> specific error pattern
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
                error_ty: vir_error_ty,
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
) -> Option<TypeDefId> {
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
                let tested = recover_tested_type(&check, scrutinee_ty, ctx);
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

    let vir_tested_type = tested_type;
    let vir_source_ty = ctx.translate(source_ty);

    VirPattern::Record {
        type_check,
        tested_type,
        vir_tested_type,
        fields: vir_fields,
        source_ty: vir_source_ty,
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
        kind.is_class_or_struct() || matches!(kind, crate::type_arena::NominalKind::Error)
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
            let compat_ty = ctx.compat_ty(ty);
            let vir_ty = ctx.translate(ty);
            VirRecordFieldBinding {
                field_name: f.field_name,
                binding_name: f.binding,
                field_slot: slot as u32,
                ty: compat_ty,
                vir_ty,
            }
        })
        .collect()
}

/// Find a field's slot index and type in a type definition.
fn find_field_slot(
    type_def_id: TypeDefId,
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
