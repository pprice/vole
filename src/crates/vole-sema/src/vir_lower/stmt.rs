// vir_lower/stmt.rs
//
// Statement lowering: AST `Stmt` -> VIR `VirStmt`.

use crate::IterableKind;
use vole_frontend::PatternKind;
use vole_frontend::ast::{ExprKind, LetInit, LetStmt, Stmt};
use vole_identity::TypeId;

use vole_vir::expr::VirExpr;
use vole_vir::stmt::{
    DestructureTupleKind, LetStorageHint, ReturnConvention, UnionTagHint, VirDestructureElement,
    VirDestructureField, VirDestructurePattern, VirFor, VirIterKind, VirModuleBinding, VirStmt,
};

use super::LoweringCtx;
use super::expr::lower_expr;
use super::lower_stmts;

/// Lower a single AST statement into a VIR statement.
///
/// All `Stmt` variants are lowered to typed `VirStmt` nodes.  Expression
/// statements are recursively lowered through `lower_expr`.
///
/// Each variant is listed explicitly so that adding a new `Stmt` variant
/// causes a compile error rather than silently falling through a wildcard.
pub fn lower_stmt(stmt: &Stmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    match stmt {
        Stmt::Expr(expr_stmt) => VirStmt::Expr {
            value: lower_expr(&expr_stmt.expr, ctx),
        },
        Stmt::While(while_stmt) => lower_while(while_stmt, ctx),
        Stmt::If(if_stmt) => lower_if_stmt(if_stmt, ctx),
        Stmt::Break(_) => VirStmt::Break,
        Stmt::Continue(_) => VirStmt::Continue,
        Stmt::Raise(raise_stmt) => lower_raise(raise_stmt, ctx),
        Stmt::Let(let_stmt) => lower_let(let_stmt, ctx),
        Stmt::For(for_stmt) => lower_for(for_stmt, ctx),
        Stmt::Return(ret) => {
            let value = ret.value.as_ref().map(|v| lower_expr(v, ctx));
            let convention = classify_return_convention(ctx.func_return_type, ctx);
            VirStmt::Return { value, convention }
        }
        Stmt::LetTuple(let_tuple) => {
            let value = lower_expr(&let_tuple.init, ctx);
            let init_ty = ctx
                .node_map
                .get_type(let_tuple.init.id)
                .unwrap_or(TypeId::UNKNOWN);
            let pattern = lower_destructure_pattern(&let_tuple.pattern, init_ty, ctx);
            let vir_init_ty = ctx.translate(init_ty);
            VirStmt::LetTuple {
                pattern,
                value,
                init_ty: vir_init_ty,
                vir_init_ty,
            }
        }
    }
}

/// Lower a while statement to `VirStmt::While`.
///
/// The condition expression and body statements are recursively lowered.
fn lower_while(while_stmt: &vole_frontend::ast::WhileStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let cond = lower_expr(&while_stmt.condition, ctx);
    let body = lower_stmts(&while_stmt.body.stmts, ctx);
    VirStmt::While { cond, body }
}

/// Lower a raise statement to `VirStmt::Raise`.
///
/// The error name and field value expressions are extracted from the AST.
/// Field values are recursively lowered through `lower_expr`.
fn lower_raise(raise_stmt: &vole_frontend::ast::RaiseStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let fields = raise_stmt
        .fields
        .iter()
        .map(|f| (f.name, lower_expr(&f.value, ctx)))
        .collect();
    VirStmt::Raise {
        error_name: raise_stmt.error_name,
        fields,
    }
}

/// Lower a let statement to `VirStmt::Let`.
///
/// Type aliases (`let T = i32 | i64`) produce no runtime code; they are
/// lowered to `VirStmt::Noop`.
///
/// The binding type (`ty`) comes from:
/// 1. The declared type annotation (via `node_map.get_declared_var_type`),
///    if one was provided in the source -- this is the type the codegen
///    should coerce to.
/// 2. Otherwise, the sema-computed expression type.
fn lower_let(let_stmt: &LetStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let init_expr = match &let_stmt.init {
        LetInit::Expr(e) => e,
        // Type aliases produce no runtime code -- skip entirely.
        LetInit::TypeAlias(_) => {
            return VirStmt::Noop;
        }
    };

    let value = lower_expr(init_expr, ctx);

    // Determine the binding type: use declared type if annotated, else the
    // init expression's inferred type.
    let declared_ty = ctx.node_map.get_declared_var_type(init_expr.id);
    let expr_ty = if matches!(&init_expr.kind, ExprKind::MethodCall(_) | ExprKind::Call(_)) {
        ctx.node_map
            .get_substituted_return_type(init_expr.id)
            .or_else(|| ctx.node_map.get_type(init_expr.id))
            .unwrap_or(TypeId::UNKNOWN)
    } else {
        ctx.node_map
            .get_type(init_expr.id)
            .unwrap_or(TypeId::UNKNOWN)
    };
    let ty = declared_ty.unwrap_or(expr_ty);

    let vir_ty = ctx.translate(ty);
    let sema_ty = ctx.compat_ty(ty);
    let storage = classify_let_storage(ty, expr_ty, ctx);
    let declared_type = declared_ty.map(|dt| ctx.compat_ty(dt));
    VirStmt::Let {
        name: let_stmt.name,
        value,
        mutable: let_stmt.mutable,
        ty: sema_ty,
        vir_ty,
        storage,
        declared_type,
    }
}

/// Classify the storage kind for a let binding based on its declared type.
///
/// Mirrors the decision logic in codegen's `coerce_let_init`, which queries
/// the arena at compile time to determine: unknown → box to TaggedValue,
/// union → stack-allocate tag+payload, interface → interface boxing,
/// numeric → widen/narrow, else → scalar pass-through.
///
/// When the binding type is a union, `init_ty` (the init expression's type)
/// is used to pre-compute the variant tag, RC state, and coercion target.
fn classify_let_storage(ty: TypeId, init_ty: TypeId, ctx: &mut LoweringCtx<'_>) -> LetStorageHint {
    if ctx.type_arena.is_unknown(ty) {
        LetStorageHint::Unknown
    } else if ctx.type_arena.is_union(ty) {
        let tag_hint = compute_union_tag_hint(ty, init_ty, ctx);
        LetStorageHint::Union { tag_hint }
    } else if ctx.type_arena.is_interface(ty) {
        LetStorageHint::Interface
    } else if ctx.type_arena.is_numeric(ty) {
        LetStorageHint::Numeric
    } else {
        LetStorageHint::Scalar
    }
}

/// Pre-compute the union variant tag for a value-to-union coercion.
///
/// Returns `None` when the tag cannot be determined statically:
/// - The init type is already a union (codegen passes through)
/// - The init type contains type parameters (generic context)
/// - The init type is unknown
/// - No matching variant is found in the union
///
/// Mirrors the variant-matching logic in codegen's `find_union_variant_tag`:
/// 1. Exact type match against variants
/// 2. Sentinel type fallback (unique sentinel variant)
/// 3. Integer compatibility fallback (i32 init → i64 variant)
fn compute_union_tag_hint(
    union_ty: TypeId,
    init_ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> Option<UnionTagHint> {
    // Cannot pre-compute if the init type is already a union, unknown, or
    // contains unresolved type parameters.
    if ctx.type_arena.is_union(init_ty)
        || init_ty == TypeId::UNKNOWN
        || ctx.type_arena.contains_type_param(init_ty)
    {
        return None;
    }
    // In generic lowering mode, the init type may not be fully resolved.
    if ctx.generic {
        return None;
    }

    let variants = ctx.type_arena.unwrap_union(union_ty)?;
    let variants = variants.to_vec();

    // 1. Exact type match
    if let Some(pos) = variants.iter().position(|&v| v == init_ty) {
        return Some(build_tag_hint(pos, variants[pos], ctx));
    }

    // 2. Sentinel fallback: if init is a sentinel and there's exactly one
    //    sentinel variant, use it.
    if ctx.type_arena.is_sentinel(init_ty) {
        let sentinel_variants: Vec<(usize, TypeId)> = variants
            .iter()
            .enumerate()
            .filter_map(|(i, &v)| ctx.type_arena.is_sentinel(v).then_some((i, v)))
            .collect();
        if sentinel_variants.len() == 1 {
            let (pos, variant_ty) = sentinel_variants[0];
            return Some(build_tag_hint(pos, variant_ty, ctx));
        }
    }

    // 3. Integer compatibility: find a compatible integer variant for
    //    widening/narrowing (e.g. i32 init → i64 union variant).
    if ctx.type_arena.is_integer(init_ty)
        && let Some((pos, &variant_ty)) = variants
            .iter()
            .enumerate()
            .find(|(_, v)| ctx.type_arena.is_integer(**v))
    {
        return Some(build_tag_hint(pos, variant_ty, ctx));
    }

    // Cannot determine the tag statically.
    None
}

/// Build a `UnionTagHint` from a resolved variant position and type.
fn build_tag_hint(pos: usize, variant_ty: TypeId, ctx: &mut LoweringCtx<'_>) -> UnionTagHint {
    let is_rc = is_simple_rc_type(ctx.type_arena, variant_ty);
    let variant_type = ctx.translate(variant_ty);
    UnionTagHint {
        tag: pos as u8,
        is_rc,
        variant_type,
    }
}

/// Check if a sema type is a simple RC type (needs cleanup via rc_dec).
///
/// Mirrors the logic in codegen's `is_simple_rc_type` (rc_state.rs) but
/// operates on `TypeArena` queries available during VIR lowering.
fn is_simple_rc_type(arena: &crate::type_arena::TypeArena, ty: TypeId) -> bool {
    arena.is_string(ty)
        || arena.is_array(ty)
        || arena.is_function(ty)
        || arena.is_class(ty)
        || arena.is_handle(ty)
        || arena.is_runtime_iterator(ty)
        || arena.is_interface(ty)
}

/// Classify the return convention for a function based on its return type.
///
/// Mirrors the 7-way dispatch in codegen's `emit_return_value`, using
/// `TypeArena` queries available during VIR lowering.  The result is stored
/// on `VirStmt::Return` so codegen reads the decision rather than querying
/// the arena at compile time.
///
/// For struct returns, codegen further splits into small (register) vs sret
/// (stack pointer) based on the flat slot count — that detail is left to
/// codegen since it depends on `MAX_SMALL_STRUCT_FIELDS`, a codegen constant.
fn classify_return_convention(return_type: TypeId, ctx: &LoweringCtx<'_>) -> ReturnConvention {
    // If the return type contains unresolved type parameters (e.g., sema-side
    // monomorphized method where the return type references a class type param),
    // we cannot determine the convention now.  Mark as Unresolved so codegen
    // falls back to the old type-query dispatch.
    //
    // Also guard against function types: some lowering paths (e.g.,
    // `lower_single_method`) pass the method's *signature* TypeId (a function
    // type like `(K) -> V?`) as the return type.  A function type is never a
    // valid return convention, so mark it Unresolved and let codegen resolve
    // from the real return type it sees at compile time.
    if ctx.type_arena.contains_type_param(return_type) || ctx.type_arena.is_function(return_type) {
        return ReturnConvention::Unresolved;
    }
    if ctx.type_arena.is_void(return_type) {
        return ReturnConvention::Void;
    }
    if ctx.type_arena.is_interface(return_type) {
        return ReturnConvention::InterfaceBox;
    }
    if ctx.type_arena.is_unknown(return_type) {
        return ReturnConvention::UnknownBox;
    }
    if let Some((success_ty, _)) = ctx.type_arena.unwrap_fallible(return_type) {
        if matches!(success_ty, TypeId::I128 | TypeId::F128) {
            return ReturnConvention::WideFallible;
        }
        return ReturnConvention::Fallible;
    }
    if ctx.type_arena.is_struct(return_type) {
        return ReturnConvention::Struct;
    }
    if ctx.type_arena.is_union(return_type) {
        return ReturnConvention::Union;
    }
    ReturnConvention::Scalar
}

/// Lower a for statement to `VirStmt::For`.
///
/// Looks up the `IterableKind` from the NodeMap (annotated by sema) and
/// maps it to a `VirIterKind`.  The iterable expression, loop body, and
/// iteration variable are recursively lowered.
fn lower_for(for_stmt: &vole_frontend::ast::ForStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let iterable = lower_expr(&for_stmt.iterable, ctx);
    let body = lower_stmts(&for_stmt.body.stmts, ctx);

    let sema_kind = ctx.node_map.get_iterable_kind(for_stmt.iterable.id);

    let kind = match sema_kind {
        Some(IterableKind::Range) => VirIterKind::Range,
        Some(IterableKind::Array { elem_type }) => {
            let union_storage = ctx.node_map.get_union_storage_kind(for_stmt.iterable.id);
            VirIterKind::Array {
                elem_type: ctx.translate(elem_type),
                vir_elem_type: ctx.translate(elem_type),
                union_storage,
            }
        }
        Some(IterableKind::String) => VirIterKind::String,
        Some(IterableKind::IteratorInterface { elem_type }) => VirIterKind::IteratorInterface {
            elem_type: ctx.translate(elem_type),
            vir_elem_type: ctx.translate(elem_type),
        },
        Some(IterableKind::CustomIterator { elem_type }) => VirIterKind::CustomIterator {
            elem_type: ctx.translate(elem_type),
            vir_elem_type: ctx.translate(elem_type),
        },
        Some(IterableKind::CustomIterable { elem_type }) => VirIterKind::CustomIterable {
            elem_type: ctx.translate(elem_type),
            vir_elem_type: ctx.translate(elem_type),
        },
        Some(IterableKind::Generic { elem_type }) => VirIterKind::Generic {
            elem_type: ctx.translate(elem_type),
            vir_elem_type: ctx.translate(elem_type),
        },
        None if ctx.generic => {
            // Generic mode: missing iterable kind is expected when the
            // iterable type is a bare type parameter.  Use the iterable
            // expression's sema type to derive a best-effort element type.
            let iter_ty = ctx
                .node_map
                .get_type(for_stmt.iterable.id)
                .unwrap_or(TypeId::UNKNOWN);
            VirIterKind::Generic {
                elem_type: ctx.translate(iter_ty),
                vir_elem_type: ctx.translate(iter_ty),
            }
        }
        None => {
            // Concrete mode fallback for error types -- treat as array of i64.
            VirIterKind::Array {
                elem_type: ctx.translate(TypeId::I64),
                vir_elem_type: ctx.translate(TypeId::I64),
                union_storage: None,
            }
        }
    };

    // Determine the element type for the loop variable.
    let var_type = match kind {
        VirIterKind::Range => ctx.translate(TypeId::I64),
        VirIterKind::Array { elem_type, .. } => elem_type,
        VirIterKind::String => ctx.translate(TypeId::STRING),
        VirIterKind::IteratorInterface { elem_type, .. }
        | VirIterKind::CustomIterator { elem_type, .. }
        | VirIterKind::CustomIterable { elem_type, .. }
        | VirIterKind::Generic { elem_type, .. } => elem_type,
    };

    let vir_var_type = var_type;
    VirStmt::For(VirFor {
        var_name: for_stmt.var_name,
        var_type,
        vir_var_type,
        iterable,
        body,
        kind,
    })
}

/// Lower an if statement to `VirStmt::Expr { VirExpr::If { ... } }`.
///
/// Vole's VIR has no separate `VirStmt::If` -- statement-level `if` is
/// wrapped as a void-typed `VirExpr::If` inside `VirStmt::Expr`.
fn lower_if_stmt(if_stmt: &vole_frontend::ast::IfStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let cond = lower_expr(&if_stmt.condition, ctx);
    let then_body = lower_stmts(&if_stmt.then_branch.stmts, ctx);
    let else_body = if_stmt
        .else_branch
        .as_ref()
        .map(|block| lower_stmts(&block.stmts, ctx));
    let vir_ty = ctx.translate(TypeId::VOID);
    VirStmt::Expr {
        value: Box::new(VirExpr::If {
            cond,
            then_body,
            else_body,
            ty: vir_ty,
            vir_ty,
        }),
    }
}

// ---------------------------------------------------------------------------
// LetTuple destructuring pattern lowering
// ---------------------------------------------------------------------------

/// Lower an AST `Pattern` to a `VirDestructurePattern`.
///
/// Handles the four `PatternKind` variants used in `LetTuple`:
/// - `Identifier` -> `VirDestructurePattern::Bind`
/// - `Wildcard` -> `VirDestructurePattern::Wildcard`
/// - `Tuple` -> `VirDestructurePattern::Tuple` (recursive)
/// - `Record` -> `VirDestructurePattern::Record` or `Module`
///
/// The `ty` parameter is the type of the value being destructured at this
/// level of nesting (the init expression's type at the top level, or the
/// element/field type for nested patterns).
fn lower_destructure_pattern(
    pattern: &vole_frontend::Pattern,
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirDestructurePattern {
    match &pattern.kind {
        PatternKind::Identifier { name } => {
            let vir_ty = ctx.translate(ty);
            VirDestructurePattern::Bind {
                name: *name,
                ty: vir_ty,
                vir_ty,
            }
        }
        PatternKind::Wildcard => VirDestructurePattern::Wildcard,
        PatternKind::Tuple { elements } => lower_destructure_tuple(elements, ty, ctx),
        PatternKind::Record { fields, .. } => lower_destructure_record(fields, ty, ctx),
        // LetTuple patterns should only contain the above variants.
        // Other pattern kinds (Literal, Type, Val, Success, Error) are match-only.
        _ => VirDestructurePattern::Wildcard,
    }
}

/// Lower a tuple/fixed-array destructuring pattern.
///
/// Pre-resolves element types from `TypeArena::unwrap_tuple` or
/// `unwrap_fixed_array`.  Each element pattern is recursively lowered.
fn lower_destructure_tuple(
    elements: &[vole_frontend::Pattern],
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirDestructurePattern {
    // Try tuple first.
    if let Some(elem_types) = ctx.type_arena.unwrap_tuple(ty).cloned() {
        let elems = elements
            .iter()
            .enumerate()
            .map(|(i, pat)| {
                let elem_ty = elem_types.get(i).copied().unwrap_or(TypeId::UNKNOWN);
                let vir_ty = ctx.translate(elem_ty);
                VirDestructureElement {
                    pattern: lower_destructure_pattern(pat, elem_ty, ctx),
                    ty: vir_ty,
                    vir_ty,
                }
            })
            .collect();
        return VirDestructurePattern::Tuple {
            elements: elems,
            kind: DestructureTupleKind::Tuple,
        };
    }

    // Try fixed array.
    if let Some((elem_ty, _len)) = ctx.type_arena.unwrap_fixed_array(ty) {
        let vir_elem_ty = ctx.translate(elem_ty);
        let elems = elements
            .iter()
            .map(|pat| VirDestructureElement {
                pattern: lower_destructure_pattern(pat, elem_ty, ctx),
                ty: vir_elem_ty,
                vir_ty: vir_elem_ty,
            })
            .collect();
        return VirDestructurePattern::Tuple {
            elements: elems,
            kind: DestructureTupleKind::FixedArray {
                elem_ty: vir_elem_ty,
                vir_elem_ty,
            },
        };
    }

    // Fallback: unknown element types.
    let vir_unknown = ctx.translate(TypeId::UNKNOWN);
    let elems = elements
        .iter()
        .map(|pat| VirDestructureElement {
            pattern: lower_destructure_pattern(pat, TypeId::UNKNOWN, ctx),
            ty: vir_unknown,
            vir_ty: vir_unknown,
        })
        .collect();
    VirDestructurePattern::Tuple {
        elements: elems,
        kind: DestructureTupleKind::Tuple,
    }
}

/// Lower a record destructuring pattern to `Record` or `Module`.
///
/// Checks whether the type is a module (compile-time only bindings) or a
/// nominal type (struct/class with runtime field extraction).
fn lower_destructure_record(
    fields: &[vole_frontend::ast::RecordFieldPattern],
    ty: TypeId,
    ctx: &mut LoweringCtx<'_>,
) -> VirDestructurePattern {
    // Module destructuring: `let { A, B } = import "mod"`
    if let Some(module_info) = ctx.type_arena.unwrap_module(ty) {
        let bindings = fields
            .iter()
            .filter_map(|f| {
                let export_name_str = ctx.interner.resolve(f.field_name);
                let export_ty = module_info.exports.iter().find_map(|(name_id, ty)| {
                    let name = ctx.name_table.last_segment_str(*name_id);
                    if name.as_deref() == Some(export_name_str) {
                        Some(*ty)
                    } else {
                        None
                    }
                })?;
                let vir_export_ty = ctx.translate(export_ty);
                Some(VirModuleBinding {
                    export_name: f.field_name,
                    binding: f.binding,
                    export_ty: vir_export_ty,
                    vir_export_ty,
                })
            })
            .collect();
        return VirDestructurePattern::Module {
            bindings,
            module_id: module_info.module_id,
        };
    }

    // Struct/class destructuring: `let { x, y } = point`
    let type_def_id = ctx
        .type_arena
        .unwrap_nominal(ty)
        .map(|(def_id, _, _)| def_id);
    let is_struct = ctx.type_arena.is_struct(ty);

    let vir_fields = fields
        .iter()
        .map(|f| {
            let (slot, field_ty) = type_def_id
                .and_then(|def_id| find_destructure_field(def_id, f.field_name, ctx))
                .unwrap_or((0, TypeId::UNKNOWN));
            let vir_ty = ctx.translate(field_ty);
            VirDestructureField {
                field_name: f.field_name,
                binding: f.binding,
                slot,
                ty: vir_ty,
                vir_ty,
            }
        })
        .collect();

    let vir_source_ty = ctx.translate(ty);
    VirDestructurePattern::Record {
        fields: vir_fields,
        source_ty: vir_source_ty,
        vir_source_ty,
        is_struct,
    }
}

/// Find a field's slot index and type in a type definition.
///
/// Looks up the field by name in the entity registry and returns
/// `(slot, type_id)`.
fn find_destructure_field(
    type_def_id: vole_identity::TypeDefId,
    field_name: vole_identity::Symbol,
    ctx: &LoweringCtx<'_>,
) -> Option<(u32, TypeId)> {
    let field_name_str = ctx.interner.resolve(field_name);
    for field_id in ctx.entities.fields_on_type(type_def_id) {
        let field = ctx.entities.get_field(field_id);
        let name = ctx.name_table.last_segment_str(field.name_id);
        if name.as_deref() == Some(field_name_str) {
            return Some((field.slot as u32, field.ty));
        }
    }
    None
}
