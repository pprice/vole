// vir_lower/stmt.rs
//
// Statement lowering: AST `Stmt` → VIR `VirStmt`.

use vole_frontend::PatternKind;
use vole_frontend::ast::{LetInit, LetStmt, Stmt};
use vole_identity::TypeId;
use vole_sema::IterableKind;

use vole_vir::expr::VirExpr;
use vole_vir::stmt::{
    DestructureTupleKind, VirDestructureElement, VirDestructureField, VirDestructurePattern,
    VirFor, VirIterKind, VirModuleBinding, VirStmt,
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
pub(crate) fn lower_stmt(stmt: &Stmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
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
            VirStmt::Return { value }
        }
        Stmt::LetTuple(let_tuple) => {
            let value = lower_expr(&let_tuple.init, ctx);
            let init_ty = ctx
                .node_map
                .get_type(let_tuple.init.id)
                .unwrap_or(TypeId::UNKNOWN);
            let pattern = lower_destructure_pattern(&let_tuple.pattern, init_ty, ctx);
            VirStmt::LetTuple {
                pattern,
                value,
                init_ty,
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
///    if one was provided in the source — this is the type the codegen
///    should coerce to.
/// 2. Otherwise, the sema-computed expression type.
fn lower_let(let_stmt: &LetStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let init_expr = match &let_stmt.init {
        LetInit::Expr(e) => e,
        // Type aliases produce no runtime code — skip entirely.
        LetInit::TypeAlias(_) => {
            return VirStmt::Noop;
        }
    };

    let value = lower_expr(init_expr, ctx);

    // Determine the binding type: use declared type if annotated, else the
    // init expression's inferred type.
    let declared_ty = ctx.node_map.get_declared_var_type(init_expr.id);
    let expr_ty = ctx
        .node_map
        .get_type(init_expr.id)
        .unwrap_or(TypeId::UNKNOWN);
    let ty = declared_ty.unwrap_or(expr_ty);

    VirStmt::Let {
        name: let_stmt.name,
        value,
        mutable: let_stmt.mutable,
        ty,
    }
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
                elem_type,
                union_storage,
            }
        }
        Some(IterableKind::String) => VirIterKind::String,
        Some(IterableKind::IteratorInterface { elem_type }) => {
            VirIterKind::IteratorInterface { elem_type }
        }
        Some(IterableKind::CustomIterator { elem_type }) => {
            VirIterKind::CustomIterator { elem_type }
        }
        Some(IterableKind::CustomIterable { elem_type }) => {
            VirIterKind::CustomIterable { elem_type }
        }
        None => {
            // Fallback for error types — treat as array of i64.
            VirIterKind::Array {
                elem_type: TypeId::I64,
                union_storage: None,
            }
        }
    };

    // Determine the element type for the loop variable.
    let var_type = match kind {
        VirIterKind::Range => TypeId::I64,
        VirIterKind::Array { elem_type, .. } => elem_type,
        VirIterKind::String => TypeId::STRING,
        VirIterKind::IteratorInterface { elem_type }
        | VirIterKind::CustomIterator { elem_type }
        | VirIterKind::CustomIterable { elem_type } => elem_type,
    };

    VirStmt::For(VirFor {
        var_name: for_stmt.var_name,
        var_type,
        iterable,
        body,
        kind,
    })
}

/// Lower an if statement to `VirStmt::Expr { VirExpr::If { ... } }`.
///
/// Vole's VIR has no separate `VirStmt::If` — statement-level `if` is
/// wrapped as a void-typed `VirExpr::If` inside `VirStmt::Expr`.
fn lower_if_stmt(if_stmt: &vole_frontend::ast::IfStmt, ctx: &mut LoweringCtx<'_>) -> VirStmt {
    let cond = lower_expr(&if_stmt.condition, ctx);
    let then_body = lower_stmts(&if_stmt.then_branch.stmts, ctx);
    let else_body = if_stmt
        .else_branch
        .as_ref()
        .map(|block| lower_stmts(&block.stmts, ctx));
    VirStmt::Expr {
        value: Box::new(VirExpr::If {
            cond,
            then_body,
            else_body,
            ty: TypeId::VOID,
        }),
    }
}

// ---------------------------------------------------------------------------
// LetTuple destructuring pattern lowering
// ---------------------------------------------------------------------------

/// Lower an AST `Pattern` to a `VirDestructurePattern`.
///
/// Handles the four `PatternKind` variants used in `LetTuple`:
/// - `Identifier` → `VirDestructurePattern::Bind`
/// - `Wildcard` → `VirDestructurePattern::Wildcard`
/// - `Tuple` → `VirDestructurePattern::Tuple` (recursive)
/// - `Record` → `VirDestructurePattern::Record` or `Module`
///
/// The `ty` parameter is the type of the value being destructured at this
/// level of nesting (the init expression's type at the top level, or the
/// element/field type for nested patterns).
fn lower_destructure_pattern(
    pattern: &vole_frontend::Pattern,
    ty: TypeId,
    ctx: &LoweringCtx<'_>,
) -> VirDestructurePattern {
    match &pattern.kind {
        PatternKind::Identifier { name } => VirDestructurePattern::Bind { name: *name, ty },
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
    ctx: &LoweringCtx<'_>,
) -> VirDestructurePattern {
    // Try tuple first.
    if let Some(elem_types) = ctx.type_arena.unwrap_tuple(ty).cloned() {
        let elems = elements
            .iter()
            .enumerate()
            .map(|(i, pat)| {
                let elem_ty = elem_types.get(i).copied().unwrap_or(TypeId::UNKNOWN);
                VirDestructureElement {
                    pattern: lower_destructure_pattern(pat, elem_ty, ctx),
                    ty: elem_ty,
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
        let elems = elements
            .iter()
            .map(|pat| VirDestructureElement {
                pattern: lower_destructure_pattern(pat, elem_ty, ctx),
                ty: elem_ty,
            })
            .collect();
        return VirDestructurePattern::Tuple {
            elements: elems,
            kind: DestructureTupleKind::FixedArray { elem_ty },
        };
    }

    // Fallback: unknown element types.
    let elems = elements
        .iter()
        .map(|pat| VirDestructureElement {
            pattern: lower_destructure_pattern(pat, TypeId::UNKNOWN, ctx),
            ty: TypeId::UNKNOWN,
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
    ctx: &LoweringCtx<'_>,
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
                Some(VirModuleBinding {
                    export_name: f.field_name,
                    binding: f.binding,
                    export_ty,
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
            VirDestructureField {
                field_name: f.field_name,
                binding: f.binding,
                slot,
                ty: field_ty,
            }
        })
        .collect();

    VirDestructurePattern::Record {
        fields: vir_fields,
        source_ty: ty,
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
