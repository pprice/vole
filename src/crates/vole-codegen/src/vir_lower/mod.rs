// vir_lower/mod.rs
//
// AST-to-VIR lowering.
//
// Walks the AST and lowers all expression and statement kinds to typed VIR
// nodes.  Every `ExprKind` variant maps to a concrete `VirExpr` variant
// (no escape hatches).  A few VIR nodes still carry AST fragments for
// codegen dispatch (`MethodCall`, `OptionalMethodCall`).  All pattern kinds
// (including Record) are fully lowered to concrete `VirPattern` variants.

pub(crate) mod expr;
pub(crate) mod stmt;

#[cfg(test)]
mod tests;

use vole_frontend::ast::{FuncBody, FuncDecl, InterfaceMethod};
use vole_identity::{FunctionId, Interner, MethodId, NameId, NameTable, Symbol, TypeId};
use vole_sema::node_map::NodeMap;
use vole_sema::{EntityRegistry, TypeArena};

use vole_vir::func::{VirBody, VirFunction};

use self::expr::lower_expr;
use self::stmt::lower_stmt;

/// Shared lowering context threaded through all lowering helpers.
///
/// Bundles the sema outputs needed during AST-to-VIR lowering:
/// - `node_map`: per-node sema annotations (types, dispatch info, etc.)
/// - `interner`: string interning (mutable for new literals)
/// - `type_arena`: type resolution (unwrap_union, unwrap_fallible, etc.)
/// - `entities`: entity lookups (field info, error types, etc.)
/// - `name_table`: name resolution (last_segment_str for error tag matching)
pub(crate) struct LoweringCtx<'a> {
    pub node_map: &'a NodeMap,
    pub interner: &'a mut Interner,
    pub type_arena: &'a TypeArena,
    pub entities: &'a EntityRegistry,
    pub name_table: &'a NameTable,
}

/// Lower a single function declaration into a `VirFunction`.
///
/// `func_id`, `name`, `param_types`, and `return_type` come from the sema
/// entity registry — they are resolved during semantic analysis and passed
/// in by the caller (the compilation pipeline).
///
/// `node_map` is used by expression lowering to look up sema-computed types,
/// is-check results, optional chain info, and other annotations.
///
/// `type_arena` and `entities` are threaded into the lowering context for
/// future use by pattern lowering.
#[allow(clippy::too_many_arguments)]
pub fn lower_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
    };
    let body = lower_func_body(&func.body, &mut ctx);
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
    entities: &EntityRegistry,
    name_table: &NameTable,
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
        type_arena,
        entities,
        name_table,
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
#[allow(clippy::too_many_arguments)]
pub fn lower_method(
    func: &FuncDecl,
    method_id: MethodId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
    };
    let body = lower_func_body(&func.body, &mut ctx);
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
#[allow(clippy::too_many_arguments)]
pub fn lower_interface_method(
    method: &InterfaceMethod,
    method_id: MethodId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
) -> Option<VirFunction> {
    let body_ast = method.body.as_ref()?;
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
    };
    let body = lower_func_body(body_ast, &mut ctx);
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
pub fn lower_test_body(
    body: &FuncBody,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
) -> VirBody {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
    };
    lower_func_body(body, &mut ctx)
}

/// Lower a `FuncBody` (block or expression) into a `VirBody`.
///
/// Block bodies have their statements walked individually; expression bodies
/// become a single trailing VIR expression.
pub(crate) fn lower_func_body(body: &FuncBody, ctx: &mut LoweringCtx<'_>) -> VirBody {
    match body {
        FuncBody::Block(block) => lower_stmts(&block.stmts, ctx),
        FuncBody::Expr(expr) => {
            let trailing = lower_expr(expr, ctx);
            VirBody {
                stmts: Vec::new(),
                trailing: Some(trailing),
            }
        }
    }
}

/// Lower a slice of AST statements into a `VirBody`.
///
/// Each statement is fully lowered to a typed `VirStmt` node via
/// `lower_stmt`.  Expression statements have their inner expression
/// lowered recursively through `lower_expr`.
pub(crate) fn lower_stmts(
    stmts: &[vole_frontend::ast::Stmt],
    ctx: &mut LoweringCtx<'_>,
) -> VirBody {
    let vir_stmts = stmts.iter().map(|s| lower_stmt(s, ctx)).collect();
    VirBody {
        stmts: vir_stmts,
        trailing: None,
    }
}
