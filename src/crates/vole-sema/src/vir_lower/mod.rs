// vir_lower/mod.rs
//
// AST-to-VIR lowering.
//
// Walks the AST and lowers all expression and statement kinds to typed VIR
// nodes.  Every `ExprKind` variant maps to a concrete `VirExpr` variant
// (no escape hatches). Method calls carry explicit VIR dispatch metadata.
// All pattern kinds (including Record) are fully lowered to concrete
// `VirPattern` variants.

pub mod expr;
pub mod stmt;
pub mod type_translate;

#[cfg(test)]
mod tests;

use vole_frontend::ast::{FuncBody, FuncDecl, InterfaceMethod};
use vole_identity::{
    FunctionId, Interner, MethodId, NameId, NameTable, NodeId, Symbol, TypeDefId, TypeId, VirTypeId,
};

use crate::node_map::NodeMap;
use crate::{EntityRegistry, TypeArena};

use vole_vir::func::{VirBody, VirFunction};
use vole_vir::type_table::VirTypeTable;

use self::expr::lower_expr;
use self::stmt::lower_stmt;
use self::type_translate::translate_type_id;

/// Shared lowering context threaded through all lowering helpers.
///
/// Bundles the sema outputs needed during AST-to-VIR lowering:
/// - `node_map`: per-node sema annotations (types, dispatch info, etc.)
/// - `interner`: string interning (mutable for new literals)
/// - `type_arena`: type resolution (unwrap_union, unwrap_fallible, etc.)
/// - `entities`: entity lookups (field info, error types, etc.)
/// - `name_table`: name resolution (last_segment_str for error tag matching)
/// - `type_table`: VIR type interning table (populated during lowering)
pub struct LoweringCtx<'a> {
    pub node_map: &'a NodeMap,
    pub interner: &'a mut Interner,
    pub type_arena: &'a TypeArena,
    pub entities: &'a EntityRegistry,
    pub name_table: &'a NameTable,
    pub type_table: &'a mut VirTypeTable,
    /// When `true`, NodeMap lookups that would normally panic on missing
    /// entries instead produce placeholder/generic values.  Used when
    /// lowering generic function bodies where sema decision data may be
    /// absent for type-parameter-dependent expressions.
    ///
    /// Default: `false` (concrete mode — existing strict behaviour).
    pub generic: bool,
    /// The return type of the enclosing function.
    ///
    /// Used to pre-compute the `ReturnConvention` on `VirStmt::Return`
    /// nodes.  `VOID` for test bodies and void-returning functions.
    pub func_return_type: TypeId,
}

impl LoweringCtx<'_> {
    /// Translate a sema `TypeId` to a `VirTypeId`, interning into the type table.
    pub fn translate(&mut self, type_id: TypeId) -> VirTypeId {
        translate_type_id(self.type_table, type_id, self.type_arena)
    }

    /// Compatibility `VirTypeId` for mixed migration fields.
    ///
    /// Prefer a true translated VIR ID when available; when translation yields
    /// `UNKNOWN` for a non-unknown sema type (for types not represented in
    /// `VirTypeTable` yet), preserve the raw sema ID so legacy bridges can
    /// still recover the original `TypeId`.
    pub fn compat_ty(&mut self, type_id: TypeId) -> VirTypeId {
        let vir_ty = self.translate(type_id);
        if vir_ty == VirTypeId::UNKNOWN && type_id != TypeId::UNKNOWN {
            VirTypeId::from_raw(type_id.raw())
        } else {
            vir_ty
        }
    }

    // -- Tolerant NodeMap query helpers -------------------------------------
    //
    // In generic mode (`self.generic == true`), these helpers return a
    // placeholder value instead of panicking when sema decision data is
    // missing.  In concrete mode they panic exactly as before.

    /// Get the `IsCheckResult` for a node, with a tolerant fallback in
    /// generic mode.
    ///
    /// Concrete mode: panics if missing (existing behaviour).
    /// Generic mode: returns `CheckUnknown(UNKNOWN)` if missing.
    pub fn require_is_check_result(&mut self, node_id: NodeId, line: u32) -> crate::IsCheckResult {
        match self.node_map.get_is_check_result(node_id) {
            Some(result) => result,
            None if self.generic => crate::IsCheckResult::CheckUnknown(TypeId::UNKNOWN),
            None => panic!(
                "VIR lower: missing sema is_check_result for NodeId {node_id:?} (line {line})"
            ),
        }
    }

    /// Get the `MetaAccessKind` for a node, with a tolerant fallback in
    /// generic mode.
    ///
    /// Concrete mode: panics if missing (existing behaviour).
    /// Generic mode: returns `Dynamic` as a safe placeholder.
    pub fn require_meta_access(
        &self,
        node_id: NodeId,
        line: u32,
    ) -> crate::node_map::MetaAccessKind {
        match self.node_map.get_meta_access(node_id) {
            Some(kind) => kind,
            None if self.generic => crate::node_map::MetaAccessKind::Dynamic,
            None => {
                panic!("VIR lower: missing sema meta_access for NodeId {node_id:?} (line {line})")
            }
        }
    }

    /// Get the `OptionalChainInfo` for a node, with a tolerant fallback
    /// in generic mode.
    ///
    /// Concrete mode: panics if missing.
    /// Generic mode: returns a minimal placeholder with UNKNOWN types.
    pub fn require_optional_chain(
        &self,
        node_id: NodeId,
        line: u32,
    ) -> crate::node_map::OptionalChainInfo {
        match self.node_map.get_optional_chain(node_id) {
            Some(info) => info.clone(),
            None if self.generic => crate::node_map::OptionalChainInfo {
                object_type: TypeId::UNKNOWN,
                inner_type: TypeId::UNKNOWN,
                result_type: TypeId::UNKNOWN,
                kind: crate::node_map::OptionalChainKind::FieldAccess {
                    field: Symbol::UNKNOWN,
                },
            },
            None => panic!(
                "VIR lower: missing sema optional_chain for NodeId {node_id:?} (line {line})"
            ),
        }
    }

    /// Get the `StructLiteralInfo` for a node, with a tolerant fallback
    /// in generic mode.
    ///
    /// Concrete mode: panics if missing.
    /// Generic mode: returns a placeholder with a zeroed TypeDefId and
    /// `is_class = false`.
    pub fn require_struct_literal_info(
        &self,
        node_id: NodeId,
        line: u32,
    ) -> crate::node_map::StructLiteralInfo {
        match self.node_map.get_struct_literal_info(node_id) {
            Some(info) => info,
            None if self.generic => crate::node_map::StructLiteralInfo {
                type_def_id: TypeDefId::new(0),
                is_class: false,
            },
            None => panic!(
                "VIR lower: missing sema struct_literal_info for NodeId {node_id:?} (line {line})"
            ),
        }
    }
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
    type_table: &mut VirTypeTable,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        generic: false,
        func_return_type: return_type,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let body = lower_func_body(&func.body, &mut ctx);
    VirFunction {
        id: func_id,
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        body,
        mangled_name_id: None,
        method_id: None,
        type_params: Vec::new(),
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
    type_table: &mut VirTypeTable,
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
        type_table,
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
    type_table: &mut VirTypeTable,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        generic: false,
        func_return_type: return_type,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let body = lower_func_body(&func.body, &mut ctx);
    VirFunction {
        id: FunctionId::new(0), // dummy — methods use method_id for lookup
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        body,
        mangled_name_id: None,
        method_id: Some(method_id),
        type_params: Vec::new(),
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
    type_table: &mut VirTypeTable,
) -> Option<VirFunction> {
    let body_ast = method.body.as_ref()?;
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        generic: false,
        func_return_type: return_type,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let body = lower_func_body(body_ast, &mut ctx);
    Some(VirFunction {
        id: FunctionId::new(0), // dummy — methods use method_id for lookup
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        body,
        mangled_name_id: None,
        method_id: Some(method_id),
        type_params: Vec::new(),
    })
}

/// Lower a generic function declaration into a `VirFunction` template.
///
/// Like [`lower_function`], but uses `generic: true` mode so that missing
/// or type-parameter-dependent NodeMap entries produce placeholder values
/// instead of panicking.  The `param_types` and `return_type` should contain
/// abstract `TypeParam` types from the function's `GenericFuncInfo`.
///
/// The resulting `VirFunction` is a **template** — it must NOT reach codegen
/// directly.  A future VIR-to-VIR monomorphization pass substitutes type
/// parameters with concrete types before compilation.
#[allow(clippy::too_many_arguments)]
pub fn lower_generic_function(
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
    type_table: &mut VirTypeTable,
    type_param_names: &[NameId],
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        generic: true,
        func_return_type: return_type,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let body = lower_func_body(&func.body, &mut ctx);
    VirFunction {
        id: func_id,
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        body,
        mangled_name_id: None,
        method_id: None,
        type_params: type_param_names.to_vec(),
    }
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
    type_table: &mut VirTypeTable,
) -> VirBody {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        generic: false,
        func_return_type: TypeId::VOID,
    };
    lower_func_body(body, &mut ctx)
}

/// Lower a `FuncBody` (block or expression) into a `VirBody`.
///
/// Block bodies have their statements walked individually; expression bodies
/// become a single trailing VIR expression.
pub fn lower_func_body(body: &FuncBody, ctx: &mut LoweringCtx<'_>) -> VirBody {
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
pub fn lower_stmts(stmts: &[vole_frontend::ast::Stmt], ctx: &mut LoweringCtx<'_>) -> VirBody {
    let vir_stmts = stmts.iter().map(|s| lower_stmt(s, ctx)).collect();
    VirBody {
        stmts: vir_stmts,
        trailing: None,
    }
}
