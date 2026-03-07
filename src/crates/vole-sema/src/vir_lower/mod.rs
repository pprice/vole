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
    FunctionId, Interner, MethodId, ModuleId, NameId, NameTable, NodeId, Symbol, TypeDefId, TypeId,
    VirTypeId,
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
/// - `module_id`: the module being lowered (for resolving callee symbols)
pub struct LoweringCtx<'a> {
    pub node_map: &'a NodeMap,
    pub interner: &'a mut Interner,
    pub type_arena: &'a TypeArena,
    pub entities: &'a EntityRegistry,
    pub name_table: &'a NameTable,
    pub type_table: &'a mut VirTypeTable,
    /// The module whose body is being lowered.
    ///
    /// Used by call resolution to convert callee symbols to `NameId`
    /// via `NameTable::name_id(module_id, &[sym], interner)`.
    pub module_id: ModuleId,
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

    /// Translate a `TypeId` to a `VirTypeId` for VIR node annotations.
    ///
    /// Returns `VirTypeId::UNKNOWN` for sema-internal types (Module,
    /// Placeholder, Invalid) that have no VirTypeTable representation.
    pub fn compat_ty(&mut self, type_id: TypeId) -> VirTypeId {
        self.translate(type_id)
    }

    // -- Call resolution helpers ---------------------------------------------

    /// Try to resolve a callee `Symbol` to a `FunctionId` in the current
    /// module.  Returns `None` when the symbol doesn't map to a known
    /// same-module function (e.g. lambdas, closures, builtins, cross-module).
    pub fn resolve_callee_function(&self, callee_sym: Symbol) -> Option<FunctionId> {
        // Guard: if the symbol can't be resolved (e.g. UNKNOWN in tests),
        // bail early to avoid panicking in name_table.name_id().
        self.interner.try_resolve(callee_sym)?;
        let name_id = self
            .name_table
            .name_id(self.module_id, &[callee_sym], self.interner)?;
        let func_id = self.entities.function_by_name(name_id)?;
        let func_def = self.entities.get_function(func_id);
        // Only resolve non-generic functions — generic calls use GenericCall.
        if func_def.generic_info.is_some() {
            return None;
        }
        // Skip external (FFI) functions — they are declared through
        // implement blocks or FFI registration, not the normal function
        // declaration path, so they won't be in the func_registry by NameId.
        if func_def.is_external {
            return None;
        }
        // Only resolve same-module calls — cross-module calls go through
        // different codegen registration paths and may not be available
        // in the func_registry under the same NameId.
        if func_def.module != self.module_id {
            return None;
        }
        // Skip generator functions — codegen overrides their return type to
        // RuntimeIterator(T) and compiles them with special generator
        // infrastructure.  The Direct call path doesn't account for this.
        if func_def.generator_element_type.is_some() {
            return None;
        }
        // Skip functions returning struct types — codegen may use the sret
        // calling convention (hidden first parameter for the return buffer)
        // for structs with more than 2 flat fields.  The Direct call path
        // doesn't emit the sret argument.
        let ret_ty = func_def.signature.return_type_id;
        if self.type_arena.is_struct(ret_ty) {
            return None;
        }
        // Skip functions with default parameters — when the call site
        // omits a defaulted argument, the Direct path emits too few args.
        // Default filling happens in call_dispatch (Unresolved path).
        if func_def.param_defaults.iter().any(|d| d.is_some()) {
            return None;
        }
        // Skip functions with interface or union/optional parameters —
        // callers need implicit boxing/coercion that the Direct call path
        // doesn't perform (the Unresolved path handles this via
        // box_interface_value and union boxing in call_dispatch).
        for &param_ty in func_def.signature.params_id.iter() {
            if self.type_arena.is_interface(param_ty) || self.type_arena.is_union(param_ty) {
                return None;
            }
        }
        Some(func_id)
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

    /// Resolve the field storage dispatch for a field access.
    ///
    /// Given the object's sema type and the field name (as a `Symbol`),
    /// returns:
    /// - `FieldStorage::Direct { slot }` for struct fields (logical slot index)
    /// - `FieldStorage::Heap { slot }` for class fields (physical slot,
    ///   accounting for wide types)
    /// - `FieldStorage::ByName` for modules, unknown types, or generic templates
    pub fn resolve_field_storage(
        &self,
        object_type: TypeId,
        field: Symbol,
    ) -> vole_vir::expr::FieldStorage {
        use vole_vir::expr::FieldStorage;

        // Generic templates can't resolve storage — type params are abstract.
        if self.generic {
            return FieldStorage::ByName;
        }

        let field_name = self.interner.resolve(field);

        // Try struct first (value-type, stack-allocated).
        // Exception: annotation structs (@annotation) are heap-allocated via
        // InstanceNew at runtime, so their fields must use Heap storage.
        if let Some((type_def_id, type_args)) = self.type_arena.unwrap_struct(object_type) {
            let is_annotation = self.entities.get_type(type_def_id).is_annotation;
            if is_annotation {
                return self
                    .resolve_class_field_slot(type_def_id, type_args, field_name)
                    .map_or(FieldStorage::ByName, |slot| FieldStorage::Heap {
                        slot: slot as u32,
                    });
            }
            return self
                .resolve_struct_field_slot(type_def_id, type_args, field_name)
                .map_or(FieldStorage::ByName, |slot| FieldStorage::Direct {
                    slot: slot as u32,
                });
        }

        // Try class (reference-counted, heap-allocated).
        if let Some((type_def_id, type_args)) = self.type_arena.unwrap_class(object_type) {
            return self
                .resolve_class_field_slot(type_def_id, type_args, field_name)
                .map_or(FieldStorage::ByName, |slot| FieldStorage::Heap {
                    slot: slot as u32,
                });
        }

        // Module types carry the ModuleId for codegen dispatch.
        if let crate::SemaType::Module(interned) = self.type_arena.get(object_type) {
            return FieldStorage::Module {
                module_id: interned.module_id,
            };
        }

        // Interface or other type — codegen handles separately.
        FieldStorage::ByName
    }

    /// Resolve the logical field slot for a struct field.
    ///
    /// Returns the field's index in the struct's field list (0-based).
    fn resolve_struct_field_slot(
        &self,
        type_def_id: TypeDefId,
        _type_args: &crate::type_arena::TypeIdVec,
        field_name: &str,
    ) -> Option<usize> {
        let type_def = self.entities.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;
        generic_info.field_index_by_name(field_name, self.name_table)
    }

    /// Resolve the physical slot for a class field, accounting for wide
    /// types (i128/f128) that occupy 2 consecutive slots.
    fn resolve_class_field_slot(
        &self,
        type_def_id: TypeDefId,
        type_args: &crate::type_arena::TypeIdVec,
        field_name: &str,
    ) -> Option<usize> {
        let type_def = self.entities.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;

        // Build substitution map for generic classes.
        let subs: rustc_hash::FxHashMap<NameId, TypeId> = type_def
            .type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        let mut physical_slot = 0usize;
        for (idx, field_name_id) in generic_info.field_names.iter().enumerate() {
            let name = self.name_table.last_segment_str(*field_name_id);
            if name.as_deref() == Some(field_name) {
                return Some(physical_slot);
            }
            // Advance physical slot: wide types use 2 slots.
            let ft = generic_info.field_types[idx];
            let resolved_ft = if !subs.is_empty() {
                self.type_arena.lookup_substitute(ft, &subs).unwrap_or(ft)
            } else {
                ft
            };
            physical_slot += if is_wide_sema_type(resolved_ft) { 2 } else { 1 };
        }
        None
    }

    /// Get the `StructLiteralInfo` for a node, with a tolerant fallback.
    ///
    /// Returns a placeholder with a zeroed `TypeDefId` and `is_class = false`
    /// when the info is missing.  This can happen in two situations:
    ///
    /// 1. **Generic mode** — the template was never fully analyzed.
    /// 2. **Concrete mode** — sema returned early (e.g. the method body was
    ///    never type-checked because the method wasn't found in the implement
    ///    registry).  A sema error was already reported, so VIR lowering
    ///    should emit a best-effort placeholder instead of panicking.
    pub fn require_struct_literal_info(
        &self,
        node_id: NodeId,
        _line: u32,
    ) -> crate::node_map::StructLiteralInfo {
        self.node_map.get_struct_literal_info(node_id).unwrap_or(
            crate::node_map::StructLiteralInfo {
                type_def_id: TypeDefId::new(0),
                is_class: false,
            },
        )
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
    module_id: ModuleId,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
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
    module_id: ModuleId,
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
        module_id,
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
    module_id: ModuleId,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
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
    module_id: ModuleId,
) -> Option<VirFunction> {
    let body_ast = method.body.as_ref()?;
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
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
    module_id: ModuleId,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
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
    module_id: ModuleId,
) -> VirBody {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
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

/// Check whether a sema `TypeId` is a wide type (i128 or f128) that
/// occupies 2 consecutive slots in class instance storage.
fn is_wide_sema_type(type_id: TypeId) -> bool {
    matches!(type_id, TypeId::I128 | TypeId::F128)
}
