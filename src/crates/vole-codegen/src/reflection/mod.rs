// src/codegen/reflection.rs
//
// Compile `.@meta` access expressions into TypeMeta class instances.
//
// For `MetaAccessKind::Static { type_def_id }`, builds a TypeMeta instance
// containing the type's name, an array of FieldMeta instances (with getter/setter
// trampolines), and a constructor function.
//
// For `MetaAccessKind::Dynamic`, loads the meta getter function pointer from
// the interface vtable slot 0, calls it, and returns the resulting TypeMeta.
// This allows `val.@meta` to return the correct concrete type metadata when
// `val` has an interface type.
//
// TypeMeta and FieldMeta are Vole classes defined in
// `stdlib/prelude/reflection.vole`. We construct them using the same
// instance-allocation / field-store patterns that class literal codegen uses.

mod fields;
mod trampolines;

use cranelift::prelude::*;
use cranelift_module::Module;
use rustc_hash::FxHashMap;
use vole_frontend::ast::MetaAccessExpr;
use vole_identity::{NameId, TypeDefId};
use vole_sema::node_map::MetaAccessKind;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::interfaces::vtable::VTABLE_META_SLOT;
use crate::structs::helpers::store_field_value;
use crate::types::CompiledValue;

/// Entry point for compiling a `MetaAccess` expression.
///
/// Reads the `MetaAccessKind` annotation from sema and dispatches:
/// - `Static`: builds a TypeMeta instance for the given TypeDefId
/// - `Dynamic`: loads the meta getter from the interface vtable and calls it
pub fn compile_meta_access(
    cg: &mut Cg,
    expr_node_id: vole_frontend::NodeId,
    meta_access: &MetaAccessExpr,
) -> CodegenResult<CompiledValue> {
    let meta_kind = cg
        .env
        .analyzed
        .node_map
        .get_meta_access(expr_node_id)
        .ok_or_else(|| CodegenError::unsupported("@meta access without sema annotation"))?;

    match meta_kind {
        MetaAccessKind::Static { type_def_id } => {
            // In monomorphized contexts, the Static annotation may be stale:
            // sema re-analyzes each monomorphization of a generic function body
            // but all share the same NodeId, so the last re-analysis overwrites
            // earlier ones. Re-derive the TypeDefId from the object expression's
            // actual type in the current codegen scope.
            let effective_type_def_id = if cg.substitutions.is_some() {
                resolve_static_meta_type_def_id(cg, &meta_access.object).unwrap_or(type_def_id)
            } else {
                type_def_id
            };
            compile_static_meta(cg, effective_type_def_id, expr_node_id)
        }
        MetaAccessKind::Dynamic => compile_dynamic_meta(cg, meta_access, expr_node_id),
        MetaAccessKind::TypeParam { name_id } => {
            resolve_type_param_meta(cg, name_id, meta_access, expr_node_id)
        }
    }
}

/// Resolve the correct TypeDefId for a value-expression meta access in a
/// monomorphized context. Returns `None` when the object is a type name
/// (e.g. `Point.@meta`) or when the type can't be resolved.
///
/// For identifiers (the common case: `v.@meta`), looks up the variable's
/// concrete type in the codegen scope. For other expressions, falls back to
/// the sema node_map type with type-parameter substitution applied.
fn resolve_static_meta_type_def_id(
    cg: &Cg,
    object: &vole_frontend::ast::Expr,
) -> Option<TypeDefId> {
    use vole_frontend::ast::ExprKind;

    let object_type_id = match &object.kind {
        ExprKind::Identifier(sym) => {
            // Look up the variable's type in the current codegen scope.
            // This is set per-monomorphization from the concrete param types.
            cg.vars.get(sym).map(|(_, ty)| *ty)?
        }
        _ => {
            // For other expressions, use the node_map type with substitution.
            // `get_expr_type_substituted` applies the current monomorphization's
            // type-parameter substitutions to the stored type.
            cg.get_expr_type_substituted(&object.id)?
        }
    };

    // Extract the TypeDefId from the concrete nominal type.
    let (type_def_id, _, _) = cg.arena().unwrap_nominal(object_type_id)?;
    Some(type_def_id)
}

/// Resolve a `TypeParam` meta access by looking up the concrete type from
/// the current monomorphization substitutions.
///
/// When codegen compiles a monomorphized generic function (e.g., `get_meta<Point>`),
/// sema's original annotation for `T.@meta` is `TypeParam { name_id }` because
/// sema's monomorph re-analysis cannot reclassify it (the identifier `T` isn't
/// resolvable as a type name or variable during re-analysis). Codegen resolves it
/// here using the substitution map carried in `FunctionCtx`.
///
/// Dispatches to:
/// - `compile_static_meta` if the concrete type is a nominal (class/struct)
/// - `compile_dynamic_meta` if the concrete type is an interface
fn resolve_type_param_meta(
    cg: &mut Cg,
    name_id: NameId,
    meta_access: &MetaAccessExpr,
    expr_node_id: vole_frontend::NodeId,
) -> CodegenResult<CompiledValue> {
    let substitutions = cg.substitutions.ok_or_else(|| {
        CodegenError::unsupported("T.@meta requires concrete type (not in a monomorphized context)")
    })?;

    let concrete_type_id = substitutions.get(&name_id).copied().ok_or_else(|| {
        let param_name = cg
            .query()
            .last_segment(name_id)
            .unwrap_or_else(|| "?".to_string());
        CodegenError::unsupported_with_context(
            "T.@meta: no substitution for type parameter",
            param_name,
        )
    })?;

    // Interface types require dynamic dispatch via vtable.
    if cg.arena().is_interface(concrete_type_id) {
        return compile_dynamic_meta(cg, meta_access, expr_node_id);
    }

    // Concrete nominal types (class/struct) are resolved statically.
    if let Some((type_def_id, _, _)) = cg.arena().unwrap_nominal(concrete_type_id) {
        return compile_static_meta(cg, type_def_id, expr_node_id);
    }

    // Unsupported concrete type (primitive, array, function, etc.)
    let display = cg.arena().display_basic(concrete_type_id);
    Err(CodegenError::unsupported_with_context(
        "T.@meta: concrete type does not support reflection",
        display,
    ))
}

/// Build a TypeMeta instance for a statically-known type, with singleton caching.
///
/// Uses a runtime-side cache keyed by runtime type_id. On first access the
/// TypeMeta is built and stored into the cache; subsequent accesses return
/// the cached pointer with rc_inc so the caller gets an owned reference.
///
/// TypeMeta layout (from reflection.vole):
///   - name: string           (slot 0)
///   - fields: [FieldMeta]    (slot 1)
///   - construct: func        (slot 2)
fn compile_static_meta(
    cg: &mut Cg,
    type_def_id: TypeDefId,
    expr_node_id: vole_frontend::NodeId,
) -> CodegenResult<CompiledValue> {
    let ptr_type = cg.ptr_type();

    // Get or allocate a unique cache key for this type.
    // Classes use their runtime type_id (always nonzero); structs (type_id=0) get
    // a freshly allocated ID so different struct types don't collide.
    let cache_key = get_or_alloc_meta_cache_key(cg, type_def_id)?;

    // Call type_meta_cache_get(cache_key) to check the runtime cache.
    let type_id_val = cg.iconst_cached(types::I32, cache_key as i64);
    let cached_ptr = cg.call_runtime(RuntimeKey::TypeMetaCacheGet, &[type_id_val])?;

    // Check if the cached pointer is null (first access).
    let null = cg.iconst_cached(ptr_type, 0);
    let is_null = cg.builder.ins().icmp(IntCC::Equal, cached_ptr, null);

    let cold_block = cg.builder.create_block();
    let hot_block = cg.builder.create_block();
    let merge_block = cg.builder.create_block();
    cg.builder.append_block_param(merge_block, ptr_type);

    cg.emit_brif(is_null, cold_block, hot_block);

    // --- Cold path: first access, build and cache ---
    cg.switch_to_block(cold_block);
    cg.builder.seal_block(cold_block);
    let fresh_ptr = build_type_meta_instance(cg, type_def_id)?;
    // rc_inc so the cache holds one reference AND the caller gets one.
    cg.emit_rc_inc(fresh_ptr)?;
    // Store into cache (cache takes ownership of one rc reference).
    let type_id_val2 = cg.iconst_cached(types::I32, cache_key as i64);
    cg.call_runtime_void(RuntimeKey::TypeMetaCacheStore, &[type_id_val2, fresh_ptr])?;
    cg.builder.ins().jump(merge_block, &[fresh_ptr.into()]);

    // --- Hot path: cached, rc_inc and return ---
    cg.switch_to_block(hot_block);
    cg.builder.seal_block(hot_block);
    cg.emit_rc_inc(cached_ptr)?;
    cg.builder.ins().jump(merge_block, &[cached_ptr.into()]);

    cg.switch_to_block(merge_block);
    cg.builder.seal_block(merge_block);
    let result_ptr = cg.builder.block_params(merge_block)[0];

    let result_type_id = cg.get_expr_type(&expr_node_id).unwrap_or_else(|| {
        resolve_reflection_types(cg)
            .ok()
            .map(|i| i.type_meta_type_id)
            .unwrap_or(TypeId::UNKNOWN)
    });

    let cv = CompiledValue::new(result_ptr, ptr_type, result_type_id);
    Ok(cg.mark_rc_owned(cv))
}

/// Get or allocate a unique cache key for a TypeDefId's TypeMeta singleton.
///
/// Classes already have unique nonzero runtime type_ids which we reuse.
/// Structs have type_id=0, so we allocate a fresh unique ID to avoid collisions.
/// The mapping is cached in `CodegenState.meta_cache_keys` so the same TypeDefId
/// always maps to the same key across multiple `.@meta` call sites.
fn get_or_alloc_meta_cache_key(cg: &Cg, type_def_id: TypeDefId) -> CodegenResult<u32> {
    // Check cache first.
    if let Some(&key) = cg.env.state.meta_cache_keys.borrow().get(&type_def_id) {
        return Ok(key);
    }

    // For classes, use their existing nonzero runtime type_id.
    // For structs (type_id=0), allocate a unique ID.
    let meta = cg
        .type_metadata()
        .get(&type_def_id)
        .ok_or_else(|| CodegenError::not_found("type in type_metadata", "meta_cache_key"))?;
    let key = if meta.type_id != 0 {
        meta.type_id
    } else {
        vole_runtime::type_registry::alloc_type_id()
    };

    cg.env
        .state
        .meta_cache_keys
        .borrow_mut()
        .insert(type_def_id, key);
    Ok(key)
}

/// Build a fresh TypeMeta instance for a type (no caching — called by the cold path).
fn build_type_meta_instance(cg: &mut Cg, type_def_id: TypeDefId) -> CodegenResult<Value> {
    let info = resolve_reflection_types(cg)?;

    let type_name = {
        let type_def = cg.query().get_type(type_def_id);
        cg.query()
            .last_segment(type_def.name_id)
            .unwrap_or_else(|| "?".to_string())
    };

    let name_cv = cg.string_literal(&type_name)?;
    let fields_cv = fields::build_field_meta_array(cg, type_def_id, &info)?;
    let construct_cv = trampolines::build_constructor(cg, type_def_id, &info)?;

    let instance_ptr = allocate_class_instance(cg, info.type_meta_def_id)?;
    let set_func_ref = cg.runtime_func_ref(RuntimeKey::InstanceSetField)?;

    let name_slot = lookup_slot(&info.type_meta_slots, "name", "TypeMeta")?;
    let fields_slot = lookup_slot(&info.type_meta_slots, "fields", "TypeMeta")?;
    let construct_slot = lookup_slot(&info.type_meta_slots, "construct", "TypeMeta")?;

    store_field_value(cg, set_func_ref, instance_ptr, name_slot, &name_cv);
    store_field_value(cg, set_func_ref, instance_ptr, fields_slot, &fields_cv);
    store_field_value(
        cg,
        set_func_ref,
        instance_ptr,
        construct_slot,
        &construct_cv,
    );

    Ok(instance_ptr)
}

/// Build a TypeMeta instance for a dynamically-typed value (interface type).
///
/// When `val` has an interface type (e.g., `let val: Animal = Dog {}`),
/// `val.@meta` must return metadata for the concrete type (`Dog`), not the
/// interface (`Animal`). This is achieved by loading the meta getter function
/// pointer from vtable slot 0 and calling it.
///
/// Vtable layout: `[meta_getter_fn, method_0, method_1, ...]`
/// Interface box layout: `[data_ptr, vtable_ptr]`
fn compile_dynamic_meta(
    cg: &mut Cg,
    meta_access: &MetaAccessExpr,
    expr_node_id: vole_frontend::NodeId,
) -> CodegenResult<CompiledValue> {
    // Compile the object expression to get the interface-boxed value
    let obj = cg.expr(&meta_access.object)?;

    let ptr_type = cg.ptr_type();
    let word_bytes = ptr_type.bytes() as i32;

    // Load vtable pointer from the boxed interface (offset = word_bytes, i.e. slot 1)
    let vtable_ptr = cg
        .builder
        .ins()
        .load(ptr_type, MemFlags::new(), obj.value, word_bytes);

    // Load the meta getter function pointer from vtable[VTABLE_META_SLOT] (slot 0)
    let meta_fn_ptr = cg.builder.ins().load(
        ptr_type,
        MemFlags::new(),
        vtable_ptr,
        (VTABLE_META_SLOT as i32) * word_bytes,
    );

    // Build the call signature: () -> ptr (the meta getter takes no arguments and returns a TypeMeta pointer)
    let mut sig = cg.jit_module().make_signature();
    sig.returns.push(AbiParam::new(ptr_type));
    let sig_ref = cg.builder.import_signature(sig);

    // Call the meta getter
    let call = cg.builder.ins().call_indirect(sig_ref, meta_fn_ptr, &[]);
    let type_meta_ptr = cg.builder.inst_results(call)[0];

    // Determine the result type (TypeMeta)
    let result_type_id = cg.get_expr_type(&expr_node_id).unwrap_or_else(|| {
        // Fallback: resolve TypeMeta type from entity registry
        let info = resolve_reflection_types(cg).ok();
        info.map(|i| i.type_meta_type_id).unwrap_or(TypeId::UNKNOWN)
    });

    let cv = CompiledValue::new(type_meta_ptr, ptr_type, result_type_id);
    Ok(cg.mark_rc_owned(cv))
}

/// Look up a field's physical slot index from a field_slots map.
fn lookup_slot(
    slots: &FxHashMap<String, usize>,
    field_name: &str,
    type_name: &str,
) -> CodegenResult<usize> {
    slots.get(field_name).copied().ok_or_else(|| {
        CodegenError::not_found(
            "reflection field slot",
            format!("{}.{}", type_name, field_name),
        )
    })
}

/// Allocate a class instance using type_metadata for the given TypeDefId.
pub(crate) fn allocate_class_instance(cg: &mut Cg, type_def_id: TypeDefId) -> CodegenResult<Value> {
    use vole_runtime::value::RuntimeTypeId;

    let meta = cg
        .type_metadata()
        .get(&type_def_id)
        .ok_or_else(|| CodegenError::not_found("type in type_metadata", "reflection"))?;

    let type_id_val = cg.iconst_cached(types::I32, meta.type_id as i64);
    let field_count_val = cg.iconst_cached(types::I32, meta.physical_slot_count as i64);
    let runtime_type = cg.iconst_cached(types::I32, RuntimeTypeId::Instance as i64);

    cg.call_runtime(
        RuntimeKey::InstanceNew,
        &[type_id_val, field_count_val, runtime_type],
    )
}

/// Cached IDs for TypeMeta and FieldMeta from the entity registry.
pub(crate) struct ReflectionTypeInfo {
    pub type_meta_def_id: TypeDefId,
    pub type_meta_type_id: TypeId,
    pub field_meta_def_id: TypeDefId,
    pub field_meta_type_id: TypeId,
    /// Physical slot indices for TypeMeta fields (name, fields, construct).
    pub type_meta_slots: FxHashMap<String, usize>,
    /// Physical slot indices for FieldMeta fields (name, type_name, annotations, get, set).
    pub field_meta_slots: FxHashMap<String, usize>,
}

/// Resolve TypeMeta and FieldMeta TypeDefIds from the entity registry.
pub(crate) fn resolve_reflection_types(cg: &Cg) -> CodegenResult<ReflectionTypeInfo> {
    let registry = cg.registry();
    let name_table = cg.name_table();

    let type_meta_def_id = registry
        .type_by_short_name("TypeMeta", name_table)
        .ok_or_else(|| CodegenError::not_found("TypeMeta class", "entity registry"))?;

    let field_meta_def_id = registry
        .type_by_short_name("FieldMeta", name_table)
        .ok_or_else(|| CodegenError::not_found("FieldMeta class", "entity registry"))?;

    // Look up the type_ids and field_slots from type_metadata.
    let type_meta_meta = cg
        .type_metadata()
        .get(&type_meta_def_id)
        .ok_or_else(|| CodegenError::not_found("TypeMeta", "type_metadata"))?;
    let type_meta_type_id = type_meta_meta.vole_type;
    let type_meta_slots = type_meta_meta.field_slots.clone();

    let field_meta_meta = cg
        .type_metadata()
        .get(&field_meta_def_id)
        .ok_or_else(|| CodegenError::not_found("FieldMeta", "type_metadata"))?;
    let field_meta_type_id = field_meta_meta.vole_type;
    let field_meta_slots = field_meta_meta.field_slots.clone();

    Ok(ReflectionTypeInfo {
        type_meta_def_id,
        type_meta_type_id,
        field_meta_def_id,
        field_meta_type_id,
        type_meta_slots,
        field_meta_slots,
    })
}
