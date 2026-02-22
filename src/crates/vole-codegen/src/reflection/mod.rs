// src/codegen/reflection.rs
//
// Compile `.@meta` access expressions into TypeMeta class instances.
//
// For `MetaAccessKind::Static { type_def_id }`, builds a TypeMeta instance
// containing the type's name, an array of FieldMeta instances (with getter/setter
// trampolines), and a constructor function.
//
// TypeMeta and FieldMeta are Vole classes defined in
// `stdlib/prelude/reflection.vole`. We construct them using the same
// instance-allocation / field-store patterns that class literal codegen uses.

mod fields;
mod trampolines;

use cranelift::prelude::*;
use rustc_hash::FxHashMap;
use vole_identity::TypeDefId;
use vole_sema::node_map::MetaAccessKind;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::structs::helpers::store_field_value;
use crate::types::CompiledValue;

/// Entry point for compiling a `MetaAccess` expression.
///
/// Reads the `MetaAccessKind` annotation from sema and dispatches:
/// - `Static`: builds a TypeMeta instance for the given TypeDefId
/// - `Dynamic`: not yet implemented (returns an error)
pub fn compile_meta_access(
    cg: &mut Cg,
    expr_node_id: vole_frontend::NodeId,
) -> CodegenResult<CompiledValue> {
    let meta_kind = cg
        .env
        .analyzed
        .node_map
        .get_meta_access(expr_node_id)
        .ok_or_else(|| CodegenError::unsupported("@meta access without sema annotation"))?;

    match meta_kind {
        MetaAccessKind::Static { type_def_id } => {
            compile_static_meta(cg, type_def_id, expr_node_id)
        }
        MetaAccessKind::Dynamic => Err(CodegenError::unsupported(
            "dynamic @meta access (interface-typed values)",
        )),
    }
}

/// Build a TypeMeta instance for a statically-known type.
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
    let info = resolve_reflection_types(cg)?;

    // Get the type's name
    let type_name = {
        let type_def = cg.query().get_type(type_def_id);
        cg.query()
            .last_segment(type_def.name_id)
            .unwrap_or_else(|| "?".to_string())
    };

    // Build the name string
    let name_cv = cg.string_literal(&type_name)?;

    // Build the fields array
    let fields_cv = fields::build_field_meta_array(cg, type_def_id, &info)?;

    // Build the constructor closure
    let construct_cv = trampolines::build_constructor(cg, type_def_id, &info)?;

    // Allocate a TypeMeta instance and store its fields
    let type_meta_cv =
        allocate_type_meta(cg, &info, name_cv, fields_cv, construct_cv, expr_node_id)?;

    Ok(cg.mark_rc_owned(type_meta_cv))
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

/// Allocate a TypeMeta instance and store its three fields.
fn allocate_type_meta(
    cg: &mut Cg,
    info: &ReflectionTypeInfo,
    name_cv: CompiledValue,
    fields_cv: CompiledValue,
    construct_cv: CompiledValue,
    expr_node_id: vole_frontend::NodeId,
) -> CodegenResult<CompiledValue> {
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

    let result_type_id = cg
        .get_expr_type(&expr_node_id)
        .unwrap_or(info.type_meta_type_id);
    Ok(CompiledValue::new(
        instance_ptr,
        cg.ptr_type(),
        result_type_id,
    ))
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
