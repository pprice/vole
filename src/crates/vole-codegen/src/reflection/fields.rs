// src/codegen/reflection/fields.rs
//
// Build the [FieldMeta] array for a TypeMeta instance.
//
// For each field on the target type, allocates a FieldMeta class instance
// with name, type_name, annotations (empty), getter, and setter closures.

use cranelift::prelude::*;
use vole_identity::TypeDefId;

use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::CodegenResult;
use crate::structs::helpers::store_field_value;
use crate::types::CompiledValue;

use super::ReflectionTypeInfo;
use super::trampolines;

/// Build a dynamic array of FieldMeta instances for all fields on the type.
pub(super) fn build_field_meta_array(
    cg: &mut Cg,
    type_def_id: TypeDefId,
    info: &ReflectionTypeInfo,
) -> CodegenResult<CompiledValue> {
    // Collect field info before building (avoids borrowing issues)
    let field_info = collect_field_info(cg, type_def_id);

    // Create the dynamic array
    let arr_ptr = cg.call_runtime(RuntimeKey::ArrayNew, &[])?;
    let array_push_ref = cg.runtime_func_ref(RuntimeKey::ArrayPush)?;

    for (field_name, type_name, slot, field_type_id) in &field_info {
        let field_meta_ptr = build_single_field_meta(
            cg,
            info,
            field_name,
            type_name,
            type_def_id,
            *slot,
            *field_type_id,
        )?;

        // Push to array - FieldMeta is a class (RC pointer), tag = Instance
        let tag = cg.iconst_cached(
            types::I64,
            vole_runtime::value::RuntimeTypeId::Instance as i64,
        );
        cg.emit_call(array_push_ref, &[arr_ptr, tag, field_meta_ptr]);
    }

    // The array type is [FieldMeta]. Use lookup_array (read-only) since the
    // arena is immutable in codegen. If not found, fall back to the sema-provided
    // type from the TypeMeta fields definition.
    let array_type_id = cg
        .arena()
        .lookup_array(info.field_meta_type_id)
        .unwrap_or(info.field_meta_type_id);
    Ok(CompiledValue::new(arr_ptr, cg.ptr_type(), array_type_id))
}

/// Collect (field_name, type_name, slot, field_type_id) tuples for all fields.
fn collect_field_info(cg: &Cg, type_def_id: TypeDefId) -> Vec<(String, String, usize, TypeId)> {
    let query = cg.query();
    let arena = cg.arena();
    query
        .fields_on_type(type_def_id)
        .map(|field_id| {
            let field = query.get_field(field_id);
            let field_name = cg
                .name_table()
                .last_segment_str(field.name_id)
                .unwrap_or_default();
            let type_name = arena.display_basic(field.ty);
            (field_name, type_name, field.slot, field.ty)
        })
        .collect()
}

/// Build a single FieldMeta class instance for one field.
///
/// FieldMeta layout (from reflection.vole):
///   - name: string
///   - type_name: string
///   - annotations: [unknown]
///   - get: (unknown) -> unknown
///   - set: (unknown, unknown) -> void
///
/// Physical slot indices are looked up from type_metadata, not hardcoded.
fn build_single_field_meta(
    cg: &mut Cg,
    info: &ReflectionTypeInfo,
    field_name: &str,
    type_name: &str,
    target_type_def_id: TypeDefId,
    field_slot: usize,
    field_type_id: TypeId,
) -> CodegenResult<Value> {
    // Compute the RuntimeTypeId tag for this field's type (used by getter boxing).
    let runtime_tag = crate::types::unknown_type_tag(field_type_id, cg.arena()) as i64;

    let instance_ptr = super::allocate_class_instance(cg, info.field_meta_def_id)?;
    let set_func_ref = cg.runtime_func_ref(RuntimeKey::InstanceSetField)?;

    let name_slot = super::lookup_slot(&info.field_meta_slots, "name", "FieldMeta")?;
    let type_name_slot = super::lookup_slot(&info.field_meta_slots, "type_name", "FieldMeta")?;
    let annotations_slot = super::lookup_slot(&info.field_meta_slots, "annotations", "FieldMeta")?;
    let get_slot = super::lookup_slot(&info.field_meta_slots, "get", "FieldMeta")?;
    let set_slot = super::lookup_slot(&info.field_meta_slots, "set", "FieldMeta")?;

    // name (string)
    let name_cv = cg.string_literal(field_name)?;
    store_field_value(cg, set_func_ref, instance_ptr, name_slot, &name_cv);

    // type_name (string)
    let type_name_cv = cg.string_literal(type_name)?;
    store_field_value(
        cg,
        set_func_ref,
        instance_ptr,
        type_name_slot,
        &type_name_cv,
    );

    // annotations (empty [unknown] array)
    let annotations_ptr = cg.call_runtime(RuntimeKey::ArrayNew, &[])?;
    let annotations_cv = CompiledValue::new(annotations_ptr, cg.ptr_type(), cg.arena().unknown());
    store_field_value(
        cg,
        set_func_ref,
        instance_ptr,
        annotations_slot,
        &annotations_cv,
    );

    // getter trampoline (uses correct RuntimeTypeId tag for boxing)
    let getter_cv = trampolines::build_getter(cg, target_type_def_id, field_slot, runtime_tag)?;
    store_field_value(cg, set_func_ref, instance_ptr, get_slot, &getter_cv);

    // setter trampoline
    let setter_cv = trampolines::build_setter(cg, target_type_def_id, field_slot)?;
    store_field_value(cg, set_func_ref, instance_ptr, set_slot, &setter_cv);

    Ok(instance_ptr)
}
