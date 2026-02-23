// src/codegen/reflection/fields.rs
//
// Build the [FieldMeta] array for a TypeMeta instance.
//
// For each field on the target type, allocates a FieldMeta class instance
// with name, type_name, annotations, getter, and setter closures.
//
// Annotations are populated from sema's ValidatedAnnotation data: each
// annotation struct is allocated as a heap instance, its fields are filled
// from the compiled argument expressions, and it is boxed as unknown
// before being pushed into the [unknown] annotations array.

use cranelift::prelude::*;
use vole_frontend::Expr;
use vole_identity::{NameId, TypeDefId};
use vole_sema::entity_defs::ValidatedAnnotation;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::structs::helpers::store_field_value;
use crate::types::CompiledValue;
use crate::union_layout;

use super::ReflectionTypeInfo;
use super::trampolines;

/// Pre-collected info for a single field (avoids borrow conflicts with Cg).
struct FieldInfo {
    name: String,
    type_name: String,
    slot: usize,
    type_id: TypeId,
    annotations: Vec<ValidatedAnnotation>,
}

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

    for fi in &field_info {
        let field_meta_ptr = build_single_field_meta(
            cg,
            info,
            &fi.name,
            &fi.type_name,
            type_def_id,
            fi.slot,
            fi.type_id,
            &fi.annotations,
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

/// Collect field info tuples for all fields, including annotations.
fn collect_field_info(cg: &Cg, type_def_id: TypeDefId) -> Vec<FieldInfo> {
    let query = cg.query();
    let arena = cg.arena();
    query
        .fields_on_type(type_def_id)
        .map(|field_id| {
            let field = query.get_field(field_id);
            let name = cg
                .name_table()
                .last_segment_str(field.name_id)
                .unwrap_or_default();
            let type_name = arena.display_basic(field.ty);
            FieldInfo {
                name,
                type_name,
                slot: field.slot,
                type_id: field.ty,
                annotations: field.annotations.clone(),
            }
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
#[expect(clippy::too_many_arguments)]
fn build_single_field_meta(
    cg: &mut Cg,
    info: &ReflectionTypeInfo,
    field_name: &str,
    type_name: &str,
    target_type_def_id: TypeDefId,
    field_slot: usize,
    field_type_id: TypeId,
    annotations: &[ValidatedAnnotation],
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

    // annotations ([unknown] array, populated from sema ValidatedAnnotation data)
    let annotations_cv = build_annotations_array(cg, annotations)?;
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

/// Build the [unknown] annotations array from validated annotations.
///
/// For each annotation, allocates a heap instance of the annotation struct,
/// compiles and stores each field value, then boxes it into a heap-allocated
/// TaggedValue before pushing into the array.
///
/// ## Why heap TaggedValues?
///
/// `box_to_unknown()` creates heap-allocated TaggedValues. The array stores a
/// pointer to each TaggedValue as the element value. When `arr[i]` is accessed,
/// `ArrayGetValue` returns this pointer, and the `is` check loads from it at
/// offset 0 to read the type tag. The inner tag for annotations is `Instance`
/// since annotation structs are allocated as class instances via `InstanceNew`.
fn build_annotations_array(
    cg: &mut Cg,
    annotations: &[ValidatedAnnotation],
) -> CodegenResult<CompiledValue> {
    let arr_ptr = cg.call_runtime(RuntimeKey::ArrayNew, &[])?;

    if annotations.is_empty() {
        return Ok(CompiledValue::new(
            arr_ptr,
            cg.ptr_type(),
            cg.arena().unknown(),
        ));
    }

    let array_push_ref = cg.runtime_func_ref(RuntimeKey::ArrayPush)?;
    let heap_alloc_ref = cg.runtime_func_ref(RuntimeKey::HeapAlloc)?;

    for ann in annotations {
        let ann_ptr = build_annotation_instance(cg, ann)?;

        // Allocate a heap TaggedValue: [tag: i64 @ 0, value: i64 @ 8]
        // Tag = Instance (annotation structs are heap-allocated class instances).
        let pt = cg.ptr_type();
        let size_val = cg.iconst_cached(pt, union_layout::STANDARD_SIZE as i64);
        let alloc_call = cg.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_tv_ptr = cg.builder.inst_results(alloc_call)[0];

        let inner_tag = cg.iconst_cached(
            types::I64,
            vole_runtime::value::RuntimeTypeId::Instance as i64,
        );
        cg.builder
            .ins()
            .store(MemFlags::new(), inner_tag, heap_tv_ptr, 0);
        cg.builder.ins().store(
            MemFlags::new(),
            ann_ptr,
            heap_tv_ptr,
            union_layout::PAYLOAD_OFFSET,
        );

        // Push as UnknownHeap so that array_drop calls unknown_heap_cleanup
        // on the heap TaggedValue, which rc_dec's the inner annotation instance
        // and frees the 16-byte buffer. The actual type tag lives inside the
        // heap TaggedValue at offset 0.
        let array_tag = cg.iconst_cached(
            types::I64,
            vole_runtime::value::RuntimeTypeId::UnknownHeap as i64,
        );
        cg.emit_call(array_push_ref, &[arr_ptr, array_tag, heap_tv_ptr]);
    }

    Ok(CompiledValue::new(
        arr_ptr,
        cg.ptr_type(),
        cg.arena().unknown(),
    ))
}

/// Build a heap-allocated instance of an annotation struct.
///
/// Annotation types are normally structs (stack-allocated), but when used in
/// FieldMeta.annotations they need to be heap-allocated class instances so they
/// can be stored in [unknown] arrays with proper RC lifecycle. This function:
/// 1. Ensures the annotation type is registered with the runtime type registry
/// 2. Allocates a heap instance with the registered type_id
/// 3. Compiles and stores each field value
fn build_annotation_instance(cg: &mut Cg, ann: &ValidatedAnnotation) -> CodegenResult<Value> {
    // Ensure the annotation type has a runtime type_id for proper field cleanup
    let (runtime_type_id, field_count) = ensure_annotation_type_registered(cg, ann.type_def_id)?;

    // Allocate the heap instance
    let instance_ptr = allocate_annotation_instance(cg, runtime_type_id, field_count)?;

    if ann.args.is_empty() {
        return Ok(instance_ptr);
    }

    // Pre-collect field slot info to avoid borrow conflicts
    let field_slots = collect_annotation_field_slots(cg, ann.type_def_id, &ann.args);

    // Clone expressions to avoid borrow conflict with cg.expr()
    let exprs: Vec<Expr> = ann.args.iter().map(|(_, expr)| (**expr).clone()).collect();

    let set_func_ref = cg.runtime_func_ref(RuntimeKey::InstanceSetField)?;

    for (slot, expr) in field_slots.into_iter().zip(exprs.iter()) {
        let compiled = cg.expr(expr)?;
        store_field_value(cg, set_func_ref, instance_ptr, slot, &compiled);
    }

    Ok(instance_ptr)
}

/// Ensure an annotation struct type is registered in the runtime type registry.
///
/// Annotation types (structs) normally have type_id=0 since they're stack-allocated.
/// When used as heap instances (in FieldMeta.annotations), they need a proper
/// runtime type_id with field type tags so instance_drop can clean up RC fields.
///
/// Returns (runtime_type_id, physical_slot_count).
fn ensure_annotation_type_registered(
    cg: &Cg,
    ann_type_def_id: TypeDefId,
) -> CodegenResult<(u32, usize)> {
    // Check if this annotation type is already a class with a non-zero type_id
    let meta = cg
        .type_metadata()
        .get(&ann_type_def_id)
        .ok_or_else(|| CodegenError::not_found("annotation type in type_metadata", "reflection"))?;

    let field_count = meta.physical_slot_count;

    if meta.type_id != 0 {
        // Already a class type with proper runtime registration
        return Ok((meta.type_id, field_count));
    }

    // Check the annotation_type_ids cache
    if let Some(&cached_id) = cg
        .env
        .state
        .annotation_type_ids
        .borrow()
        .get(&ann_type_def_id)
    {
        return Ok((cached_id, field_count));
    }

    // Allocate a new runtime type_id and register field type tags
    let new_type_id = vole_runtime::type_registry::alloc_type_id();
    let field_type_tags = collect_annotation_field_type_tags(cg, ann_type_def_id);
    vole_runtime::type_registry::register_instance_type(new_type_id, field_type_tags);

    // Cache for future use
    cg.env
        .state
        .annotation_type_ids
        .borrow_mut()
        .insert(ann_type_def_id, new_type_id);

    Ok((new_type_id, field_count))
}

/// Collect runtime field type tags for an annotation struct's fields.
fn collect_annotation_field_type_tags(
    cg: &Cg,
    ann_type_def_id: TypeDefId,
) -> Vec<vole_runtime::type_registry::FieldTypeTag> {
    let query = cg.query();
    query
        .fields_on_type(ann_type_def_id)
        .map(|field_id| {
            let field = query.get_field(field_id);
            cg.field_type_tag(field.ty)
        })
        .collect()
}

/// Allocate a heap instance with a specific runtime type_id and field count.
fn allocate_annotation_instance(
    cg: &mut Cg,
    runtime_type_id: u32,
    field_count: usize,
) -> CodegenResult<Value> {
    use vole_runtime::value::RuntimeTypeId;

    let type_id_val = cg.iconst_cached(types::I32, runtime_type_id as i64);
    let field_count_val = cg.iconst_cached(types::I32, field_count as i64);
    let runtime_type = cg.iconst_cached(types::I32, RuntimeTypeId::Instance as i64);

    cg.call_runtime(
        RuntimeKey::InstanceNew,
        &[type_id_val, field_count_val, runtime_type],
    )
}

/// Collect field slot indices for annotation args from type_metadata.
///
/// Returns a Vec of slot indices parallel to `args`, mapping each annotation
/// argument to its physical slot in the instance.
fn collect_annotation_field_slots(
    cg: &Cg,
    ann_type_def_id: TypeDefId,
    args: &[(NameId, Box<Expr>)],
) -> Vec<usize> {
    let name_table = cg.name_table();
    let type_meta = cg.type_metadata().get(&ann_type_def_id);

    args.iter()
        .map(|(name_id, _)| {
            let field_name = name_table.last_segment_str(*name_id).unwrap_or_default();
            type_meta
                .and_then(|meta| meta.field_slots.get(&field_name).copied())
                .unwrap_or(0)
        })
        .collect()
}
