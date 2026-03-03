// src/codegen/structs/helpers.rs

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::ops::uextend_const;
use crate::types::CompiledValue;
use vole_identity::{NameId, TypeId, VirTypeId};
use vole_vir::types::VirType;

/// Get field slot and type for a field access (Cg API).
pub(crate) fn get_field_slot_and_type_id_cg(
    type_id: TypeId,
    field_name: &str,
    cg: &crate::context::Cg,
) -> CodegenResult<(usize, TypeId)> {
    let vir_table = cg.vir_type_table();

    // Apply function-level substitutions first (for monomorphized generics)
    // This handles the case where type_id is a TypeParam that needs to be
    // substituted with a concrete type (e.g., in duck typing with structural constraints)
    let sema_subs_ref = cg.sema_substitutions();
    let resolved_type_id = if let Some(ref func_subs) = sema_subs_ref {
        tracing::debug!(?type_id, ?func_subs, "field access: applying substitutions");
        vir_table
            .lookup_substitute(type_id, func_subs)
            .unwrap_or(type_id)
    } else {
        tracing::debug!(?type_id, "field access: no substitutions available");
        type_id
    };

    tracing::debug!(?resolved_type_id, "field access: resolved type");

    // Unwrap class/struct via VIR type table
    let vir_ty = vir_table
        .lookup_type_id(resolved_type_id)
        .unwrap_or(VirTypeId::UNKNOWN);
    let (type_def_id, type_args) =
        crate::types::vir_conversions::vir_unwrap_class(vir_ty, vir_table)
            .or_else(|| crate::types::vir_conversions::vir_unwrap_struct(vir_ty, vir_table))
            .ok_or_else(|| {
                CodegenError::type_mismatch("field access", "class or struct", "other type")
            })?;

    let type_def = cg.analyzed().type_def(type_def_id);
    let generic_field_types = type_def
        .generic_field_types
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_field_types", "type"))?;
    let field_names = type_def
        .generic_field_names
        .as_ref()
        .ok_or_else(|| CodegenError::not_found("generic_field_names", "type"))?;

    // Build VIR-native combined substitution map: type params -> VirTypeId args,
    // plus monomorphization context (sema TypeId -> VirTypeId).
    let mut combined_subs: FxHashMap<NameId, VirTypeId> = type_def
        .type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Merge in function-level substitutions (monomorphization context).
    // Convert sema TypeId subs to VirTypeId.  Prefer concrete function
    // substitutions over placeholder type args from partially-specialized
    // generic instances.
    if let Some(ref func_subs) = sema_subs_ref {
        for (&k, &v) in func_subs.iter() {
            let vir_v = vir_table.lookup_type_id(v);
            let should_override = combined_subs
                .get(&k)
                .is_some_and(|&existing| matches!(vir_table.get(existing), VirType::Param { .. }));
            if (should_override || !combined_subs.contains_key(&k))
                && let Some(vir_v) = vir_v
            {
                combined_subs.insert(k, vir_v);
            }
        }
    }
    // Drop the borrow on sema_substitutions before mutable access to cg.
    drop(sema_subs_ref);

    // Compute physical slot: i128 fields use 2 u64 slots, all others use 1.
    // Physical slot is the sum of slot widths for all fields before this one.
    let is_class = crate::types::vir_conversions::vir_unwrap_class(vir_ty, vir_table).is_some();
    let mut physical_slot = 0usize;
    for (idx, field_name_id) in field_names.iter().enumerate() {
        let name = cg.analyzed().last_segment(*field_name_id);
        if name.as_deref() == Some(field_name) {
            let base_vir = generic_field_types[idx];
            let field_vir = if !combined_subs.is_empty() {
                vir_table
                    .substitute_vir_ids(base_vir, &combined_subs)
                    .unwrap_or(base_vir)
            } else {
                base_vir
            };
            let field_type_id = vir_table.vir_to_type_id(field_vir);
            // For structs, use the original sema slot (they don't go through instance storage)
            let slot = if is_class { physical_slot } else { idx };
            return Ok((slot, field_type_id));
        }
        // Advance physical slot counter
        let ft = generic_field_types[idx];
        let resolved_vir = if !combined_subs.is_empty() {
            vir_table
                .substitute_vir_ids(ft, &combined_subs)
                .unwrap_or(ft)
        } else {
            ft
        };
        physical_slot += if is_class && matches!(resolved_vir, VirTypeId::I128 | VirTypeId::F128) {
            2
        } else {
            1
        };
    }

    Err(CodegenError::not_found(
        "field",
        format!("{} in type", field_name),
    ))
}

/// Convert a raw i64 field value to the appropriate Cranelift type.
///
/// Primitive types are narrowed (f64 bitcast, bool/int reduction); all other
/// types (classes, arrays, etc.) are stored as i64.
pub(crate) fn convert_field_value_id(
    builder: &mut FunctionBuilder,
    raw_value: Value,
    type_id: TypeId,
) -> (Value, Type) {
    match type_id {
        TypeId::F64 => {
            let fval = builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_value);
            (fval, types::F64)
        }
        TypeId::F32 => {
            let i32_val = builder.ins().ireduce(types::I32, raw_value);
            let fval = builder.ins().bitcast(types::F32, MemFlags::new(), i32_val);
            (fval, types::F32)
        }
        TypeId::F128 => {
            panic!("f128 cannot be reconstructed from a single i64 slot")
        }
        TypeId::BOOL => {
            let bval = builder.ins().ireduce(types::I8, raw_value);
            (bval, types::I8)
        }
        TypeId::I8 | TypeId::U8 => {
            let val = builder.ins().ireduce(types::I8, raw_value);
            (val, types::I8)
        }
        TypeId::I16 | TypeId::U16 => {
            let val = builder.ins().ireduce(types::I16, raw_value);
            (val, types::I16)
        }
        TypeId::I32 | TypeId::U32 => {
            let val = builder.ins().ireduce(types::I32, raw_value);
            (val, types::I32)
        }
        // All other types (String, classes, arrays, etc.) are pointers stored as i64
        _ => (raw_value, types::I64),
    }
}

pub(crate) fn convert_to_i64_for_storage(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
) -> Value {
    match value.ty {
        types::F64 => builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), value.value),
        types::F32 => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            uextend_const(builder, types::I64, i32_val)
        }
        types::I8 => uextend_const(builder, types::I64, value.value),
        types::I16 => uextend_const(builder, types::I64, value.value),
        types::I32 => uextend_const(builder, types::I64, value.value),
        types::I64 => value.value,
        // i128 should not reach here - callers must use store_field_value,
        // split_i128_for_storage, or store_i128_to_stack instead
        types::I128 => panic!("i128 must use store_field_value for 2-slot storage"),
        types::F128 => panic!("f128 must use store_field_value for 2-slot storage"),
        _ => value.value,
    }
}

/// Split an i128 value into (low, high) i64 halves.
/// Used for fallible returns and stack storage of wide types.
pub(crate) fn split_i128_for_storage(
    builder: &mut FunctionBuilder,
    value: Value,
) -> (Value, Value) {
    let low = builder.ins().ireduce(types::I64, value);
    let sixty_four_i64 = builder.ins().iconst(types::I64, 64);
    let sixty_four = uextend_const(builder, types::I128, sixty_four_i64);
    let shifted = builder.ins().ushr(value, sixty_four);
    let high = builder.ins().ireduce(types::I64, shifted);
    (low, high)
}

/// Reconstruct an i128 from (low, high) i64 halves.
/// Reverse of `split_i128_for_storage`.
pub(crate) fn reconstruct_i128(builder: &mut FunctionBuilder, low: Value, high: Value) -> Value {
    let low_ext = uextend_const(builder, types::I128, low);
    let high_ext = uextend_const(builder, types::I128, high);
    let sixty_four_i64 = builder.ins().iconst(types::I64, 64);
    let sixty_four = uextend_const(builder, types::I128, sixty_four_i64);
    let high_shifted = builder.ins().ishl(high_ext, sixty_four);
    builder.ins().bor(high_shifted, low_ext)
}

/// Store an i128 value to a stack slot at the given offset (uses 16 bytes: 2 x 8-byte slots).
pub(crate) fn store_i128_to_stack(
    builder: &mut FunctionBuilder,
    value: Value,
    slot: codegen::ir::StackSlot,
    offset: i32,
) {
    let (low, high) = split_i128_for_storage(builder, value);
    builder.ins().stack_store(low, slot, offset);
    builder.ins().stack_store(high, slot, offset + 8);
}

/// Store a field value to a stack slot, handling i128 which needs 2 x 8-byte slots.
/// For i128: stores low 64 bits at `offset`, high 64 bits at `offset + 8`.
/// For all other types: stores via convert_to_i64_for_storage at `offset`.
/// Returns the number of bytes consumed (8 for normal types, 16 for i128).
pub(crate) fn store_value_to_stack(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    slot: codegen::ir::StackSlot,
    offset: i32,
) -> i32 {
    if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
        let i128_bits = wide.to_i128_bits(builder, value.value);
        store_i128_to_stack(builder, i128_bits, slot, offset);
        16
    } else {
        let store_val = convert_to_i64_for_storage(builder, value);
        builder.ins().stack_store(store_val, slot, offset);
        8
    }
}

/// Store a field value into a class instance, handling wide types (i128) that need 2 slots.
/// For i128: stores low 64 bits in `slot`, high 64 bits in `slot+1`.
/// For all other types: stores via convert_to_i64_for_storage in a single slot.
///
/// Clears `field_cache` after the store — the mutation invalidates cached
/// field reads for the same instance.
pub(crate) fn store_field_value(
    cg: &mut crate::context::Cg,
    set_func_ref: codegen::ir::FuncRef,
    instance_ptr: Value,
    slot: usize,
    value: &CompiledValue,
) {
    let slot_val = cg.iconst_cached(types::I32, slot as i64);

    if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
        // Split wide values into low/high halves and store in 2 consecutive slots.
        let i128_bits = wide.to_i128_bits(cg.builder, value.value);
        let (low, high) = split_i128_for_storage(cg.builder, i128_bits);
        cg.builder
            .ins()
            .call(set_func_ref, &[instance_ptr, slot_val, low]);
        let high_slot = cg.iconst_cached(types::I32, (slot + 1) as i64);
        cg.builder
            .ins()
            .call(set_func_ref, &[instance_ptr, high_slot, high]);
    } else {
        let store_value = convert_to_i64_for_storage(cg.builder, value);
        cg.builder
            .ins()
            .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
    }
    cg.field_cache.clear();
}

/// Load a field value from a class instance, handling wide types (i128) that use 2 slots.
/// For i128: loads low 64 bits from `slot` and high 64 bits from `slot+1`, reconstructs i128.
/// For all other types: loads from a single slot via convert_field_value_id.
pub(crate) fn load_wide_field(
    cg: &mut crate::context::Cg,
    get_func_ref: codegen::ir::FuncRef,
    instance_ptr: Value,
    slot: usize,
) -> Value {
    let slot_val = cg.iconst_cached(types::I32, slot as i64);
    let low_raw = cg
        .builder
        .ins()
        .call(get_func_ref, &[instance_ptr, slot_val]);
    let low = cg.builder.func.dfg.inst_results(low_raw)[0];

    let high_slot = cg.iconst_cached(types::I32, (slot + 1) as i64);
    let high_raw = cg
        .builder
        .ins()
        .call(get_func_ref, &[instance_ptr, high_slot]);
    let high = cg.builder.func.dfg.inst_results(high_raw)[0];

    reconstruct_i128(cg.builder, low, high)
}
