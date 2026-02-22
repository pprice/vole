// src/codegen/structs/mod.rs
//
// Struct/class operations for code generation.

mod access;
mod builtin_methods;
pub(crate) mod helpers;
mod iterator_methods;
mod literals;
mod method_dispatch;
mod methods;
mod static_methods;

pub(crate) use helpers::{
    convert_field_value_id, convert_to_i64_for_storage, field_flat_slots,
    get_field_slot_and_type_id_cg, reconstruct_i128, split_i128_for_storage, store_value_to_stack,
    struct_flat_slot_count, struct_total_byte_size,
};
