// src/codegen/structs/mod.rs
//
// Struct/class operations for code generation.

mod access;
mod builtin_methods;
pub(crate) mod helpers;
mod iterator_methods;
mod literals;
mod method_dispatch;
pub(crate) mod methods;
mod static_methods;
mod vir_literals;

#[cfg(test)]
pub(crate) use helpers::field_flat_slots;
pub(crate) use helpers::{
    convert_field_value_id, convert_to_i64_for_storage, reconstruct_i128, split_i128_for_storage,
    store_value_to_stack, struct_total_byte_size,
};
