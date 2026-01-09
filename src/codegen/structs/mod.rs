// src/codegen/structs/mod.rs
//
// Struct/class/record operations for code generation.

mod access;
mod helpers;
mod literals;
mod methods;

pub(crate) use helpers::{
    convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type, get_type_name_id,
};
