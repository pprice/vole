//! Interface vtable generation and context.
//!
//! This module contains:
//! - Vtable registry and compilation for interface implementations
//! - VtableCtx trait for providing context to vtable operations

pub(crate) mod vtable;
pub(crate) mod vtable_ctx;

pub(crate) use vtable::{
    InterfaceVtableRegistry, box_interface_value_id, interface_method_slot_by_type_def_id,
};
pub(crate) use vtable_ctx::VtableCtx;
