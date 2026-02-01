// src/runtime/instance.rs

use crate::alloc_track;
use crate::type_registry::get_instance_type_info;
use crate::value::{RcHeader, TYPE_INSTANCE, rc_dec, rc_inc};
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

/// Reference-counted class instance
/// Layout: RcHeader, then n slots of 64-bit values
#[repr(C)]
pub struct RcInstance {
    pub header: RcHeader,
    pub type_id: u32, // Type identifier for this class
    pub field_count: u32, // Number of fields
                      // Fields follow inline as 64-bit slots
}

impl RcInstance {
    /// Allocate a new instance with the given number of fields
    pub fn new(type_id: u32, field_count: u32, runtime_type_id: u32) -> *mut Self {
        let layout = Self::layout_for_fields(field_count as usize);

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(runtime_type_id, instance_drop),
            );
            ptr::write(&mut (*ptr).type_id, type_id);
            ptr::write(&mut (*ptr).field_count, field_count);

            // Zero-initialize fields
            let fields_ptr = Self::fields_ptr(ptr);
            for i in 0..field_count as usize {
                ptr::write(fields_ptr.add(i), 0u64);
            }

            alloc_track::track_alloc(TYPE_INSTANCE);
            ptr
        }
    }

    fn layout_for_fields(field_count: usize) -> Layout {
        let size = size_of::<RcInstance>() + field_count * 8;
        let align = align_of::<RcInstance>();
        Layout::from_size_align(size, align).expect("instance layout overflow")
    }

    /// Get pointer to the fields array (mutable)
    ///
    /// # Safety
    /// The pointer must point to a valid, properly initialized `RcInstance`.
    pub unsafe fn fields_ptr(ptr: *mut Self) -> *mut u64 {
        unsafe { (ptr as *mut u8).add(size_of::<RcInstance>()) as *mut u64 }
    }

    /// Get pointer to the fields array (const)
    ///
    /// # Safety
    /// The pointer must point to a valid, properly initialized `RcInstance`.
    unsafe fn fields_ptr_const(ptr: *const Self) -> *const u64 {
        unsafe { (ptr as *const u8).add(size_of::<RcInstance>()) as *const u64 }
    }

    /// Get field value by slot index
    ///
    /// # Safety
    /// The pointer must point to a valid, properly initialized `RcInstance`,
    /// and `slot` must be less than `field_count`.
    #[inline]
    pub unsafe fn get_field(ptr: *const Self, slot: usize) -> u64 {
        unsafe {
            let fields = Self::fields_ptr_const(ptr);
            *fields.add(slot)
        }
    }

    /// Set field value by slot index
    ///
    /// # Safety
    /// The pointer must point to a valid, properly initialized `RcInstance`,
    /// and `slot` must be less than `field_count`.
    #[inline]
    pub unsafe fn set_field(ptr: *mut Self, slot: usize, value: u64) {
        unsafe {
            let fields = Self::fields_ptr(ptr);
            *fields.add(slot) = value;
        }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// The pointer must be null or point to a valid, properly initialized `RcInstance`.
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        rc_inc(ptr as *mut u8);
    }

    /// Decrement reference count and free if zero (via unified rc_dec + drop_fn)
    ///
    /// # Safety
    /// The pointer must be null or point to a valid, properly initialized `RcInstance`.
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }
}

/// Drop function for RcInstance, called by rc_dec when refcount reaches zero.
/// Walks fields using the type registry, decrements RC fields via rc_dec,
/// then frees the instance memory.
///
/// # Safety
/// `ptr` must point to a valid `RcInstance` allocation with refcount already at zero.
unsafe extern "C" fn instance_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(TYPE_INSTANCE);
    unsafe {
        let inst = ptr as *mut RcInstance;
        let type_id = (*inst).type_id;
        let field_count = (*inst).field_count as usize;

        // Look up field types and clean up reference-typed fields
        if let Some(type_info) = get_instance_type_info(type_id) {
            let fields_ptr = RcInstance::fields_ptr(inst);
            for (slot, field_type) in type_info.field_types.iter().enumerate() {
                if slot >= field_count {
                    break;
                }
                let field_value = *fields_ptr.add(slot);
                if field_value == 0 {
                    continue; // Null pointer, skip
                }
                if field_type.needs_cleanup() {
                    // All RC types (String, Array, Instance) go through rc_dec,
                    // which will call their respective drop_fn.
                    rc_dec(field_value as *mut u8);
                }
            }
        }

        let layout = RcInstance::layout_for_fields(field_count);
        dealloc(ptr, layout);
    }
}

// Functions exposed to JIT-compiled code
#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_new(
    type_id: u32,
    field_count: u32,
    runtime_type_id: u32,
) -> *mut RcInstance {
    RcInstance::new(type_id, field_count, runtime_type_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_inc(ptr: *mut RcInstance) {
    rc_inc(ptr as *mut u8);
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_dec(ptr: *mut RcInstance) {
    rc_dec(ptr as *mut u8);
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_get_field(ptr: *const RcInstance, slot: u32) -> u64 {
    if ptr.is_null() {
        return 0;
    }
    unsafe { RcInstance::get_field(ptr, slot as usize) }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_set_field(ptr: *mut RcInstance, slot: u32, value: u64) {
    if ptr.is_null() {
        return;
    }
    unsafe { RcInstance::set_field(ptr, slot as usize, value) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::TYPE_INSTANCE;

    #[test]
    fn create_and_access_instance() {
        let inst = RcInstance::new(1, 2, TYPE_INSTANCE);
        unsafe {
            assert_eq!((*inst).field_count, 2);

            RcInstance::set_field(inst, 0, 42);
            RcInstance::set_field(inst, 1, 100);

            assert_eq!(RcInstance::get_field(inst, 0), 42);
            assert_eq!(RcInstance::get_field(inst, 1), 100);

            RcInstance::dec_ref(inst);
        }
    }
}
