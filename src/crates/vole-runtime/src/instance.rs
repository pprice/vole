// src/runtime/instance.rs

use crate::alloc_track;
use crate::closure::vole_heap_free;
use crate::type_registry::{FieldTypeTag, get_instance_type_info};
use crate::value::{RcHeader, RuntimeTypeId, rc_dec, rc_inc, union_heap_cleanup};
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

        // SAFETY: `layout` from `layout_for_fields` guarantees valid size/alignment.
        // After the null check, `ptr` is a valid allocation. `ptr::write` initializes
        // each field without dropping uninitialized memory. The allocation includes
        // space for `field_count` u64 field slots.
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

            alloc_track::track_alloc(RuntimeTypeId::Instance as u32);
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
        // SAFETY: Caller guarantees `ptr` is a valid `RcInstance`. Fields start at
        // offset `size_of::<RcInstance>()`, within the allocation from `layout_for_fields`.
        unsafe { (ptr as *mut u8).add(size_of::<RcInstance>()) as *mut u64 }
    }

    /// Get pointer to the fields array (const)
    ///
    /// # Safety
    /// The pointer must point to a valid, properly initialized `RcInstance`.
    unsafe fn fields_ptr_const(ptr: *const Self) -> *const u64 {
        // SAFETY: Caller guarantees `ptr` is a valid `RcInstance`. Fields start at
        // a fixed offset after the struct header, within the allocation bounds.
        unsafe { (ptr as *const u8).add(size_of::<RcInstance>()) as *const u64 }
    }

    /// Get field value by slot index
    ///
    /// # Safety
    /// The pointer must point to a valid, properly initialized `RcInstance`,
    /// and `slot` must be less than `field_count`.
    #[inline]
    pub unsafe fn get_field(ptr: *const Self, slot: usize) -> u64 {
        // SAFETY: Caller guarantees `ptr` is valid and `slot < field_count`.
        // `fields_ptr_const` returns a valid pointer; `add(slot)` stays in bounds.
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
        // SAFETY: Caller guarantees `ptr` is valid and `slot < field_count`.
        // `fields_ptr` returns a valid pointer; `add(slot)` stays in bounds.
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
    alloc_track::track_dealloc(RuntimeTypeId::Instance as u32);
    // SAFETY: Called by `rc_dec` when refcount reaches zero, so `ptr` is a valid
    // `RcInstance` with no other live references. Field reads, RC cleanup of
    // field values, and final `dealloc` are all valid on the live allocation.
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
                match field_type {
                    FieldTypeTag::Rc => {
                        // RC types (String, Array, Instance) go through rc_dec,
                        // which will call their respective drop_fn.
                        rc_dec(field_value as *mut u8);
                    }
                    FieldTypeTag::UnionHeap => {
                        // Union heap buffer: conditionally rc_dec the payload,
                        // then free the buffer.
                        union_heap_cleanup(field_value as *mut u8);
                    }
                    FieldTypeTag::Interface => {
                        // Interface fat pointer: heap-allocated [data_word, vtable_ptr].
                        // The RC-managed object is the data_word at offset 0.
                        let fat_ptr = field_value as *const u64;
                        let data_word = *fat_ptr;
                        if data_word != 0 {
                            rc_dec(data_word as *mut u8);
                        }
                        // Free the 16-byte fat pointer allocation (2 * size_of::<u64>()).
                        vole_heap_free(field_value as *mut u8, 16);
                    }
                    FieldTypeTag::UnknownHeap => {
                        // Unknown TaggedValue: heap-allocated [tag: u64, value: u64].
                        // Check tag to determine if value is RC, then free the buffer.
                        crate::value::unknown_heap_cleanup(field_value as *mut u8);
                    }
                    FieldTypeTag::Value => {}
                }
            }
        }

        let layout = RcInstance::layout_for_fields(field_count);
        dealloc(ptr, layout);
    }
}

// =============================================================================
// FFI functions for JIT-compiled code
// =============================================================================
//
// Safety contract between JIT codegen and runtime:
//
// The JIT guarantees that all pointers passed to these functions are either:
//   (a) null, or
//   (b) valid pointers to properly initialized, live allocations.
//
// Null handling philosophy: all FFI functions that receive a pointer defensively
// check for null and return a zero/nil/no-op result rather than crashing. This
// provides a safety net for the common case where nil propagates through field
// access chains (e.g. `obj.field.subfield` where `obj` is nil). The JIT does
// NOT emit null checks before every FFI call -- instead, the runtime absorbs
// nil gracefully, matching Vole's "nil propagates" semantics.
//
// Bounds checking: `vole_instance_get_field` and `vole_instance_set_field` do
// NOT bounds-check `slot` in release builds. The JIT statically knows the field
// count for each class from type-checking, so an out-of-bounds slot would be a
// compiler bug, not a user error. A debug_assert in the underlying methods
// catches this during development.
// =============================================================================

/// Allocate a new class instance with the given type ID, field count, and
/// runtime type ID (used for RC header / drop dispatch).
///
/// # JIT contract
/// - `type_id` and `runtime_type_id` come from the type registry; codegen
///   ensures they are valid IDs registered via `vole_register_instance_type`.
/// - `field_count` matches the class definition known at compile time.
/// - The returned pointer is non-null and has refcount 1.
#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_new(
    type_id: u32,
    field_count: u32,
    runtime_type_id: u32,
) -> *mut RcInstance {
    RcInstance::new(type_id, field_count, runtime_type_id)
}

/// Increment the reference count of an instance.
///
/// # JIT contract
/// `ptr` must be null or a valid `RcInstance` pointer. Null is a no-op
/// (delegated to `rc_inc`).
#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_inc(ptr: *mut RcInstance) {
    rc_inc(ptr as *mut u8);
}

/// Decrement the reference count of an instance. Frees the instance
/// (via `instance_drop`) when the count reaches zero.
///
/// # JIT contract
/// `ptr` must be null or a valid `RcInstance` pointer. Null is a no-op
/// (delegated to `rc_dec`).
#[unsafe(no_mangle)]
pub extern "C" fn vole_instance_dec(ptr: *mut RcInstance) {
    rc_dec(ptr as *mut u8);
}

/// Read a field value from an instance by slot index.
///
/// Returns 0 if `ptr` is null, supporting Vole's nil-propagation semantics
/// (e.g. `nil_instance.field` evaluates to 0/nil rather than crashing).
///
/// # JIT contract
/// - `ptr` is null or a valid `RcInstance` pointer.
/// - `slot` is within bounds (< field_count). The JIT knows the field count
///   from static type-checking, so this is not bounds-checked in release.
///   A debug_assert in `RcInstance::get_field` catches bugs during development.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_instance_get_field(ptr: *const RcInstance, slot: u32) -> u64 {
    if ptr.is_null() {
        return 0;
    }
    // SAFETY: Null check above guarantees `ptr` is non-null. Per JIT contract,
    // non-null `ptr` is a valid `RcInstance` and `slot` is within bounds.
    unsafe { RcInstance::get_field(ptr, slot as usize) }
}

/// Write a field value to an instance by slot index.
///
/// No-ops if `ptr` is null, supporting nil-propagation semantics.
///
/// # JIT contract
/// - `ptr` is null or a valid `RcInstance` pointer.
/// - `slot` is within bounds (< field_count). Not bounds-checked in release;
///   the JIT guarantees correctness from static type information.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_instance_set_field(ptr: *mut RcInstance, slot: u32, value: u64) {
    if ptr.is_null() {
        return;
    }
    // SAFETY: Null check above guarantees `ptr` is non-null. Per JIT contract,
    // non-null `ptr` is a valid `RcInstance` and `slot` is within bounds.
    unsafe { RcInstance::set_field(ptr, slot as usize, value) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::RuntimeTypeId;

    #[test]
    fn create_and_access_instance() {
        let inst = RcInstance::new(1, 2, RuntimeTypeId::Instance as u32);
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
