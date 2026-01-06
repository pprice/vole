//! Iterator runtime support
//!
//! Provides runtime representation for iterators.

use crate::runtime::array::RcArray;

/// Runtime iterator state for arrays
#[repr(C)]
pub struct ArrayIterator {
    /// Pointer to the source array
    pub array: *const RcArray,
    /// Current index
    pub index: i64,
}

/// Create a new array iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter(array: *const RcArray) -> *mut ArrayIterator {
    // Increment ref count on array so it stays alive while iterator exists
    unsafe {
        if !array.is_null() {
            RcArray::inc_ref(array as *mut RcArray);
        }
    }

    let iter = Box::new(ArrayIterator { array, index: 0 });
    Box::into_raw(iter)
}

/// Free an array iterator
///
/// TODO: Iterator cleanup is currently deferred. When Vole adds drop semantics,
/// iterators should call vole_array_iter_free when they go out of scope.
/// For now, iterators leak - this is acceptable for short-lived test programs.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_free(iter: *mut ArrayIterator) {
    if iter.is_null() {
        return;
    }

    unsafe {
        // Decrement ref count on array
        let array = (*iter).array;
        if !array.is_null() {
            RcArray::dec_ref(array as *mut RcArray);
        }

        // Free the iterator
        drop(Box::from_raw(iter));
    }
}

/// Get next value from array iterator
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_next(iter: *mut ArrayIterator, out_value: *mut i64) -> i64 {
    let iter = unsafe { &mut *iter };
    if iter.index >= unsafe { (*iter.array).len } as i64 {
        return 0; // Done
    }
    let tagged_value = unsafe {
        let data = (*iter.array).data;
        *data.add(iter.index as usize)
    };
    // Store the value part (ignoring tag for now - iterators return element type)
    unsafe { *out_value = tagged_value.value as i64 };
    iter.index += 1;
    1 // Has value
}
