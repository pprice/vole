// src/runtime/array.rs

use crate::alloc_track;
use crate::value::{RcHeader, RuntimeTypeId, TaggedValue, rc_dec, rc_inc};
use std::alloc::{Layout, alloc, dealloc, realloc};
use std::ptr;

/// Reference-counted dynamic array
#[repr(C)]
pub struct RcArray {
    pub header: RcHeader,
    pub len: usize,
    pub capacity: usize,
    pub data: *mut TaggedValue,
}

impl RcArray {
    /// Allocate a new empty array
    pub fn new() -> *mut Self {
        Self::with_capacity(0)
    }

    /// Allocate with initial capacity
    pub fn with_capacity(capacity: usize) -> *mut Self {
        let layout = Layout::new::<RcArray>();

        // SAFETY: Layout is valid (fixed-size RcArray). All fields are initialized
        // via ptr::write before the pointer is returned.
        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let data = if capacity > 0 {
                let data_layout = Layout::array::<TaggedValue>(capacity)
                    .expect("array capacity exceeds maximum allocation size");
                alloc(data_layout) as *mut TaggedValue
            } else {
                ptr::null_mut()
            };

            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(RuntimeTypeId::Array as u32, array_drop),
            );
            ptr::write(&mut (*ptr).len, 0);
            ptr::write(&mut (*ptr).capacity, capacity);
            ptr::write(&mut (*ptr).data, data);

            alloc_track::track_alloc(RuntimeTypeId::Array as u32);
            ptr
        }
    }

    /// Push a value onto the array
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray`
    pub unsafe fn push(arr: *mut Self, value: TaggedValue) {
        unsafe {
            let len = (*arr).len;
            let cap = (*arr).capacity;

            if len >= cap {
                Self::grow(arr);
            }

            ptr::write((*arr).data.add(len), value);
            (*arr).len = len + 1;
        }
    }

    /// Grow the array capacity
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray`
    unsafe fn grow(arr: *mut Self) {
        unsafe {
            let old_cap = (*arr).capacity;
            let new_cap = if old_cap == 0 { 4 } else { old_cap * 2 };

            let new_data = if old_cap == 0 {
                let layout = Layout::array::<TaggedValue>(new_cap)
                    .expect("array capacity exceeds maximum allocation size");
                alloc(layout) as *mut TaggedValue
            } else {
                let old_layout = Layout::array::<TaggedValue>(old_cap)
                    .expect("array capacity exceeds maximum allocation size");
                let new_layout = Layout::array::<TaggedValue>(new_cap)
                    .expect("array capacity exceeds maximum allocation size");
                realloc((*arr).data as *mut u8, old_layout, new_layout.size()) as *mut TaggedValue
            };

            if new_data.is_null() {
                let layout = Layout::array::<TaggedValue>(new_cap)
                    .expect("array capacity exceeds maximum allocation size");
                std::alloc::handle_alloc_error(layout);
            }

            (*arr).data = new_data;
            (*arr).capacity = new_cap;
        }
    }

    /// Get element at index
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray` and
    /// `index` must be less than the array length
    #[inline]
    pub unsafe fn get(arr: *const Self, index: usize) -> TaggedValue {
        // SAFETY: Caller guarantees arr is valid and index < len (asserted in debug).
        unsafe {
            debug_assert!(index < (*arr).len);
            ptr::read((*arr).data.add(index))
        }
    }

    /// Set element at index, decrementing RC of old value if needed.
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray` and
    /// `index` must be less than the array length
    #[inline]
    pub unsafe fn set(arr: *mut Self, index: usize, value: TaggedValue) {
        // SAFETY: Caller guarantees arr is valid and index < len (asserted in debug).
        // Old value is read and RC-decremented before being overwritten.
        unsafe {
            debug_assert!(index < (*arr).len);
            // Dec the old value being overwritten
            let old = ptr::read((*arr).data.add(index));
            old.rc_dec_if_needed();
            ptr::write((*arr).data.add(index), value);
        }
    }

    /// Get array length
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray`
    #[inline]
    pub unsafe fn len(arr: *const Self) -> usize {
        // SAFETY: Caller guarantees arr is a valid, initialized RcArray pointer.
        unsafe { (*arr).len }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcArray`
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        rc_inc(ptr as *mut u8);
    }

    /// Decrement reference count and free if zero (via unified rc_dec + drop_fn)
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcArray`
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }
}

/// Drop function for RcArray, called by rc_dec when refcount reaches zero.
/// Decrements RC for all contained RC elements, frees the data buffer,
/// and deallocates the RcArray struct itself.
///
/// # Safety
/// `ptr` must point to a valid `RcArray` allocation with refcount already at zero.
unsafe extern "C" fn array_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(RuntimeTypeId::Array as u32);
    // SAFETY: Called only by rc_dec when refcount reaches zero. ptr is a valid
    // RcArray allocation. All contained elements are RC-decremented before
    // the data buffer and header are freed.
    unsafe {
        let arr = ptr as *mut RcArray;
        let len = (*arr).len;
        let cap = (*arr).capacity;

        // Dec all contained RC elements before freeing
        if len > 0 && !(*arr).data.is_null() {
            for i in 0..len {
                let tv = ptr::read((*arr).data.add(i));
                tv.rc_dec_if_needed();
            }
        }

        if cap > 0 && !(*arr).data.is_null() {
            let data_layout = Layout::array::<TaggedValue>(cap)
                .expect("array capacity exceeds maximum allocation size");
            dealloc((*arr).data as *mut u8, data_layout);
        }

        let layout = Layout::new::<RcArray>();
        dealloc(ptr, layout);
    }
}
