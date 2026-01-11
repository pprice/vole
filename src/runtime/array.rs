// src/runtime/array.rs

use crate::runtime::value::{RcHeader, TYPE_ARRAY, TaggedValue};
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

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let data = if capacity > 0 {
                let data_layout = Layout::array::<TaggedValue>(capacity).unwrap();
                alloc(data_layout) as *mut TaggedValue
            } else {
                ptr::null_mut()
            };

            ptr::write(&mut (*ptr).header, RcHeader::new(TYPE_ARRAY));
            ptr::write(&mut (*ptr).len, 0);
            ptr::write(&mut (*ptr).capacity, capacity);
            ptr::write(&mut (*ptr).data, data);

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
                let layout = Layout::array::<TaggedValue>(new_cap).unwrap();
                alloc(layout) as *mut TaggedValue
            } else {
                let old_layout = Layout::array::<TaggedValue>(old_cap).unwrap();
                let new_layout = Layout::array::<TaggedValue>(new_cap).unwrap();
                realloc((*arr).data as *mut u8, old_layout, new_layout.size()) as *mut TaggedValue
            };

            if new_data.is_null() {
                let layout = Layout::array::<TaggedValue>(new_cap).unwrap();
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
        unsafe {
            debug_assert!(index < (*arr).len);
            ptr::read((*arr).data.add(index))
        }
    }

    /// Set element at index
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray` and
    /// `index` must be less than the array length
    #[inline]
    pub unsafe fn set(arr: *mut Self, index: usize, value: TaggedValue) {
        unsafe {
            debug_assert!(index < (*arr).len);
            ptr::write((*arr).data.add(index), value);
        }
    }

    /// Get array length
    ///
    /// # Safety
    /// `arr` must be a valid pointer to an initialized `RcArray`
    #[inline]
    pub unsafe fn len(arr: *const Self) -> usize {
        unsafe { (*arr).len }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcArray`
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        unsafe {
            if !ptr.is_null() {
                (*ptr).header.inc();
            }
        }
    }

    /// Decrement reference count and free if zero
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcArray`
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        if ptr.is_null() {
            return;
        }

        unsafe {
            let prev = (*ptr).header.dec();
            if prev == 1 {
                let cap = (*ptr).capacity;
                if cap > 0 && !(*ptr).data.is_null() {
                    let data_layout = Layout::array::<TaggedValue>(cap).unwrap();
                    dealloc((*ptr).data as *mut u8, data_layout);
                }

                let layout = Layout::new::<RcArray>();
                dealloc(ptr as *mut u8, layout);
            }
        }
    }
}
