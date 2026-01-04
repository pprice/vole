// src/runtime/closure.rs

//! Closure runtime support
//!
//! This module provides the runtime representation for closures (lambdas with captures).
//! A closure consists of a function pointer plus an array of pointers to captured variables.

use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

/// Runtime representation of a closure
///
/// This is a variable-length struct: the captures array extends beyond the struct size.
/// Each capture is stored as a pointer to the captured value (which may be heap-allocated
/// if the variable needs to outlive its original scope).
#[repr(C)]
pub struct Closure {
    /// Pointer to the compiled function
    pub func_ptr: *const u8,
    /// Number of captured values
    pub num_captures: usize,
    // Captures array follows in memory (flexible array member pattern)
}

impl Closure {
    /// Calculate the layout for a closure with the given number of captures
    fn layout(num_captures: usize) -> Layout {
        let ptr_size = std::mem::size_of::<*mut u8>();
        let captures_size = num_captures
            .checked_mul(ptr_size)
            .expect("closure captures size overflow");
        let total_size = std::mem::size_of::<Closure>()
            .checked_add(captures_size)
            .expect("closure total size overflow");
        Layout::from_size_align(total_size, std::mem::align_of::<Closure>()).unwrap()
    }

    /// Get pointer to the captures array
    ///
    /// # Safety
    /// The closure pointer must be valid and properly initialized.
    unsafe fn captures_ptr(closure: *mut Closure) -> *mut *mut u8 {
        unsafe { (closure as *mut u8).add(std::mem::size_of::<Closure>()) as *mut *mut u8 }
    }

    /// Allocate a new closure with space for captures
    ///
    /// # Safety
    /// The func_ptr must be a valid function pointer or null.
    pub unsafe fn alloc(func_ptr: *const u8, num_captures: usize) -> *mut Closure {
        unsafe {
            let layout = Self::layout(num_captures);
            let ptr = alloc(layout) as *mut Closure;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            (*ptr).func_ptr = func_ptr;
            (*ptr).num_captures = num_captures;
            // Initialize capture pointers to null
            let captures = Self::captures_ptr(ptr);
            for i in 0..num_captures {
                *captures.add(i) = ptr::null_mut();
            }
            ptr
        }
    }

    /// Get capture at index
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized.
    /// - The index must be less than num_captures.
    pub unsafe fn get_capture(closure: *const Closure, index: usize) -> *mut u8 {
        unsafe {
            debug_assert!(index < (*closure).num_captures);
            let captures = Self::captures_ptr(closure as *mut Closure);
            *captures.add(index)
        }
    }

    /// Set capture at index
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized.
    /// - The index must be less than num_captures.
    /// - The ptr must be valid or null.
    pub unsafe fn set_capture(closure: *mut Closure, index: usize, ptr: *mut u8) {
        unsafe {
            debug_assert!(index < (*closure).num_captures);
            let captures = Self::captures_ptr(closure);
            *captures.add(index) = ptr;
        }
    }

    /// Get the function pointer from a closure
    ///
    /// # Safety
    /// The closure pointer must be valid and properly initialized.
    pub unsafe fn get_func(closure: *const Closure) -> *const u8 {
        unsafe { (*closure).func_ptr }
    }

    /// Free a closure
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized, or null.
    /// - The caller must ensure captures are properly managed (freed or still in use elsewhere).
    pub unsafe fn free(closure: *mut Closure) {
        if !closure.is_null() {
            unsafe {
                let layout = Self::layout((*closure).num_captures);
                dealloc(closure as *mut u8, layout);
            }
        }
    }
}

// Functions exposed to JIT-compiled code
// These functions are called from JIT-generated code which is responsible for
// ensuring pointer validity.

/// Allocate a new closure with space for captures
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_alloc(func_ptr: *const u8, num_captures: usize) -> *mut Closure {
    // Safety: Called from JIT code which ensures func_ptr validity
    unsafe { Closure::alloc(func_ptr, num_captures) }
}

/// Get capture at index
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_get_capture(closure: *const Closure, index: usize) -> *mut u8 {
    // Safety: Called from JIT code which ensures pointer validity and index bounds
    unsafe { Closure::get_capture(closure, index) }
}

/// Set capture at index
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_set_capture(closure: *mut Closure, index: usize, ptr: *mut u8) {
    // Safety: Called from JIT code which ensures pointer validity and index bounds
    unsafe { Closure::set_capture(closure, index, ptr) }
}

/// Get the function pointer from a closure
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_get_func(closure: *const Closure) -> *const u8 {
    // Safety: Called from JIT code which ensures pointer validity
    unsafe { Closure::get_func(closure) }
}

/// Free a closure (caller must ensure captures are properly managed)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_free(closure: *mut Closure) {
    // Safety: Called from JIT code which ensures pointer validity
    unsafe { Closure::free(closure) }
}

/// Allocate heap memory for a captured variable
///
/// Returns a pointer to heap-allocated memory of the given size.
/// The caller is responsible for freeing this memory.
#[unsafe(no_mangle)]
pub extern "C" fn vole_heap_alloc(size: usize) -> *mut u8 {
    use std::alloc::{Layout, alloc};
    if size == 0 {
        return std::ptr::NonNull::dangling().as_ptr();
    }
    let layout = Layout::from_size_align(size, 8).expect("invalid layout");
    // Safety: layout is valid and non-zero size
    unsafe { alloc(layout) }
}

/// Free heap-allocated memory
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_heap_free(ptr: *mut u8, size: usize) {
    use std::alloc::{Layout, dealloc};
    if ptr.is_null() || size == 0 {
        return;
    }
    let layout = Layout::from_size_align(size, 8).expect("invalid layout");
    // Safety: Called from JIT code which ensures pointer validity
    unsafe { dealloc(ptr, layout) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_closure_alloc_and_access() {
        unsafe {
            let func_ptr = 0x1234 as *const u8;
            let closure = Closure::alloc(func_ptr, 2);

            assert_eq!((*closure).func_ptr, func_ptr);
            assert_eq!((*closure).num_captures, 2);

            // Verify captures are initialized to null
            assert!(Closure::get_capture(closure, 0).is_null());
            assert!(Closure::get_capture(closure, 1).is_null());

            // Set captures
            let val1 = 42i64;
            let val2 = 100i64;
            Closure::set_capture(closure, 0, &val1 as *const i64 as *mut u8);
            Closure::set_capture(closure, 1, &val2 as *const i64 as *mut u8);

            // Get captures
            let cap1 = Closure::get_capture(closure, 0) as *const i64;
            let cap2 = Closure::get_capture(closure, 1) as *const i64;
            assert_eq!(*cap1, 42);
            assert_eq!(*cap2, 100);

            // Get function pointer
            assert_eq!(Closure::get_func(closure), func_ptr);

            // Free
            Closure::free(closure);
        }
    }

    #[test]
    fn test_closure_zero_captures() {
        unsafe {
            let func_ptr = 0xABCD as *const u8;
            let closure = Closure::alloc(func_ptr, 0);

            assert_eq!((*closure).func_ptr, func_ptr);
            assert_eq!((*closure).num_captures, 0);

            Closure::free(closure);
        }
    }

    #[test]
    fn test_extern_c_functions() {
        let func_ptr = 0x5678 as *const u8;
        let closure = vole_closure_alloc(func_ptr, 1);

        unsafe {
            assert_eq!((*closure).func_ptr, func_ptr);
            assert_eq!((*closure).num_captures, 1);
        }

        let val = 999i64;
        vole_closure_set_capture(closure, 0, &val as *const i64 as *mut u8);

        let cap = vole_closure_get_capture(closure, 0) as *const i64;
        unsafe {
            assert_eq!(*cap, 999);
        }

        assert_eq!(vole_closure_get_func(closure), func_ptr);

        vole_closure_free(closure);
    }

    #[test]
    fn test_closure_free_null() {
        // Should not panic when freeing null
        unsafe {
            Closure::free(ptr::null_mut());
        }
        vole_closure_free(ptr::null_mut());
    }
}
