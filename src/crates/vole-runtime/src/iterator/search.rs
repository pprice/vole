//! Iterator search operations: find, any, all.

use crate::closure::Closure;
use std::alloc::{Layout, alloc};
use std::ptr;

use super::types::*;
use super::vole_array_iter_next;

// =============================================================================
// Search methods: find, any, all
// =============================================================================

/// Find the first element matching a predicate, returns T? (optional)
/// Short-circuits on first match.
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after finding (or exhausting).
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_find(iter: *mut RcIterator, predicate: *const Closure) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() || predicate.is_null() {
        // Return nil
        unsafe {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
        }
        if !iter.is_null() {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
        }
        return ptr;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Apply predicate function
        let passes: i8 = unsafe {
            let func_ptr = Closure::get_func(predicate);
            let predicate_fn: extern "C" fn(*const Closure, i64) -> i8 =
                std::mem::transmute(func_ptr);
            predicate_fn(predicate, value)
        };

        // If predicate returns non-zero (true), we found our match
        if passes != 0 {
            // Free the iterator chain
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }

            unsafe {
                ptr::write(ptr, 0u8); // tag 0 = value present
                ptr::write(ptr.add(8) as *mut i64, value);
            }
            return ptr;
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // No match found, return nil
    unsafe {
        ptr::write(ptr, 1u8); // tag 1 = nil
        ptr::write(ptr.add(8) as *mut i64, 0);
    }

    ptr
}

/// Check if any element matches a predicate, returns bool
/// Short-circuits on first true.
/// Frees the iterator after checking.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_any(iter: *mut RcIterator, predicate: *const Closure) -> i8 {
    if iter.is_null() || predicate.is_null() {
        if !iter.is_null() {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
        }
        return 0; // false
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Apply predicate function
        let passes: i8 = unsafe {
            let func_ptr = Closure::get_func(predicate);
            let predicate_fn: extern "C" fn(*const Closure, i64) -> i8 =
                std::mem::transmute(func_ptr);
            predicate_fn(predicate, value)
        };

        // If predicate returns non-zero (true), short-circuit
        if passes != 0 {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
            return 1; // true
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    0 // false - no element matched
}

/// Check if all elements match a predicate, returns bool
/// Short-circuits on first false.
/// Frees the iterator after checking.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_all(iter: *mut RcIterator, predicate: *const Closure) -> i8 {
    if iter.is_null() || predicate.is_null() {
        if !iter.is_null() {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
        }
        // Empty iterator -> all() returns true (vacuous truth)
        // Null predicate is an error condition, return true to be safe
        return 1;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Apply predicate function
        let passes: i8 = unsafe {
            let func_ptr = Closure::get_func(predicate);
            let predicate_fn: extern "C" fn(*const Closure, i64) -> i8 =
                std::mem::transmute(func_ptr);
            predicate_fn(predicate, value)
        };

        // If predicate returns zero (false), short-circuit
        if passes == 0 {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
            return 0; // false
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    1 // true - all elements matched
}
