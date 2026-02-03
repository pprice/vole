// src/runtime/closure.rs

//! Closure runtime support
//!
//! This module provides the runtime representation for closures (lambdas with captures).
//! A closure consists of an RcHeader, a function pointer, and an array of pointers to
//! captured variables. Each capture also has a "kind" byte (0=Value, 1=Rc) so the drop
//! function knows which captures need rc_dec.
//!
//! Layout (flexible array member pattern):
//! ```text
//! [RcHeader: ref_count, type_id, drop_fn]  (16 bytes)
//! [func_ptr: *const u8]                    (8 bytes)
//! [num_captures: usize]                    (8 bytes)
//! [capture_kinds: u8 * num_captures]       (num_captures bytes, padded to 8)
//! [captures: *mut u8 * num_captures]       (num_captures * 8 bytes)
//! ```

use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

use crate::alloc_track;
use crate::value::{RcHeader, TYPE_CLOSURE, rc_dec};

/// Capture kind constants
pub const CAPTURE_KIND_VALUE: u8 = 0;
pub const CAPTURE_KIND_RC: u8 = 1;

/// Runtime representation of a closure
///
/// This is a variable-length struct: the capture_kinds and captures arrays extend
/// beyond the struct size. Each capture is stored as a pointer to the captured value
/// (which may be heap-allocated if the variable needs to outlive its original scope).
#[repr(C)]
pub struct Closure {
    /// Reference counting header
    pub header: RcHeader,
    /// Pointer to the compiled function
    pub func_ptr: *const u8,
    /// Number of captured values
    pub num_captures: usize,
    // capture_kinds: [u8; num_captures]  (padded to 8-byte alignment)
    // captures: [*mut u8; num_captures]
}

/// Round up to the next multiple of pointer size (8 bytes) for alignment.
#[inline]
fn align_to_ptr(size: usize) -> usize {
    let ptr_size = size_of::<*mut u8>();
    (size + ptr_size - 1) & !(ptr_size - 1)
}

impl Closure {
    /// Size of the fixed portion of the struct (header + func_ptr + num_captures)
    const FIXED_SIZE: usize = size_of::<Closure>();

    /// Calculate the layout for a closure with the given number of captures
    fn layout(num_captures: usize) -> Layout {
        let ptr_size = size_of::<*mut u8>();
        // capture_kinds: num_captures bytes, padded to pointer alignment
        let kinds_size = align_to_ptr(num_captures);
        // captures: num_captures pointers
        let captures_size = num_captures
            .checked_mul(ptr_size)
            .expect("closure captures size overflow");
        let trailing = kinds_size
            .checked_add(captures_size)
            .expect("closure trailing size overflow");
        let total_size = Self::FIXED_SIZE
            .checked_add(trailing)
            .expect("closure total size overflow");
        Layout::from_size_align(total_size, align_of::<Closure>()).expect("closure layout overflow")
    }

    /// Get pointer to the capture_kinds array (u8 per capture)
    ///
    /// # Safety
    /// The closure pointer must be valid and properly initialized.
    unsafe fn capture_kinds_ptr(closure: *mut Closure) -> *mut u8 {
        unsafe { (closure as *mut u8).add(Self::FIXED_SIZE) }
    }

    /// Get pointer to the captures array (pointers, after the padded capture_kinds)
    ///
    /// # Safety
    /// The closure pointer must be valid and properly initialized.
    unsafe fn captures_ptr(closure: *mut Closure) -> *mut *mut u8 {
        unsafe {
            let num = (*closure).num_captures;
            let kinds_size = align_to_ptr(num);
            (closure as *mut u8).add(Self::FIXED_SIZE + kinds_size) as *mut *mut u8
        }
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
            // Initialize RcHeader with closure_drop
            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(TYPE_CLOSURE, closure_drop),
            );
            (*ptr).func_ptr = func_ptr;
            (*ptr).num_captures = num_captures;
            // Zero-initialize capture_kinds
            let kinds = Self::capture_kinds_ptr(ptr);
            ptr::write_bytes(kinds, 0, align_to_ptr(num_captures));
            // Initialize capture pointers to null
            let captures = Self::captures_ptr(ptr);
            for i in 0..num_captures {
                *captures.add(i) = ptr::null_mut();
            }
            alloc_track::track_alloc(TYPE_CLOSURE);
            ptr
        }
    }

    /// Get capture at index
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized.
    /// - The index must be less than num_captures.
    #[inline]
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
    #[inline]
    pub unsafe fn set_capture(closure: *mut Closure, index: usize, ptr: *mut u8) {
        unsafe {
            debug_assert!(index < (*closure).num_captures);
            let captures = Self::captures_ptr(closure);
            *captures.add(index) = ptr;
        }
    }

    /// Set the capture kind at index (0=Value, 1=Rc)
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized.
    /// - The index must be less than num_captures.
    #[inline]
    pub unsafe fn set_capture_kind(closure: *mut Closure, index: usize, kind: u8) {
        unsafe {
            debug_assert!(index < (*closure).num_captures);
            let kinds = Self::capture_kinds_ptr(closure);
            *kinds.add(index) = kind;
        }
    }

    /// Get the capture kind at index (0=Value, 1=Rc)
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized.
    /// - The index must be less than num_captures.
    #[inline]
    pub unsafe fn get_capture_kind(closure: *const Closure, index: usize) -> u8 {
        unsafe {
            debug_assert!(index < (*closure).num_captures);
            let kinds = Self::capture_kinds_ptr(closure as *mut Closure);
            *kinds.add(index)
        }
    }

    /// Get the function pointer from a closure
    ///
    /// # Safety
    /// The closure pointer must be valid and properly initialized.
    #[inline]
    pub unsafe fn get_func(closure: *const Closure) -> *const u8 {
        unsafe { (*closure).func_ptr }
    }

    /// Free a closure by decrementing its reference count.
    /// When the refcount reaches zero, `closure_drop` handles cleanup.
    ///
    /// # Safety
    /// - The closure pointer must be valid and properly initialized, or null.
    pub unsafe fn free(closure: *mut Closure) {
        if !closure.is_null() {
            rc_dec(closure as *mut u8);
        }
    }
}

/// Drop function for closures. Called by rc_dec when refcount reaches zero.
///
/// Walks the captures array using capture_kinds:
/// - For each RC capture (kind=1): loads the value from the heap-allocated
///   capture slot, then rc_decs it.
/// - Frees each capture slot's heap allocation.
/// - Deallocates the closure struct itself.
///
/// # Safety
/// `ptr` must point to a valid `Closure` allocation with refcount at zero.
unsafe extern "C" fn closure_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(TYPE_CLOSURE);
    unsafe {
        let closure = ptr as *mut Closure;
        let num = (*closure).num_captures;
        let kinds = Closure::capture_kinds_ptr(closure);
        let captures = Closure::captures_ptr(closure);

        for i in 0..num {
            let capture_ptr = *captures.add(i);
            if capture_ptr.is_null() {
                continue;
            }
            let kind = *kinds.add(i);
            if kind == CAPTURE_KIND_RC {
                // The capture slot holds a heap-allocated box containing
                // an RC pointer. Load the pointer and dec it.
                let rc_ptr = *(capture_ptr as *const *mut u8);
                if !rc_ptr.is_null() {
                    rc_dec(rc_ptr);
                }
            }
            // Free the heap-allocated capture slot.
            // Capture slots are allocated with vole_heap_alloc which uses
            // 8-byte alignment and variable size. We use 8 bytes as the
            // standard capture slot size (one i64/pointer value).
            let slot_layout = Layout::from_size_align_unchecked(8, 8);
            dealloc(capture_ptr, slot_layout);
        }

        // Free the closure struct itself
        let layout = Closure::layout(num);
        dealloc(ptr, layout);
    }
}

// Functions exposed to JIT-compiled code
// These functions are called from JIT-generated code which is responsible for
// ensuring pointer validity.

/// Allocate a new closure with space for captures
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_alloc(func_ptr: *const u8, num_captures: usize) -> *mut Closure {
    // Safety: Called from JIT code which ensures func_ptr validity
    unsafe { Closure::alloc(func_ptr, num_captures) }
}

/// Get capture at index
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_get_capture(closure: *const Closure, index: usize) -> *mut u8 {
    // Safety: Called from JIT code which ensures pointer validity and index bounds
    unsafe { Closure::get_capture(closure, index) }
}

/// Set capture at index
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_set_capture(closure: *mut Closure, index: usize, ptr: *mut u8) {
    // Safety: Called from JIT code which ensures pointer validity and index bounds
    unsafe { Closure::set_capture(closure, index, ptr) }
}

/// Set capture kind at index (0=Value, 1=Rc)
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_set_capture_kind(closure: *mut Closure, index: usize, kind: u8) {
    // Safety: Called from JIT code which ensures pointer validity and index bounds
    unsafe { Closure::set_capture_kind(closure, index, kind) }
}

/// Get the function pointer from a closure
#[unsafe(no_mangle)]
pub extern "C" fn vole_closure_get_func(closure: *const Closure) -> *const u8 {
    // Safety: Called from JIT code which ensures pointer validity
    unsafe { Closure::get_func(closure) }
}

/// Free a closure (decrements refcount; cleanup via closure_drop when zero)
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
        return ptr::NonNull::dangling().as_ptr();
    }
    let layout = Layout::from_size_align(size, 8).expect("invalid layout");
    // Safety: layout is valid and non-zero size
    unsafe { alloc(layout) }
}

/// Free heap-allocated memory
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
    use std::sync::atomic::{AtomicU32, Ordering};

    #[test]
    fn test_closure_alloc_and_access() {
        unsafe {
            let func_ptr = 0x1234 as *const u8;
            let closure = Closure::alloc(func_ptr, 2);

            assert_eq!((*closure).func_ptr, func_ptr);
            assert_eq!((*closure).num_captures, 2);

            // Verify RcHeader is initialized
            assert_eq!((*closure).header.ref_count.load(Ordering::Relaxed), 1);
            assert_eq!((*closure).header.type_id, TYPE_CLOSURE);
            assert!((*closure).header.drop_fn.is_some());

            // Verify captures are initialized to null
            assert!(Closure::get_capture(closure, 0).is_null());
            assert!(Closure::get_capture(closure, 1).is_null());

            // Verify capture_kinds are zero-initialized
            assert_eq!(Closure::get_capture_kind(closure, 0), CAPTURE_KIND_VALUE);
            assert_eq!(Closure::get_capture_kind(closure, 1), CAPTURE_KIND_VALUE);

            // Set captures
            let val1 = 42i64;
            let val2 = 100i64;
            Closure::set_capture(closure, 0, &val1 as *const i64 as *mut u8);
            Closure::set_capture(closure, 1, &val2 as *const i64 as *mut u8);

            // Set capture kinds
            Closure::set_capture_kind(closure, 0, CAPTURE_KIND_VALUE);
            Closure::set_capture_kind(closure, 1, CAPTURE_KIND_RC);

            // Get captures
            let cap1 = Closure::get_capture(closure, 0) as *const i64;
            let cap2 = Closure::get_capture(closure, 1) as *const i64;
            assert_eq!(*cap1, 42);
            assert_eq!(*cap2, 100);

            // Get capture kinds
            assert_eq!(Closure::get_capture_kind(closure, 0), CAPTURE_KIND_VALUE);
            assert_eq!(Closure::get_capture_kind(closure, 1), CAPTURE_KIND_RC);

            // Get function pointer
            assert_eq!(Closure::get_func(closure), func_ptr);

            // Free (without closure_drop running, since captures point to stack)
            // We need to reset captures to null to avoid closure_drop freeing stack pointers
            Closure::set_capture(closure, 0, ptr::null_mut());
            Closure::set_capture(closure, 1, ptr::null_mut());
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
            assert_eq!((*closure).header.type_id, TYPE_CLOSURE);

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

        // Set capture kind via extern C
        vole_closure_set_capture_kind(closure, 0, CAPTURE_KIND_VALUE);
        unsafe {
            assert_eq!(Closure::get_capture_kind(closure, 0), CAPTURE_KIND_VALUE);
        }

        // Reset capture to null before free to avoid freeing stack pointer
        vole_closure_set_capture(closure, 0, ptr::null_mut());
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

    #[test]
    fn test_closure_drop_with_heap_captures() {
        // Allocate a closure with heap captures and verify cleanup
        unsafe {
            let func_ptr = 0x1234 as *const u8;
            let closure = Closure::alloc(func_ptr, 2);

            // Allocate heap captures (simulating what codegen does)
            let slot0 = vole_heap_alloc(8);
            *(slot0 as *mut i64) = 42;
            Closure::set_capture(closure, 0, slot0);
            Closure::set_capture_kind(closure, 0, CAPTURE_KIND_VALUE);

            let slot1 = vole_heap_alloc(8);
            *(slot1 as *mut i64) = 100;
            Closure::set_capture(closure, 1, slot1);
            Closure::set_capture_kind(closure, 1, CAPTURE_KIND_VALUE);

            // Free should call closure_drop which frees the heap slots
            Closure::free(closure);
            // If this didn't crash, the heap slots were freed correctly
        }
    }

    #[test]
    fn test_closure_drop_with_rc_capture() {
        // Test that closure_drop correctly rc_decs RC captures
        static DEC_COUNT: AtomicU32 = AtomicU32::new(0);

        unsafe extern "C" fn test_drop(ptr: *mut u8) {
            DEC_COUNT.fetch_add(1, Ordering::SeqCst);
            let layout = Layout::new::<RcHeader>();
            unsafe { dealloc(ptr, layout) };
        }

        unsafe {
            // Create a fake RC object
            let rc_layout = Layout::new::<RcHeader>();
            let rc_ptr = alloc(rc_layout);
            ptr::write(
                rc_ptr as *mut RcHeader,
                RcHeader::with_drop_fn(crate::value::TYPE_STRING, test_drop),
            );
            // Give it refcount 2 so the first dec doesn't free it
            (*(rc_ptr as *mut RcHeader)).inc();

            DEC_COUNT.store(0, Ordering::SeqCst);

            let func_ptr = 0x1234 as *const u8;
            let closure = Closure::alloc(func_ptr, 1);

            // Heap-allocate a capture slot holding the RC pointer
            let slot = vole_heap_alloc(8);
            *(slot as *mut *mut u8) = rc_ptr;
            Closure::set_capture(closure, 0, slot);
            Closure::set_capture_kind(closure, 0, CAPTURE_KIND_RC);

            // Free closure — should rc_dec the RC object
            Closure::free(closure);

            // The RC object should have been dec'd (2 -> 1)
            let header = &*(rc_ptr as *const RcHeader);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);

            // Now dec it to zero to trigger test_drop cleanup
            rc_dec(rc_ptr);
            assert_eq!(DEC_COUNT.load(Ordering::SeqCst), 1);
        }
    }

    #[test]
    fn test_closure_layout_alignment() {
        // Verify layout calculations for various capture counts
        for n in 0..=17 {
            let layout = Closure::layout(n);
            assert!(layout.align() >= 8, "alignment must be >= 8");
            // Total size must fit: fixed + kinds_padded + captures
            let expected_kinds = align_to_ptr(n);
            let expected = Closure::FIXED_SIZE + expected_kinds + n * 8;
            assert_eq!(layout.size(), expected, "layout size for {} captures", n);
        }
    }

    #[test]
    fn test_rc_header_size() {
        // Closure's fixed size includes RcHeader (16) + func_ptr (8) + num_captures (8) = 32
        assert_eq!(Closure::FIXED_SIZE, 32);
    }
}
