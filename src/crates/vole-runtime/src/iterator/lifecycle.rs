//! Iterator lifecycle management: allocation, reference counting, drop.

use crate::alloc_track;
use crate::array::RcArray;
use crate::closure::Closure;
use crate::string::RcString;
use crate::value::{RcHeader, RuntimeTypeId, rc_dec, rc_inc};
use std::alloc::{Layout, dealloc};
use std::ptr;

use super::types::*;

impl RcIterator {
    /// Allocate a new RcIterator with the given kind and source (elem_tag defaults to 0/i64)
    pub fn new(kind: IteratorKind, source: IteratorSource) -> *mut Self {
        Self::new_with_tag(kind, source, 0)
    }

    /// Allocate a new RcIterator with the given kind, source, and element type tag
    pub fn new_with_tag(kind: IteratorKind, source: IteratorSource, elem_tag: u64) -> *mut Self {
        let layout = Layout::new::<RcIterator>();
        unsafe {
            let ptr = std::alloc::alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(RuntimeTypeId::Iterator as u32, iterator_drop),
            );
            ptr::write(&mut (*ptr).iter.kind, kind);
            ptr::write(&mut (*ptr).iter.source, source);
            ptr::write(&mut (*ptr).elem_tag, elem_tag);
            ptr::write(&mut (*ptr).produces_owned, false);
            alloc_track::track_alloc(RuntimeTypeId::Iterator as u32);
            ptr
        }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcIterator`
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        rc_inc(ptr as *mut u8);
    }

    /// Decrement reference count and free if zero (via unified rc_dec + drop_fn)
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcIterator`.
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }

    /// Set the element type tag on this iterator (non-recursive).
    /// Each iterator in the chain stores its OWN element type tag.
    /// The tag represents the type of values this iterator produces.
    #[expect(clippy::not_unsafe_ptr_arg_deref)]
    pub fn set_elem_tag(ptr: *mut Self, tag: u64) {
        if ptr.is_null() {
            return;
        }
        unsafe {
            (*ptr).elem_tag = tag;
        }
    }
}

/// Set the element type tag on an iterator chain.
/// Called from codegen to enable RC tracking in the iterator pipeline.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_set_elem_tag(iter: *mut RcIterator, tag: u64) {
    RcIterator::set_elem_tag(iter, tag);
}

/// Mark an iterator as producing owned values (e.g. generators).
///
/// # Safety
/// `iter` must be null or a valid pointer to an initialized `RcIterator`.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_iter_set_produces_owned(iter: *mut RcIterator) {
    if !iter.is_null() {
        unsafe {
            (*iter).produces_owned = true;
        }
    }
}

/// Create a new array iterator
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter(array: *const RcArray) -> *mut RcIterator {
    // Increment ref count on array so it stays alive while iterator exists
    unsafe {
        if !array.is_null() {
            RcArray::inc_ref(array as *mut RcArray);
        }
    }

    RcIterator::new(
        IteratorKind::Array,
        IteratorSource {
            array: ArraySource { array, index: 0 },
        },
    )
}

/// Create an interface iterator wrapper from a boxed interface implementing Iterator.
/// The boxed_interface has layout: [data_ptr, vtable_ptr].
/// Returns pointer to heap-allocated iterator.
#[unsafe(no_mangle)]
pub extern "C" fn vole_interface_iter(boxed_interface: *const u8) -> *mut RcIterator {
    // rc_inc the data_ptr so the iterator owns its own reference.
    // The JIT scope cleanup will independently rc_dec via the boxed interface,
    // so both sides need their own reference.
    if !boxed_interface.is_null() {
        unsafe {
            let data_ptr = *(boxed_interface as *const *mut u8);
            if !data_ptr.is_null() {
                rc_inc(data_ptr);
            }
        }
    }
    let iter = RcIterator::new(
        IteratorKind::Interface,
        IteratorSource {
            interface: InterfaceSource { boxed_interface },
        },
    );
    // Interface iterators produce owned values: next() is a function call
    // that returns a fresh value (generators, or classes returning owned values).
    if !iter.is_null() {
        unsafe {
            (*iter).produces_owned = true;
        }
    }
    iter
}

/// Create an RcIterator adapter for an interface with a known element type tag.
/// Used when the element type is known at compile time (e.g. vtable thunks for
/// Iterator<string>).
#[unsafe(no_mangle)]
pub extern "C" fn vole_interface_iter_tagged(
    boxed_interface: *const u8,
    elem_tag: u64,
) -> *mut RcIterator {
    // rc_inc the data_ptr so the iterator owns its own reference.
    if !boxed_interface.is_null() {
        unsafe {
            let data_ptr = *(boxed_interface as *const *mut u8);
            if !data_ptr.is_null() {
                rc_inc(data_ptr);
            }
        }
    }
    let iter = RcIterator::new_with_tag(
        IteratorKind::Interface,
        IteratorSource {
            interface: InterfaceSource { boxed_interface },
        },
        elem_tag,
    );
    if !iter.is_null() {
        unsafe {
            (*iter).produces_owned = true;
        }
    }
    iter
}

/// Drop function for RcIterator, called by rc_dec when refcount reaches zero.
///
/// Handles all iterator kinds and recursively decrements nested source iterators.
/// Closures (for Map, Filter, FlatMap, FromFn) are freed here since the iterator
/// takes ownership of the closure reference passed by the caller.
///
/// # Safety
/// `ptr` must point to a valid `RcIterator` allocation.
unsafe extern "C" fn iterator_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(RuntimeTypeId::Iterator as u32);
    unsafe {
        let rc_iter = ptr as *mut RcIterator;
        let iter_ref = &(*rc_iter).iter;
        iterator_drop_sources(iter_ref);
        let layout = Layout::new::<RcIterator>();
        dealloc(ptr, layout);
    }
}

// Generate iterator_drop_sources from the central definition
for_all_iterator_kinds!(generate_drop_sources);

iter_next_fn!(
    /// Get next value from interface iterator by calling through the vtable.
    /// The boxed interface has layout: [data_ptr, vtable_ptr]
    /// The vtable has method pointers, with next() at slot 0.
    /// The next() wrapper returns a tagged union pointer.
    /// Union variants are sorted descending: Primitive(T) > Done, so tag 0 = value, tag 1 = Done.
    vole_interface_iter_next, Interface, interface, |src, _iter, out| {
        let boxed = src.boxed_interface;
        if boxed.is_null() {
            return 0;
        }

        unsafe {
            // Load vtable pointer from the boxed interface (layout: [data_ptr, vtable_ptr])
            let vtable_ptr = *((boxed as *const i64).add(1));

            // Get the next() method pointer from vtable slot 0
            let next_fn_ptr = *(vtable_ptr as *const usize);

            // Call the next() wrapper: fn(box_ptr) -> tagged_union_ptr
            // The wrapper expects the full boxed interface pointer so it can extract data_ptr
            let next_fn: extern "C" fn(i64) -> *mut u8 = std::mem::transmute(next_fn_ptr);
            let result_ptr = next_fn(boxed as i64);

            // Parse the tagged union result
            // Layout: [tag:1][pad:7][payload:8]
            // Tag 0 = value, Tag 1 = Done (descending sort order)
            let tag = *result_ptr;
            if tag == 1 {
                // Done - no more values
                0
            } else {
                // Has value - extract payload
                let payload = *(result_ptr.add(8) as *const i64);
                *out = payload;
                1
            }
        }
    }
);
