//! Iterator combinators: chain, flatten, flat_map.

use crate::array::RcArray;
use crate::closure::Closure;
use crate::value::{RuntimeTypeId, rc_inc, tag_needs_rc};
use std::ptr;

use super::lifecycle::vole_array_iter;
use super::types::*;
use super::{iter_produces_owned, vole_array_iter_next};

// =============================================================================
// ChainIterator - lazy concatenation of two iterators
// =============================================================================

/// Create a new chain iterator that yields elements from first, then second
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_chain_iter(
    first: *mut RcIterator,
    second: *mut RcIterator,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Chain,
        IteratorSource {
            chain: ChainSource {
                first,
                second,
                on_second: false, // Start with first iterator
            },
        },
    )
}

iter_next_fn!(
    /// Get next value from chain iterator.
    /// First exhausts the first iterator, then yields from the second.
    /// Returns 1 and stores value in out_value if available.
    /// Returns 0 if both iterators exhausted (Done).
    vole_chain_iter_next, Chain, chain, mut |src, _iter, out| {
        // If we're still on the first iterator
        if !src.on_second {
            let has_value = vole_array_iter_next(src.first, out);
            if has_value != 0 {
                return 1; // Got value from first
            }
            // First exhausted, switch to second
            src.on_second = true;
        }

        // Now try the second iterator
        vole_array_iter_next(src.second, out)
    }
);

/// Collect all remaining chain iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_chain_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_chain_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: 0,
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}

// =============================================================================
// FlattenIterator - lazy flattening of nested iterables
// =============================================================================

/// Create a new flatten iterator wrapping any source iterator that yields arrays
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_flatten_iter(source: *mut RcIterator) -> *mut RcIterator {
    // Determine the inner element tag for the flattened output.
    // When the source is a Chunks or Windows iterator, use inner_elem_tag
    // (the element type of the sub-arrays, e.g. RuntimeTypeId::F64 for [f64] chunks).
    // This is critical because codegen may set elem_tag to RuntimeTypeId::Array
    // (the outer element type) on the flatten iterator, but flatten actually
    // yields individual elements from the inner arrays.
    let inner_tag = if !source.is_null() {
        let kind = unsafe { (*source).iter.kind };
        match kind {
            IteratorKind::Chunks => unsafe { (*source).iter.source.chunks.inner_elem_tag },
            IteratorKind::Windows => unsafe { (*source).iter.source.windows.inner_elem_tag },
            _ => 0, // For other sources, let codegen set it
        }
    } else {
        0
    };
    RcIterator::new_with_tag(
        IteratorKind::Flatten,
        IteratorSource {
            flatten: FlattenSource {
                outer: source,
                inner: ptr::null_mut(),
            },
        },
        inner_tag,
    )
}

iter_next_fn!(
    /// Get next value from flatten iterator.
    /// Yields elements from each inner array until all are exhausted.
    /// Returns 1 and stores value in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_flatten_iter_next, Flatten, flatten, mut |src, _iter, out| {
        // Check if the outer iterator produces owned arrays (e.g. from chunks/windows).
        // If so, we must dec_ref each array after wrapping it in an inner iterator,
        // because vole_array_iter inc_ref's the array.
        let outer_owns_arrays = iter_produces_owned(src.outer);

        loop {
            // If we have an inner iterator, try to get the next value from it
            if !src.inner.is_null() {
                let mut value: i64 = 0;
                let has_value = vole_array_iter_next(src.inner, &mut value);
                if has_value != 0 {
                    unsafe { *out = value };
                    return 1;
                }
                // Inner iterator exhausted, free it and get next outer element
                // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
                unsafe { RcIterator::dec_ref(src.inner); }
                src.inner = ptr::null_mut();
            }

            // Get next array from outer iterator
            let mut array_ptr: i64 = 0;
            let has_array = vole_array_iter_next(src.outer, &mut array_ptr);
            if has_array == 0 {
                return 0; // Outer iterator exhausted
            }

            // Create an iterator for the inner array
            let inner_array = array_ptr as *const RcArray;
            src.inner = vole_array_iter(inner_array);
            // vole_array_iter inc_ref'd the array. If the outer iterator produced
            // an owned array (e.g. from chunks/windows), dec_ref to transfer sole
            // ownership to the inner iterator.
            if outer_owns_arrays {
                unsafe { RcArray::dec_ref(inner_array as *mut RcArray) };
            }
            // Continue loop to get first element from this inner iterator
        }
    }
);

/// Collect all remaining flatten iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_flatten_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    // Determine the inner element type tag. The flatten iterator's elem_tag
    // may be RuntimeTypeId::Array (incorrectly set by codegen for the pre-flatten type).
    // When the outer source is Chunks or Windows, use inner_elem_tag.
    // Otherwise, fall back to the iterator's stored elem_tag.
    let elem_tag = unsafe {
        let outer = (*iter).iter.source.flatten.outer;
        if !outer.is_null() {
            let outer_kind = (*outer).iter.kind;
            match outer_kind {
                IteratorKind::Chunks => (*outer).iter.source.chunks.inner_elem_tag,
                IteratorKind::Windows => (*outer).iter.source.windows.inner_elem_tag,
                _ => {
                    let tag = (*iter).elem_tag;
                    // If the codegen-set tag is RuntimeTypeId::Array but we're flattening,
                    // the actual elements aren't arrays - use 0 (i64) as fallback
                    if tag == RuntimeTypeId::Array as u64 {
                        0
                    } else {
                        tag
                    }
                }
            }
        } else {
            (*iter).elem_tag
        }
    };

    let needs_rc = tag_needs_rc(elem_tag);

    loop {
        let mut value: i64 = 0;
        let has_value = vole_flatten_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Flatten yields borrowed values (owned: false).  For RC types,
        // rc_inc so the collected array owns its references.
        if needs_rc && value != 0 {
            rc_inc(value as *mut u8);
        }

        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: elem_tag,
                    value: value as u64,
                },
            );
        }
    }

    // Free the flatten iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}

// =============================================================================
// FlatMapIterator - lazy map then flatten
// =============================================================================

/// Create a new flat_map iterator wrapping any source iterator
/// Takes a transform function that returns an array
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_flat_map_iter(
    source: *mut RcIterator,
    transform: *const Closure,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::FlatMap,
        IteratorSource {
            flat_map: FlatMapSource {
                source,
                transform,
                inner: ptr::null_mut(),
            },
        },
    )
}

iter_next_fn!(
    /// Get next value from flat_map iterator.
    /// Applies transform to each source element, then yields elements from resulting arrays.
    /// Returns 1 and stores value in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_flat_map_iter_next, FlatMap, flat_map, mut |src, _iter, out| {
        loop {
            // If we have an inner iterator, try to get the next value from it
            if !src.inner.is_null() {
                let mut value: i64 = 0;
                let has_value = vole_array_iter_next(src.inner, &mut value);
                if has_value != 0 {
                    unsafe { *out = value };
                    return 1;
                }
                // Inner iterator exhausted, free it and get next source element
                // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
                unsafe { RcIterator::dec_ref(src.inner); }
                src.inner = ptr::null_mut();
            }

            // Get next value from source iterator
            let mut source_value: i64 = 0;
            let has_source = vole_array_iter_next(src.source, &mut source_value);
            if has_source == 0 {
                return 0; // Source iterator exhausted
            }

            // Apply transform function to get an array
            let array_ptr: i64 = unsafe {
                let func_ptr = Closure::get_func(src.transform);
                let transform_fn: extern "C" fn(*const Closure, i64) -> i64 =
                    std::mem::transmute(func_ptr);
                transform_fn(src.transform, source_value)
            };

            // Create an iterator for the resulting array.
            // vole_array_iter rc_inc's the array (for user arrays).
            // The transform created this array (refcount 1), so dec_ref after wrapping
            // to transfer sole ownership to the inner iterator.
            let inner_array = array_ptr as *mut RcArray;
            src.inner = vole_array_iter(inner_array);
            unsafe { RcArray::dec_ref(inner_array) };
            // Continue loop to get first element from this inner iterator
        }
    }
);

/// Collect all remaining flat_map iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_flat_map_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_flat_map_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: 0,
                    value: value as u64,
                },
            );
        }
    }

    // Free the flat_map iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}
