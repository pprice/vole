//! Collecting operations: reverse, sorted, unique.

use super::lifecycle::vole_array_iter;
use super::types::*;
use super::vole_array_iter_next;
use crate::array::RcArray;

// =============================================================================
// Collecting operations: reverse, sorted, unique
// =============================================================================

/// Reverse iterator - collects all elements, reverses them, returns new array iterator
/// This is an eager operation that consumes the entire source iterator.
/// Frees the source iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_reverse_iter(iter: *mut RcIterator) -> *mut RcIterator {
    use crate::value::TaggedValue;

    if iter.is_null() {
        // Return empty array iterator
        let empty = RcArray::new();
        return vole_array_iter(empty);
    }

    // Collect all values into a vector
    let mut values: Vec<i64> = Vec::new();
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);
        if has_value == 0 {
            break;
        }
        values.push(value);
    }

    // Free the source iterator
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // Create new array with reversed values
    let result = RcArray::new();
    for value in values.into_iter().rev() {
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

    // Return iterator over the reversed array.
    // vole_array_iter rc_inc's the array (for user arrays that must outlive the iterator).
    // Since we own this intermediate array, dec_ref to transfer sole ownership to the iterator.
    let iter = vole_array_iter(result);
    unsafe { RcArray::dec_ref(result) };
    iter
}

/// Sorted iterator - collects all elements, sorts them, returns new array iterator
/// This is an eager operation that consumes the entire source iterator.
/// Sorts i64 values in ascending order.
/// Frees the source iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_sorted_iter(iter: *mut RcIterator) -> *mut RcIterator {
    use crate::value::TaggedValue;

    if iter.is_null() {
        // Return empty array iterator
        let empty = RcArray::new();
        return vole_array_iter(empty);
    }

    // Collect all values into a vector
    let mut values: Vec<i64> = Vec::new();
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);
        if has_value == 0 {
            break;
        }
        values.push(value);
    }

    // Free the source iterator
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // Sort the values
    values.sort();

    // Create new array with sorted values
    let result = RcArray::new();
    for value in values {
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

    // Return iterator over the sorted array.
    // vole_array_iter rc_inc's the array (for user arrays that must outlive the iterator).
    // Since we own this intermediate array, dec_ref to transfer sole ownership to the iterator.
    let iter = vole_array_iter(result);
    unsafe { RcArray::dec_ref(result) };
    iter
}

/// Create a new unique iterator wrapping any source iterator
/// Filters consecutive duplicates (like Unix uniq)
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_unique_iter(source: *mut RcIterator) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Unique,
        IteratorSource {
            unique: UniqueSource {
                source,
                prev: 0,
                has_prev: false,
            },
        },
    )
}

iter_next_fn!(
    /// Get next value from unique iterator.
    /// Skips consecutive duplicate values.
    /// Returns 1 and stores value in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_unique_iter_next, Unique, unique, mut |src, _iter, out| {
        loop {
            // Get next value from source iterator
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(src.source, &mut value);

            if has_value == 0 {
                return 0; // Source exhausted
            }

            // If this is the first element, always yield it
            if !src.has_prev {
                src.has_prev = true;
                src.prev = value;
                unsafe { *out = value };
                return 1;
            }

            // If value differs from previous, yield it
            if value != src.prev {
                src.prev = value;
                unsafe { *out = value };
                return 1;
            }
            // Otherwise, skip this duplicate and continue
        }
    }
);
