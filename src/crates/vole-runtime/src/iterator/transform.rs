//! Lazy transform iterators: map, filter, filter_map, take, skip.

use crate::array::RcArray;
use crate::closure::Closure;
use crate::value::{rc_dec, tag_needs_rc};

use super::consumers::iter_produces_owned_rc;
use super::types::*;
use super::{iter_produces_owned, vole_array_iter_next};

// =============================================================================
// MapIterator - lazy transformation over any iterator
// =============================================================================

/// Create a new map iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_map_iter(
    source: *mut RcIterator,
    transform: *const Closure,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Map,
        IteratorSource {
            map: MapSource { source, transform },
        },
    )
}

iter_next_fn!(
    /// Get next value from map iterator.
    /// Calls the source iterator's next, applies the transform function, returns result.
    /// Returns 1 and stores transformed value in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_map_iter_next, Map, map, |src, _iter, out| {
        // Check if source values are owned RC values that need rc_dec after consumption.
        // The source iterator's elem_tag tells us the type of values it produces.
        // If the source produces owned RC values (from another map, string_chars, etc.),
        // we need to rc_dec them after the transform closure consumes them.
        let source_elem_tag = unsafe { (*src.source).elem_tag };
        let source_needs_rc_dec =
            tag_needs_rc(source_elem_tag) && iter_produces_owned(src.source);

        // Get next value from source iterator (could be Array or Map)
        let mut source_value: i64 = 0;
        let has_value = vole_array_iter_next(src.source, &mut source_value);

        if has_value == 0 {
            return 0; // Done
        }

        // Apply transform function
        // All lambdas now use closure calling convention (closure ptr as first arg)
        unsafe {
            let func_ptr = Closure::get_func(src.transform);
            let transform_fn: extern "C" fn(*const Closure, i64) -> i64 =
                std::mem::transmute(func_ptr);
            let result = transform_fn(src.transform, source_value);
            *out = result;
        }

        // rc_dec the consumed source value if it was an owned RC value (from another map, etc.).
        // The closure has consumed the value (used it to produce the result).
        if source_needs_rc_dec && source_value != 0 {
            rc_dec(source_value as *mut u8);
        }

        1 // Has value
    }
);

/// Collect all remaining map iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_map_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_map_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Push to result array
        // Tag 0 = i64 type (for now, we'll handle other types later)
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
// FilterIterator - lazy filtering over any iterator
// =============================================================================

/// Create a new filter iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_filter_iter(
    source: *mut RcIterator,
    predicate: *const Closure,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Filter,
        IteratorSource {
            filter: FilterSource { source, predicate },
        },
    )
}

iter_next_fn!(
    /// Get next value from filter iterator.
    /// Calls the source iterator's next, applies the predicate function, skips non-matching elements.
    /// Returns 1 and stores value in out_value if a matching element is found.
    /// Returns 0 if iterator exhausted (Done).
    vole_filter_iter_next, Filter, filter, |src, iter, out| {
        // Check if rejected values need rc_dec (source produces owned RC values)
        let elem_tag = unsafe { (*iter).elem_tag };
        let rc_dec_rejects =
            tag_needs_rc(elem_tag) && iter_produces_owned(src.source);

        // Keep getting values from source until we find one that passes the predicate
        loop {
            // Get next value from source iterator (could be Array, Map, or Filter)
            let mut source_value: i64 = 0;
            let has_value = vole_array_iter_next(src.source, &mut source_value);

            if has_value == 0 {
                return 0; // Done - source exhausted
            }

            // Apply predicate function
            // Check if this is a closure (has captures) or a pure function (no captures)
            // Note: Vole bools are i8, so predicate returns i8 (0 or 1)
            // All lambdas now use closure calling convention (closure ptr as first arg)
            let passes: i8 = unsafe {
                let func_ptr = Closure::get_func(src.predicate);
                let predicate_fn: extern "C" fn(*const Closure, i64) -> i8 =
                    std::mem::transmute(func_ptr);
                predicate_fn(src.predicate, source_value)
            };

            // If predicate returns non-zero (true), yield this value
            if passes != 0 {
                unsafe { *out = source_value };
                return 1; // Has value
            }
            // Rejected value: rc_dec if it's an owned RC value (from map/etc.)
            if rc_dec_rejects && source_value != 0 {
                rc_dec(source_value as *mut u8);
            }
        }
    }
);

/// Collect all remaining filter iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_filter_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_filter_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Push to result array
        // Tag 0 = i64 type (for now, we'll handle other types later)
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
// TakeIterator - lazy take of first n elements
// =============================================================================

/// Create a new take iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_take_iter(source: *mut RcIterator, count: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Take,
        IteratorSource {
            take: TakeSource {
                source,
                remaining: count,
            },
        },
    )
}

iter_next_fn!(
    /// Get next value from take iterator.
    /// Returns 1 and stores value in out_value if available (and remaining > 0).
    /// Returns 0 if remaining is 0 or source iterator exhausted (Done).
    vole_take_iter_next, Take, take, mut |src, _iter, out| {
        // If we've taken enough elements, return Done
        if src.remaining <= 0 {
            return 0;
        }

        // Get next value from source iterator
        let mut source_value: i64 = 0;
        let has_value = vole_array_iter_next(src.source, &mut source_value);

        if has_value == 0 {
            return 0; // Source exhausted
        }

        // Decrement remaining count
        src.remaining -= 1;

        unsafe { *out = source_value };
        1 // Has value
    }
);

/// Collect all remaining take iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_take_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_take_iter_next(iter, &mut value);

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
// SkipIterator - lazy skip of first n elements
// =============================================================================

/// Create a new skip iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_skip_iter(source: *mut RcIterator, count: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Skip,
        IteratorSource {
            skip: SkipSource {
                source,
                skip_count: count,
                skipped: false, // Not yet skipped
            },
        },
    )
}

iter_next_fn!(
    /// Get next value from skip iterator.
    /// On first call, skips skip_count elements, then returns remaining elements.
    /// Returns 1 and stores value in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_skip_iter_next, Skip, skip, mut |src, _iter, out| {
        // If we haven't skipped yet, do the initial skip
        if !src.skipped {
            src.skipped = true;
            let owned_rc = iter_produces_owned_rc(src.source);
            let mut skipped: i64 = 0;
            while skipped < src.skip_count {
                let mut dummy: i64 = 0;
                let has_value = vole_array_iter_next(src.source, &mut dummy);
                if has_value == 0 {
                    // Source exhausted during skip
                    return 0;
                }
                // Free skipped owned RC values
                if owned_rc && dummy != 0 {
                    rc_dec(dummy as *mut u8);
                }
                skipped += 1;
            }
        }

        // Now just pass through from source
        vole_array_iter_next(src.source, out)
    }
);

/// Collect all remaining skip iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_skip_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_skip_iter_next(iter, &mut value);

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
// FilterMapIterator - lazy map + nil-filter in one pass
// =============================================================================

/// Create a new filter_map iterator wrapping any source iterator.
/// The transform closure returns T? (optional): nil values are skipped,
/// non-nil values are unwrapped and yielded.
/// Returns pointer to heap-allocated iterator.
#[unsafe(no_mangle)]
pub extern "C" fn vole_filter_map_iter(
    source: *mut RcIterator,
    transform: *const Closure,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::FilterMap,
        IteratorSource {
            filter_map: FilterMapSource { source, transform },
        },
    )
}

iter_next_fn!(
    /// Get next value from filter_map iterator.
    /// Calls the source iterator's next, applies the transform function which returns T?,
    /// skips nil results, and yields unwrapped non-nil values.
    /// The transform returns a pointer to [tag:1][pad:7][payload:8] where tag 0 = value, tag 1 = nil.
    /// Returns 1 and stores unwrapped value in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_filter_map_iter_next, FilterMap, filter_map, |src, _iter, out| {
        // Check if source values are owned RC values that need rc_dec after consumption.
        let source_elem_tag = unsafe { (*src.source).elem_tag };
        let source_needs_rc_dec =
            tag_needs_rc(source_elem_tag) && iter_produces_owned(src.source);

        loop {
            // Get next value from source iterator
            let mut source_value: i64 = 0;
            let has_value = vole_array_iter_next(src.source, &mut source_value);

            if has_value == 0 {
                return 0; // Done
            }

            // Apply transform function — returns pointer to optional [tag][pad][payload].
            // The pointer points to the closure's stack frame (NOT heap-allocated),
            // so we must NOT free it. We just read the tag and payload.
            let opt_ptr: *const u8 = unsafe {
                let func_ptr = Closure::get_func(src.transform);
                let transform_fn: extern "C" fn(*const Closure, i64) -> *const u8 =
                    std::mem::transmute(func_ptr);
                transform_fn(src.transform, source_value)
            };

            // rc_dec the consumed source value if it was an owned RC value
            if source_needs_rc_dec && source_value != 0 {
                rc_dec(source_value as *mut u8);
            }

            // Read tag from the optional result
            // tag 0 = value present, tag 1 = nil (sorted: I64 < Nil alphabetically)
            if opt_ptr.is_null() {
                continue; // treat null pointer as nil, skip
            }

            let tag = unsafe { *opt_ptr };
            if tag != 0 {
                // nil — skip this element
                continue;
            }

            // Non-nil: read the unwrapped payload value
            let payload = unsafe { *(opt_ptr.add(8) as *const i64) };

            unsafe { *out = payload };
            return 1; // Has value
        }
    }
);

/// Collect all remaining filter_map iterator values into a new array.
/// Returns pointer to newly allocated array.
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_filter_map_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_filter_map_iter_next(iter, &mut value);

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
