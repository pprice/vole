//! Iterator runtime support
//!
//! Provides runtime representation for iterators.
//! Uses a unified IteratorSource enum to support chaining (e.g., map().map()).

use crate::runtime::array::RcArray;
use crate::runtime::closure::Closure;

/// Enum discriminant for iterator sources
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IteratorKind {
    Array = 0,
    Map = 1,
    Filter = 2,
    Take = 3,
    Skip = 4,
}

/// Unified iterator source - can be either an array, map, filter, take, or skip iterator
/// This allows chaining (e.g., arr.iter().map(f).filter(p).take(5))
#[repr(C)]
pub union IteratorSource {
    pub array: ArraySource,
    pub map: MapSource,
    pub filter: FilterSource,
    pub take: TakeSource,
    pub skip: SkipSource,
}

/// Source data for array iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ArraySource {
    pub array: *const RcArray,
    pub index: i64,
}

/// Source data for map iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct MapSource {
    /// Pointer to source iterator (could be ArrayIterator or another MapIterator)
    pub source: *mut UnifiedIterator,
    /// Transform closure
    pub transform: *const Closure,
}

/// Source data for filter iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FilterSource {
    /// Pointer to source iterator (could be any iterator type)
    pub source: *mut UnifiedIterator,
    /// Predicate closure that returns bool
    pub predicate: *const Closure,
}

/// Source data for take iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct TakeSource {
    /// Pointer to source iterator (could be any iterator type)
    pub source: *mut UnifiedIterator,
    /// Number of elements remaining to take
    pub remaining: i64,
}

/// Source data for skip iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SkipSource {
    /// Pointer to source iterator (could be any iterator type)
    pub source: *mut UnifiedIterator,
    /// Number of elements to skip
    pub skip_count: i64,
    /// Whether we've done the initial skip (0 = not skipped, 1 = skipped)
    pub skipped: i64,
}

/// Unified iterator structure
/// The kind field tells us which variant is active
#[repr(C)]
pub struct UnifiedIterator {
    pub kind: IteratorKind,
    pub source: IteratorSource,
}

// Legacy type aliases for backwards compatibility
pub type ArrayIterator = UnifiedIterator;
pub type MapIterator = UnifiedIterator;
pub type FilterIterator = UnifiedIterator;
pub type TakeIterator = UnifiedIterator;
pub type SkipIterator = UnifiedIterator;

/// Create a new array iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter(array: *const RcArray) -> *mut UnifiedIterator {
    // Increment ref count on array so it stays alive while iterator exists
    unsafe {
        if !array.is_null() {
            RcArray::inc_ref(array as *mut RcArray);
        }
    }

    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Array,
        source: IteratorSource {
            array: ArraySource { array, index: 0 },
        },
    });
    Box::into_raw(iter)
}

/// Free an array iterator
///
/// TODO: Iterator cleanup is currently deferred. When Vole adds drop semantics,
/// iterators should call vole_array_iter_free when they go out of scope.
/// For now, iterators leak - this is acceptable for short-lived test programs.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_free(iter: *mut UnifiedIterator) {
    if iter.is_null() {
        return;
    }

    unsafe {
        let iter_ref = &*iter;
        if iter_ref.kind == IteratorKind::Array {
            // Decrement ref count on array
            let array = iter_ref.source.array.array;
            if !array.is_null() {
                RcArray::dec_ref(array as *mut RcArray);
            }
        }
        // For map iterators, we'd need to recursively free the source
        // This is deferred until we have proper cleanup semantics

        // Free the iterator
        drop(Box::from_raw(iter));
    }
}

/// Get next value from any iterator (array or map)
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    match iter_ref.kind {
        IteratorKind::Array => {
            let src = unsafe { &mut iter_ref.source.array };
            if src.index >= unsafe { (*src.array).len } as i64 {
                return 0; // Done
            }
            let tagged_value = unsafe {
                let data = (*src.array).data;
                *data.add(src.index as usize)
            };
            // Store the value part (ignoring tag for now - iterators return element type)
            unsafe { *out_value = tagged_value.value as i64 };
            src.index += 1;
            1 // Has value
        }
        IteratorKind::Map => {
            // For map iterators, delegate to map_next logic
            vole_map_iter_next(iter, out_value)
        }
        IteratorKind::Filter => {
            // For filter iterators, delegate to filter_next logic
            vole_filter_iter_next(iter, out_value)
        }
        IteratorKind::Take => {
            // For take iterators, delegate to take_next logic
            vole_take_iter_next(iter, out_value)
        }
        IteratorKind::Skip => {
            // For skip iterators, delegate to skip_next logic
            vole_skip_iter_next(iter, out_value)
        }
    }
}

/// Collect all remaining iterator values into a new array
/// Returns pointer to newly allocated array (empty if iterator is null)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Push to result array with value
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: 0, // i64 type
                    value: value as u64,
                },
            );
        }
    }

    result
}

// =============================================================================
// MapIterator - lazy transformation over any iterator
// =============================================================================

/// Create a new map iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_map_iter(
    source: *mut UnifiedIterator,
    transform: *const Closure,
) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Map,
        source: IteratorSource {
            map: MapSource { source, transform },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from map iterator
/// Calls the source iterator's next, applies the transform function, returns result
/// Returns 1 and stores transformed value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_map_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &*iter };

    // This function should only be called for Map iterators
    // but vole_array_iter_next delegates here for Map kind
    if iter_ref.kind != IteratorKind::Map {
        return 0;
    }

    let map_src = unsafe { iter_ref.source.map };

    // Get next value from source iterator (could be Array or Map)
    let mut source_value: i64 = 0;
    let has_value = vole_array_iter_next(map_src.source, &mut source_value);

    if has_value == 0 {
        return 0; // Done
    }

    // Apply transform function
    // Check if this is a closure (has captures) or a pure function (no captures)
    unsafe {
        let func_ptr = Closure::get_func(map_src.transform);
        let num_captures = (*map_src.transform).num_captures;

        let result = if num_captures == 0 {
            // Pure function - call with just the value
            let transform_fn: extern "C" fn(i64) -> i64 = std::mem::transmute(func_ptr);
            transform_fn(source_value)
        } else {
            // Closure - pass closure pointer as first arg
            let transform_fn: extern "C" fn(*const Closure, i64) -> i64 =
                std::mem::transmute(func_ptr);
            transform_fn(map_src.transform, source_value)
        };
        *out_value = result;
    }

    1 // Has value
}

/// Collect all remaining map iterator values into a new array
/// Returns pointer to newly allocated array
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_map_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

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

    result
}

// =============================================================================
// FilterIterator - lazy filtering over any iterator
// =============================================================================

/// Create a new filter iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_filter_iter(
    source: *mut UnifiedIterator,
    predicate: *const Closure,
) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Filter,
        source: IteratorSource {
            filter: FilterSource { source, predicate },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from filter iterator
/// Calls the source iterator's next, applies the predicate function, skips non-matching elements
/// Returns 1 and stores value in out_value if a matching element is found
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_filter_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &*iter };

    // This function should only be called for Filter iterators
    if iter_ref.kind != IteratorKind::Filter {
        return 0;
    }

    let filter_src = unsafe { iter_ref.source.filter };

    // Keep getting values from source until we find one that passes the predicate
    loop {
        // Get next value from source iterator (could be Array, Map, or Filter)
        let mut source_value: i64 = 0;
        let has_value = vole_array_iter_next(filter_src.source, &mut source_value);

        if has_value == 0 {
            return 0; // Done - source exhausted
        }

        // Apply predicate function
        // Check if this is a closure (has captures) or a pure function (no captures)
        // Note: Vole bools are i8, so predicate returns i8 (0 or 1)
        let passes: i8 = unsafe {
            let func_ptr = Closure::get_func(filter_src.predicate);
            let num_captures = (*filter_src.predicate).num_captures;

            if num_captures == 0 {
                // Pure function - call with just the value
                let predicate_fn: extern "C" fn(i64) -> i8 = std::mem::transmute(func_ptr);
                predicate_fn(source_value)
            } else {
                // Closure - pass closure pointer as first arg
                let predicate_fn: extern "C" fn(*const Closure, i64) -> i8 =
                    std::mem::transmute(func_ptr);
                predicate_fn(filter_src.predicate, source_value)
            }
        };

        // If predicate returns non-zero (true), yield this value
        if passes != 0 {
            unsafe { *out_value = source_value };
            return 1; // Has value
        }
        // Otherwise, continue to next element
    }
}

/// Collect all remaining filter iterator values into a new array
/// Returns pointer to newly allocated array
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_filter_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

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

    result
}

// =============================================================================
// Consumer methods - eager evaluation that consumes the entire iterator
// =============================================================================

/// Count the number of elements in any iterator
/// Returns the count as i64
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_count(iter: *mut UnifiedIterator) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let mut count: i64 = 0;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }
        count += 1;
    }

    count
}

/// Sum all elements in any iterator (assumes i64 elements)
/// Returns the sum as i64
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_sum(iter: *mut UnifiedIterator) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let mut sum: i64 = 0;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }
        sum += value;
    }

    sum
}

/// Call a function for each element in any iterator
/// The callback is a closure that takes one i64 argument and returns nothing
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_for_each(iter: *mut UnifiedIterator, callback: *const Closure) {
    if iter.is_null() || callback.is_null() {
        return;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Call the callback closure with the value
        unsafe {
            let func_ptr = Closure::get_func(callback);
            let num_captures = (*callback).num_captures;

            if num_captures == 0 {
                // Pure function - call with just the value
                let callback_fn: extern "C" fn(i64) = std::mem::transmute(func_ptr);
                callback_fn(value);
            } else {
                // Closure - pass closure pointer as first arg
                let callback_fn: extern "C" fn(*const Closure, i64) = std::mem::transmute(func_ptr);
                callback_fn(callback, value);
            }
        }
    }
}

/// Reduce all elements in any iterator using an accumulator function
/// Takes initial value and a reducer closure (acc, value) -> new_acc
/// Returns the final accumulated value
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_reduce(
    iter: *mut UnifiedIterator,
    init: i64,
    reducer: *const Closure,
) -> i64 {
    if iter.is_null() || reducer.is_null() {
        return init;
    }

    let mut acc = init;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Call the reducer closure with (acc, value) -> new_acc
        unsafe {
            let func_ptr = Closure::get_func(reducer);
            let num_captures = (*reducer).num_captures;

            acc = if num_captures == 0 {
                // Pure function - call with (acc, value)
                let reducer_fn: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(func_ptr);
                reducer_fn(acc, value)
            } else {
                // Closure - pass closure pointer as first arg, then (acc, value)
                let reducer_fn: extern "C" fn(*const Closure, i64, i64) -> i64 =
                    std::mem::transmute(func_ptr);
                reducer_fn(reducer, acc, value)
            };
        }
    }

    acc
}

// =============================================================================
// TakeIterator - lazy take of first n elements
// =============================================================================

/// Create a new take iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_take_iter(source: *mut UnifiedIterator, count: i64) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Take,
        source: IteratorSource {
            take: TakeSource {
                source,
                remaining: count,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from take iterator
/// Returns 1 and stores value in out_value if available (and remaining > 0)
/// Returns 0 if remaining is 0 or source iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_take_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    // This function should only be called for Take iterators
    if iter_ref.kind != IteratorKind::Take {
        return 0;
    }

    let take_src = unsafe { &mut iter_ref.source.take };

    // If we've taken enough elements, return Done
    if take_src.remaining <= 0 {
        return 0;
    }

    // Get next value from source iterator
    let mut source_value: i64 = 0;
    let has_value = vole_array_iter_next(take_src.source, &mut source_value);

    if has_value == 0 {
        return 0; // Source exhausted
    }

    // Decrement remaining count
    take_src.remaining -= 1;

    unsafe { *out_value = source_value };
    1 // Has value
}

/// Collect all remaining take iterator values into a new array
/// Returns pointer to newly allocated array
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_take_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

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

    result
}

// =============================================================================
// SkipIterator - lazy skip of first n elements
// =============================================================================

/// Create a new skip iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_skip_iter(source: *mut UnifiedIterator, count: i64) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Skip,
        source: IteratorSource {
            skip: SkipSource {
                source,
                skip_count: count,
                skipped: 0, // Not yet skipped
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from skip iterator
/// On first call, skips skip_count elements, then returns remaining elements
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_skip_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    // This function should only be called for Skip iterators
    if iter_ref.kind != IteratorKind::Skip {
        return 0;
    }

    let skip_src = unsafe { &mut iter_ref.source.skip };

    // If we haven't skipped yet, do the initial skip
    if skip_src.skipped == 0 {
        skip_src.skipped = 1;
        let mut skipped: i64 = 0;
        while skipped < skip_src.skip_count {
            let mut dummy: i64 = 0;
            let has_value = vole_array_iter_next(skip_src.source, &mut dummy);
            if has_value == 0 {
                // Source exhausted during skip
                return 0;
            }
            skipped += 1;
        }
    }

    // Now just pass through from source
    vole_array_iter_next(skip_src.source, out_value)
}

/// Collect all remaining skip iterator values into a new array
/// Returns pointer to newly allocated array
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_skip_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

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

    result
}
