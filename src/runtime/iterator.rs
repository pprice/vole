//! Iterator runtime support
//!
//! Provides runtime representation for iterators.
//! Uses a unified IteratorSource enum to support chaining (e.g., map().map()).

use crate::runtime::array::RcArray;
use crate::runtime::closure::Closure;
use std::alloc::{Layout, alloc};

/// Enum discriminant for iterator sources
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IteratorKind {
    Array = 0,
    Map = 1,
    Filter = 2,
    Take = 3,
    Skip = 4,
    Chain = 5,
}

/// Unified iterator source - can be either an array, map, filter, take, skip, or chain iterator
/// This allows chaining (e.g., arr.iter().map(f).filter(p).take(5))
#[repr(C)]
pub union IteratorSource {
    pub array: ArraySource,
    pub map: MapSource,
    pub filter: FilterSource,
    pub take: TakeSource,
    pub skip: SkipSource,
    pub chain: ChainSource,
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

/// Source data for chain iteration (concatenates two iterators)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ChainSource {
    /// First iterator to consume
    pub first: *mut UnifiedIterator,
    /// Second iterator to consume after first is exhausted
    pub second: *mut UnifiedIterator,
    /// Whether we've exhausted the first iterator (0 = on first, 1 = on second)
    pub on_second: i64,
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
pub type ChainIterator = UnifiedIterator;

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

/// Free an iterator and its source chain recursively.
///
/// This function handles all iterator kinds (Array, Map, Filter, Take, Skip)
/// and recursively frees nested source iterators. Closures (for Map, Filter)
/// are NOT freed since they are owned by the calling context.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_free(iter: *mut UnifiedIterator) {
    if iter.is_null() {
        return;
    }

    unsafe {
        let iter_ref = &*iter;
        match iter_ref.kind {
            IteratorKind::Array => {
                // Decrement ref count on array
                let array = iter_ref.source.array.array;
                if !array.is_null() {
                    RcArray::dec_ref(array as *mut RcArray);
                }
            }
            IteratorKind::Map => {
                // Recursively free the source iterator
                // Note: we don't free the transform closure - it's owned by calling context
                let source = iter_ref.source.map.source;
                vole_array_iter_free(source);
            }
            IteratorKind::Filter => {
                // Recursively free the source iterator
                // Note: we don't free the predicate closure - it's owned by calling context
                let source = iter_ref.source.filter.source;
                vole_array_iter_free(source);
            }
            IteratorKind::Take => {
                // Recursively free the source iterator
                let source = iter_ref.source.take.source;
                vole_array_iter_free(source);
            }
            IteratorKind::Skip => {
                // Recursively free the source iterator
                let source = iter_ref.source.skip.source;
                vole_array_iter_free(source);
            }
            IteratorKind::Chain => {
                // Recursively free both source iterators
                let first = iter_ref.source.chain.first;
                let second = iter_ref.source.chain.second;
                vole_array_iter_free(first);
                vole_array_iter_free(second);
            }
        }

        // Free this iterator
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
        IteratorKind::Chain => {
            // For chain iterators, delegate to chain_next logic
            vole_chain_iter_next(iter, out_value)
        }
    }
}

/// Get next value from any iterator and return a tagged union pointer.
/// Layout: [tag:1][pad:7][payload:8].
/// Tags are determined by the normalized union ordering: "Done" < "I64" alphabetically,
/// so the union is [Done, I64] where tag 0 = Done, tag 1 = value.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_next(iter: *mut UnifiedIterator) -> *mut u8 {
    let mut value: i64 = 0;
    let has_value = if iter.is_null() {
        0
    } else {
        vole_array_iter_next(iter, &mut value)
    };

    let layout = Layout::from_size_align(16, 8).expect("valid union layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Tag 0 = Done (first in sorted union), Tag 1 = value (second in sorted union)
    let tag = if has_value == 0 { 0u8 } else { 1u8 };
    unsafe {
        std::ptr::write(ptr, tag);
        let payload_ptr = ptr.add(8) as *mut i64;
        std::ptr::write(payload_ptr, if has_value == 0 { 0 } else { value });
    }

    ptr
}

/// Collect all remaining iterator values into a new array
/// Returns pointer to newly allocated array (empty if iterator is null)
/// Frees the iterator after collecting.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

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
    // All lambdas now use closure calling convention (closure ptr as first arg)
    unsafe {
        let func_ptr = Closure::get_func(map_src.transform);
        let transform_fn: extern "C" fn(*const Closure, i64) -> i64 = std::mem::transmute(func_ptr);
        let result = transform_fn(map_src.transform, source_value);
        *out_value = result;
    }

    1 // Has value
}

/// Collect all remaining map iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

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
        // All lambdas now use closure calling convention (closure ptr as first arg)
        let passes: i8 = unsafe {
            let func_ptr = Closure::get_func(filter_src.predicate);
            let predicate_fn: extern "C" fn(*const Closure, i64) -> i8 =
                std::mem::transmute(func_ptr);
            predicate_fn(filter_src.predicate, source_value)
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
/// Frees the iterator after collecting.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

    result
}

// =============================================================================
// Consumer methods - eager evaluation that consumes the entire iterator
// =============================================================================

/// Count the number of elements in any iterator
/// Returns the count as i64
/// Frees the iterator after counting.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

    count
}

/// Sum all elements in any iterator (assumes i64 elements)
/// Returns the sum as i64
/// Frees the iterator after summing.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

    sum
}

/// Call a function for each element in any iterator
/// The callback is a closure that takes one i64 argument and returns nothing
/// Frees the iterator after iteration.
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
        // All lambdas now use closure calling convention (closure ptr as first arg)
        unsafe {
            let func_ptr = Closure::get_func(callback);
            let callback_fn: extern "C" fn(*const Closure, i64) = std::mem::transmute(func_ptr);
            callback_fn(callback, value);
        }
    }

    // Free the iterator chain
    vole_array_iter_free(iter);
}

/// Reduce all elements in any iterator using an accumulator function
/// Takes initial value and a reducer closure (acc, value) -> new_acc
/// Returns the final accumulated value
/// Frees the iterator after reduction.
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
        // All lambdas now use closure calling convention (closure ptr as first arg)
        unsafe {
            let func_ptr = Closure::get_func(reducer);
            let reducer_fn: extern "C" fn(*const Closure, i64, i64) -> i64 =
                std::mem::transmute(func_ptr);
            acc = reducer_fn(reducer, acc, value);
        }
    }

    // Free the iterator chain
    vole_array_iter_free(iter);

    acc
}

/// Get the first element from any iterator, returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Note: For T?, variants are sorted by debug string. I64 < Nil alphabetically,
/// so tag 0 = I64 (value), tag 1 = Nil.
/// Frees the iterator after getting the first element.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_first(iter: *mut UnifiedIterator) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() {
        // Return nil
        unsafe {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
        return ptr;
    }

    let mut value: i64 = 0;
    let has_value = vole_array_iter_next(iter, &mut value);

    // Free the iterator chain
    vole_array_iter_free(iter);

    unsafe {
        if has_value != 0 {
            std::ptr::write(ptr, 0u8); // tag 0 = value present
            std::ptr::write(ptr.add(8) as *mut i64, value);
        } else {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
    }

    ptr
}

/// Get the last element from any iterator, returns T? (optional)
/// Consumes the entire iterator to find the last element.
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the last element.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_last(iter: *mut UnifiedIterator) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() {
        // Return nil
        unsafe {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
        return ptr;
    }

    let mut last_value: i64 = 0;
    let mut found_any = false;

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }
        last_value = value;
        found_any = true;
    }

    // Free the iterator chain
    vole_array_iter_free(iter);

    unsafe {
        if found_any {
            std::ptr::write(ptr, 0u8); // tag 0 = value present
            std::ptr::write(ptr.add(8) as *mut i64, last_value);
        } else {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
    }

    ptr
}

/// Get the nth element from any iterator (0-indexed), returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the nth element.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_nth(iter: *mut UnifiedIterator, n: i64) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() || n < 0 {
        // Return nil for null iterator or negative index
        unsafe {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
        if !iter.is_null() {
            vole_array_iter_free(iter);
        }
        return ptr;
    }

    // Skip n elements
    for _ in 0..n {
        let mut dummy: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut dummy);
        if has_value == 0 {
            // Iterator exhausted before reaching nth element
            vole_array_iter_free(iter);
            unsafe {
                std::ptr::write(ptr, 1u8); // tag 1 = nil
                std::ptr::write(ptr.add(8) as *mut i64, 0);
            }
            return ptr;
        }
    }

    // Get the nth element
    let mut value: i64 = 0;
    let has_value = vole_array_iter_next(iter, &mut value);

    // Free the iterator chain
    vole_array_iter_free(iter);

    unsafe {
        if has_value != 0 {
            std::ptr::write(ptr, 0u8); // tag 0 = value present
            std::ptr::write(ptr.add(8) as *mut i64, value);
        } else {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
    }

    ptr
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
/// Frees the iterator after collecting.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

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
/// Frees the iterator after collecting.
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

    // Free the iterator chain
    vole_array_iter_free(iter);

    result
}

// =============================================================================
// Search methods: find, any, all
// =============================================================================

/// Find the first element matching a predicate, returns T? (optional)
/// Short-circuits on first match.
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after finding (or exhausting).
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_find(iter: *mut UnifiedIterator, predicate: *const Closure) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() || predicate.is_null() {
        // Return nil
        unsafe {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
        if !iter.is_null() {
            vole_array_iter_free(iter);
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
            vole_array_iter_free(iter);

            unsafe {
                std::ptr::write(ptr, 0u8); // tag 0 = value present
                std::ptr::write(ptr.add(8) as *mut i64, value);
            }
            return ptr;
        }
    }

    // Free the iterator chain
    vole_array_iter_free(iter);

    // No match found, return nil
    unsafe {
        std::ptr::write(ptr, 1u8); // tag 1 = nil
        std::ptr::write(ptr.add(8) as *mut i64, 0);
    }

    ptr
}

/// Check if any element matches a predicate, returns bool
/// Short-circuits on first true.
/// Frees the iterator after checking.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_any(iter: *mut UnifiedIterator, predicate: *const Closure) -> i8 {
    if iter.is_null() || predicate.is_null() {
        if !iter.is_null() {
            vole_array_iter_free(iter);
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
            vole_array_iter_free(iter);
            return 1; // true
        }
    }

    // Free the iterator chain
    vole_array_iter_free(iter);

    0 // false - no element matched
}

/// Check if all elements match a predicate, returns bool
/// Short-circuits on first false.
/// Frees the iterator after checking.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_all(iter: *mut UnifiedIterator, predicate: *const Closure) -> i8 {
    if iter.is_null() || predicate.is_null() {
        if !iter.is_null() {
            vole_array_iter_free(iter);
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
            vole_array_iter_free(iter);
            return 0; // false
        }
    }

    // Free the iterator chain
    vole_array_iter_free(iter);

    1 // true - all elements matched
}

// =============================================================================
// ChainIterator - lazy concatenation of two iterators
// =============================================================================

/// Create a new chain iterator that yields elements from first, then second
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chain_iter(
    first: *mut UnifiedIterator,
    second: *mut UnifiedIterator,
) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Chain,
        source: IteratorSource {
            chain: ChainSource {
                first,
                second,
                on_second: 0, // Start with first iterator
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from chain iterator
/// First exhausts the first iterator, then yields from the second
/// Returns 1 and stores value in out_value if available
/// Returns 0 if both iterators exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chain_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    // This function should only be called for Chain iterators
    if iter_ref.kind != IteratorKind::Chain {
        return 0;
    }

    let chain_src = unsafe { &mut iter_ref.source.chain };

    // If we're still on the first iterator
    if chain_src.on_second == 0 {
        let has_value = vole_array_iter_next(chain_src.first, out_value);
        if has_value != 0 {
            return 1; // Got value from first
        }
        // First exhausted, switch to second
        chain_src.on_second = 1;
    }

    // Now try the second iterator
    vole_array_iter_next(chain_src.second, out_value)
}

/// Collect all remaining chain iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chain_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

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
    vole_array_iter_free(iter);

    result
}
