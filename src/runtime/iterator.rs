//! Iterator runtime support
//!
//! Provides runtime representation for iterators.
//! Uses a unified IteratorSource enum to support chaining (e.g., map().map()).

use crate::runtime::array::RcArray;
use crate::runtime::closure::Closure;
use crate::runtime::string::RcString;
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
    Flatten = 6,
    FlatMap = 7,
    Unique = 8,
    Chunks = 9,
    Windows = 10,
    Repeat = 11,
    Once = 12,
    Empty = 13,
    FromFn = 14,
    Range = 15,
    StringChars = 16,
}

/// Unified iterator source - can be either an array, map, filter, take, skip, chain, flatten, flat_map, unique, chunks, windows, repeat, once, empty, from_fn, range, or string_chars iterator
/// This allows chaining (e.g., arr.iter().map(f).filter(p).take(5))
#[repr(C)]
pub union IteratorSource {
    pub array: ArraySource,
    pub map: MapSource,
    pub filter: FilterSource,
    pub take: TakeSource,
    pub skip: SkipSource,
    pub chain: ChainSource,
    pub flatten: FlattenSource,
    pub flat_map: FlatMapSource,
    pub unique: UniqueSource,
    pub chunks: ChunksSource,
    pub windows: WindowsSource,
    pub repeat: RepeatSource,
    pub once: OnceSource,
    pub empty: EmptySource,
    pub from_fn: FromFnSource,
    pub range: RangeSource,
    pub string_chars: StringCharsSource,
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

/// Source data for flatten iteration (flattens nested iterables)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FlattenSource {
    /// Outer iterator that yields arrays
    pub outer: *mut UnifiedIterator,
    /// Current inner iterator (null if not started or exhausted)
    pub inner: *mut UnifiedIterator,
}

/// Source data for flat_map iteration (map then flatten)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FlatMapSource {
    /// Source iterator
    pub source: *mut UnifiedIterator,
    /// Transform closure that returns an array
    pub transform: *const Closure,
    /// Current inner iterator (null if not started or exhausted)
    pub inner: *mut UnifiedIterator,
}

/// Source data for unique iteration (filters consecutive duplicates)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct UniqueSource {
    /// Pointer to source iterator
    pub source: *mut UnifiedIterator,
    /// Previous value (only valid after first element)
    pub prev: i64,
    /// Whether we've seen the first element (0 = no, 1 = yes)
    pub has_prev: i64,
}

/// Source data for chunks iteration (yields non-overlapping chunks as arrays)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ChunksSource {
    /// Collected elements array
    pub elements: *mut RcArray,
    /// Chunk size
    pub chunk_size: i64,
    /// Current position in the elements array
    pub position: i64,
}

/// Source data for windows iteration (yields overlapping windows as arrays)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct WindowsSource {
    /// Collected elements array
    pub elements: *mut RcArray,
    /// Window size
    pub window_size: i64,
    /// Current position in the elements array
    pub position: i64,
}

/// Source data for repeat iteration (infinite iterator yielding the same value)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct RepeatSource {
    /// The value to repeat
    pub value: i64,
}

/// Source data for once iteration (yields a single value)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct OnceSource {
    /// The value to yield
    pub value: i64,
    /// Whether the value has been yielded (0 = no, 1 = yes)
    pub exhausted: i64,
}

/// Source data for empty iteration (yields nothing)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct EmptySource {
    /// Placeholder field (empty struct would have zero size)
    pub _placeholder: i64,
}

/// Source data for from_fn iteration (calls a generator function repeatedly)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FromFnSource {
    /// Generator closure that returns T? (nil to end iteration)
    pub generator: *const Closure,
}

/// Source data for range iteration (start..end or start..=end)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct RangeSource {
    /// Current value in the range
    pub current: i64,
    /// End value (exclusive)
    pub end: i64,
}

/// Source data for string character iteration (yields each unicode character as a string)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct StringCharsSource {
    /// Pointer to the source string
    pub string: *const RcString,
    /// Current byte position in the string (not character position)
    pub byte_pos: i64,
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
pub type FlattenIterator = UnifiedIterator;
pub type FlatMapIterator = UnifiedIterator;
pub type UniqueIterator = UnifiedIterator;
pub type ChunksIterator = UnifiedIterator;
pub type WindowsIterator = UnifiedIterator;
pub type RepeatIterator = UnifiedIterator;
pub type OnceIterator = UnifiedIterator;
pub type EmptyIterator = UnifiedIterator;
pub type FromFnIterator = UnifiedIterator;
pub type RangeIterator = UnifiedIterator;
pub type StringCharsIterator = UnifiedIterator;

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
            IteratorKind::Flatten => {
                // Recursively free outer iterator and current inner iterator
                let outer = iter_ref.source.flatten.outer;
                let inner = iter_ref.source.flatten.inner;
                vole_array_iter_free(outer);
                if !inner.is_null() {
                    vole_array_iter_free(inner);
                }
            }
            IteratorKind::FlatMap => {
                // Recursively free source iterator and current inner iterator
                // Note: we don't free the transform closure - it's owned by calling context
                let source = iter_ref.source.flat_map.source;
                let inner = iter_ref.source.flat_map.inner;
                vole_array_iter_free(source);
                if !inner.is_null() {
                    vole_array_iter_free(inner);
                }
            }
            IteratorKind::Unique => {
                // Recursively free the source iterator
                let source = iter_ref.source.unique.source;
                vole_array_iter_free(source);
            }
            IteratorKind::Chunks => {
                // Free the collected elements array
                let elements = iter_ref.source.chunks.elements;
                if !elements.is_null() {
                    RcArray::dec_ref(elements);
                }
            }
            IteratorKind::Windows => {
                // Free the collected elements array
                let elements = iter_ref.source.windows.elements;
                if !elements.is_null() {
                    RcArray::dec_ref(elements);
                }
            }
            IteratorKind::Repeat => {
                // No resources to free - just the value
            }
            IteratorKind::Once => {
                // No resources to free - just the value and flag
            }
            IteratorKind::Empty => {
                // No resources to free
            }
            IteratorKind::FromFn => {
                // Note: we don't free the generator closure - it's owned by calling context
            }
            IteratorKind::Range => {
                // No resources to free - just start/current/end values
            }
            IteratorKind::StringChars => {
                // Decrement ref count on string
                let string = iter_ref.source.string_chars.string;
                if !string.is_null() {
                    RcString::dec_ref(string as *mut RcString);
                }
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
        IteratorKind::Flatten => {
            // For flatten iterators, delegate to flatten_next logic
            vole_flatten_iter_next(iter, out_value)
        }
        IteratorKind::FlatMap => {
            // For flat_map iterators, delegate to flat_map_next logic
            vole_flat_map_iter_next(iter, out_value)
        }
        IteratorKind::Unique => {
            // For unique iterators, delegate to unique_next logic
            vole_unique_iter_next(iter, out_value)
        }
        IteratorKind::Chunks => {
            // For chunks iterators, delegate to chunks_next logic
            vole_chunks_iter_next(iter, out_value)
        }
        IteratorKind::Windows => {
            // For windows iterators, delegate to windows_next logic
            vole_windows_iter_next(iter, out_value)
        }
        IteratorKind::Repeat => {
            // For repeat iterators, delegate to repeat_next logic
            vole_repeat_iter_next(iter, out_value)
        }
        IteratorKind::Once => {
            // For once iterators, delegate to once_next logic
            vole_once_iter_next(iter, out_value)
        }
        IteratorKind::Empty => {
            // Empty iterator always returns Done
            0
        }
        IteratorKind::FromFn => {
            // For from_fn iterators, delegate to from_fn_next logic
            vole_from_fn_iter_next(iter, out_value)
        }
        IteratorKind::Range => {
            // For range iterators, delegate to range_next logic
            vole_range_iter_next(iter, out_value)
        }
        IteratorKind::StringChars => {
            // For string chars iterators, delegate to string_chars_next logic
            vole_string_chars_iter_next(iter, out_value)
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

// =============================================================================
// FlattenIterator - lazy flattening of nested iterables
// =============================================================================

/// Create a new flatten iterator wrapping any source iterator that yields arrays
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flatten_iter(source: *mut UnifiedIterator) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Flatten,
        source: IteratorSource {
            flatten: FlattenSource {
                outer: source,
                inner: std::ptr::null_mut(),
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from flatten iterator
/// Yields elements from each inner array until all are exhausted
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flatten_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    // This function should only be called for Flatten iterators
    if iter_ref.kind != IteratorKind::Flatten {
        return 0;
    }

    let flatten_src = unsafe { &mut iter_ref.source.flatten };

    loop {
        // If we have an inner iterator, try to get the next value from it
        if !flatten_src.inner.is_null() {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(flatten_src.inner, &mut value);
            if has_value != 0 {
                unsafe { *out_value = value };
                return 1;
            }
            // Inner iterator exhausted, free it and get next outer element
            vole_array_iter_free(flatten_src.inner);
            flatten_src.inner = std::ptr::null_mut();
        }

        // Get next array from outer iterator
        let mut array_ptr: i64 = 0;
        let has_array = vole_array_iter_next(flatten_src.outer, &mut array_ptr);
        if has_array == 0 {
            return 0; // Outer iterator exhausted
        }

        // Create an iterator for the inner array
        let inner_array = array_ptr as *const RcArray;
        flatten_src.inner = vole_array_iter(inner_array);
        // Continue loop to get first element from this inner iterator
    }
}

/// Collect all remaining flatten iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flatten_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_flatten_iter_next(iter, &mut value);

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

    // Free the flatten iterator chain
    vole_array_iter_free(iter);

    result
}

// =============================================================================
// FlatMapIterator - lazy map then flatten
// =============================================================================

/// Create a new flat_map iterator wrapping any source iterator
/// Takes a transform function that returns an array
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flat_map_iter(
    source: *mut UnifiedIterator,
    transform: *const Closure,
) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::FlatMap,
        source: IteratorSource {
            flat_map: FlatMapSource {
                source,
                transform,
                inner: std::ptr::null_mut(),
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from flat_map iterator
/// Applies transform to each source element, then yields elements from resulting arrays
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flat_map_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    // This function should only be called for FlatMap iterators
    if iter_ref.kind != IteratorKind::FlatMap {
        return 0;
    }

    let flat_map_src = unsafe { &mut iter_ref.source.flat_map };

    loop {
        // If we have an inner iterator, try to get the next value from it
        if !flat_map_src.inner.is_null() {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(flat_map_src.inner, &mut value);
            if has_value != 0 {
                unsafe { *out_value = value };
                return 1;
            }
            // Inner iterator exhausted, free it and get next source element
            vole_array_iter_free(flat_map_src.inner);
            flat_map_src.inner = std::ptr::null_mut();
        }

        // Get next value from source iterator
        let mut source_value: i64 = 0;
        let has_source = vole_array_iter_next(flat_map_src.source, &mut source_value);
        if has_source == 0 {
            return 0; // Source iterator exhausted
        }

        // Apply transform function to get an array
        let array_ptr: i64 = unsafe {
            let func_ptr = Closure::get_func(flat_map_src.transform);
            let transform_fn: extern "C" fn(*const Closure, i64) -> i64 =
                std::mem::transmute(func_ptr);
            transform_fn(flat_map_src.transform, source_value)
        };

        // Create an iterator for the resulting array
        let inner_array = array_ptr as *const RcArray;
        flat_map_src.inner = vole_array_iter(inner_array);
        // Continue loop to get first element from this inner iterator
    }
}

/// Collect all remaining flat_map iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flat_map_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

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
    vole_array_iter_free(iter);

    result
}

// =============================================================================
// Collecting operations: reverse, sorted, unique
// =============================================================================

/// Reverse iterator - collects all elements, reverses them, returns new array iterator
/// This is an eager operation that consumes the entire source iterator.
/// Frees the source iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_reverse_iter(iter: *mut UnifiedIterator) -> *mut UnifiedIterator {
    use crate::runtime::value::TaggedValue;

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
    vole_array_iter_free(iter);

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

    // Return iterator over the reversed array
    vole_array_iter(result)
}

/// Sorted iterator - collects all elements, sorts them, returns new array iterator
/// This is an eager operation that consumes the entire source iterator.
/// Sorts i64 values in ascending order.
/// Frees the source iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_sorted_iter(iter: *mut UnifiedIterator) -> *mut UnifiedIterator {
    use crate::runtime::value::TaggedValue;

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
    vole_array_iter_free(iter);

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

    // Return iterator over the sorted array
    vole_array_iter(result)
}

/// Create a new unique iterator wrapping any source iterator
/// Filters consecutive duplicates (like Unix uniq)
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_unique_iter(source: *mut UnifiedIterator) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Unique,
        source: IteratorSource {
            unique: UniqueSource {
                source,
                prev: 0,
                has_prev: 0,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from unique iterator
/// Skips consecutive duplicate values
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_unique_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    // This function should only be called for Unique iterators
    if iter_ref.kind != IteratorKind::Unique {
        return 0;
    }

    let unique_src = unsafe { &mut iter_ref.source.unique };

    loop {
        // Get next value from source iterator
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(unique_src.source, &mut value);

        if has_value == 0 {
            return 0; // Source exhausted
        }

        // If this is the first element, always yield it
        if unique_src.has_prev == 0 {
            unique_src.has_prev = 1;
            unique_src.prev = value;
            unsafe { *out_value = value };
            return 1;
        }

        // If value differs from previous, yield it
        if value != unique_src.prev {
            unique_src.prev = value;
            unsafe { *out_value = value };
            return 1;
        }
        // Otherwise, skip this duplicate and continue
    }
}

// =============================================================================
// ChunksIterator - splits into non-overlapping chunks
// =============================================================================

/// Create a new chunks iterator wrapping any source iterator
/// First collects all elements, then yields non-overlapping chunks of the specified size.
/// The last chunk may be smaller than the specified size.
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chunks_iter(
    source: *mut UnifiedIterator,
    chunk_size: i64,
) -> *mut UnifiedIterator {
    use crate::runtime::value::TaggedValue;

    // First, collect all elements from the source iterator
    let elements = RcArray::new();

    if !source.is_null() && chunk_size > 0 {
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(source, &mut value);
            if has_value == 0 {
                break;
            }
            unsafe {
                RcArray::push(
                    elements,
                    TaggedValue {
                        tag: 0,
                        value: value as u64,
                    },
                );
            }
        }
        // Free the source iterator
        vole_array_iter_free(source);
    } else if !source.is_null() {
        // Free the source even if chunk_size <= 0
        vole_array_iter_free(source);
    }

    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Chunks,
        source: IteratorSource {
            chunks: ChunksSource {
                elements,
                chunk_size: if chunk_size > 0 { chunk_size } else { 1 },
                position: 0,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next chunk from chunks iterator
/// Returns 1 and stores array pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chunks_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    use crate::runtime::value::TaggedValue;

    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    if iter_ref.kind != IteratorKind::Chunks {
        return 0;
    }

    let chunks_src = unsafe { &mut iter_ref.source.chunks };

    let elements_len = unsafe { (*chunks_src.elements).len } as i64;

    // Check if we've exhausted all elements
    if chunks_src.position >= elements_len {
        return 0;
    }

    // Create a new array for this chunk
    let chunk = RcArray::new();
    let end_pos = std::cmp::min(chunks_src.position + chunks_src.chunk_size, elements_len);

    for i in chunks_src.position..end_pos {
        let value = unsafe {
            let data = (*chunks_src.elements).data;
            (*data.add(i as usize)).value
        };
        unsafe {
            RcArray::push(chunk, TaggedValue { tag: 0, value });
        }
    }

    chunks_src.position = end_pos;

    unsafe { *out_value = chunk as i64 };
    1
}

/// Collect all remaining chunks into a new array of arrays
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chunks_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_chunks_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Push chunk array to result
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: 0, // Arrays are stored as pointers
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator
    vole_array_iter_free(iter);

    result
}

// =============================================================================
// WindowsIterator - sliding window of elements
// =============================================================================

/// Create a new windows iterator wrapping any source iterator
/// First collects all elements, then yields overlapping windows of the specified size.
/// Yields nothing if there are fewer elements than window_size.
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_windows_iter(
    source: *mut UnifiedIterator,
    window_size: i64,
) -> *mut UnifiedIterator {
    use crate::runtime::value::TaggedValue;

    // First, collect all elements from the source iterator
    let elements = RcArray::new();

    if !source.is_null() && window_size > 0 {
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(source, &mut value);
            if has_value == 0 {
                break;
            }
            unsafe {
                RcArray::push(
                    elements,
                    TaggedValue {
                        tag: 0,
                        value: value as u64,
                    },
                );
            }
        }
        // Free the source iterator
        vole_array_iter_free(source);
    } else if !source.is_null() {
        // Free the source even if window_size <= 0
        vole_array_iter_free(source);
    }

    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Windows,
        source: IteratorSource {
            windows: WindowsSource {
                elements,
                window_size: if window_size > 0 { window_size } else { 1 },
                position: 0,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next window from windows iterator
/// Returns 1 and stores array pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_windows_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    use crate::runtime::value::TaggedValue;

    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    if iter_ref.kind != IteratorKind::Windows {
        return 0;
    }

    let windows_src = unsafe { &mut iter_ref.source.windows };

    let elements_len = unsafe { (*windows_src.elements).len } as i64;

    // Check if we can produce another window
    // We need at least window_size elements starting from position
    if windows_src.position + windows_src.window_size > elements_len {
        return 0;
    }

    // Create a new array for this window
    let window = RcArray::new();
    for i in 0..windows_src.window_size {
        let value = unsafe {
            let data = (*windows_src.elements).data;
            (*data.add((windows_src.position + i) as usize)).value
        };
        unsafe {
            RcArray::push(window, TaggedValue { tag: 0, value });
        }
    }

    // Move position forward by 1 for sliding window
    windows_src.position += 1;

    unsafe { *out_value = window as i64 };
    1
}

/// Collect all remaining windows into a new array of arrays
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_windows_iter_collect(iter: *mut UnifiedIterator) -> *mut RcArray {
    use crate::runtime::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_windows_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Push window array to result
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: 0, // Arrays are stored as pointers
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator
    vole_array_iter_free(iter);

    result
}

// =============================================================================
// RepeatIterator - infinite iterator yielding the same value
// =============================================================================

/// Create a new repeat iterator that yields the same value forever
/// WARNING: This is an infinite iterator - MUST use with take() or similar
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_repeat_iter(value: i64) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Repeat,
        source: IteratorSource {
            repeat: RepeatSource { value },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from repeat iterator
/// Always returns 1 with the same value (infinite iterator)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_repeat_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &*iter };

    if iter_ref.kind != IteratorKind::Repeat {
        return 0;
    }

    let repeat_src = unsafe { iter_ref.source.repeat };
    unsafe { *out_value = repeat_src.value };
    1 // Always has a value (infinite iterator)
}

// =============================================================================
// OnceIterator - iterator that yields a single value
// =============================================================================

/// Create a new once iterator that yields exactly one value
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_once_iter(value: i64) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Once,
        source: IteratorSource {
            once: OnceSource {
                value,
                exhausted: 0,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from once iterator
/// Returns 1 with the value on first call, 0 on subsequent calls
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_once_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    if iter_ref.kind != IteratorKind::Once {
        return 0;
    }

    let once_src = unsafe { &mut iter_ref.source.once };

    if once_src.exhausted != 0 {
        return 0; // Already yielded the value
    }

    once_src.exhausted = 1;
    unsafe { *out_value = once_src.value };
    1 // Has value
}

// =============================================================================
// EmptyIterator - iterator that yields nothing
// =============================================================================

/// Create a new empty iterator that yields nothing
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_empty_iter() -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Empty,
        source: IteratorSource {
            empty: EmptySource { _placeholder: 0 },
        },
    });
    Box::into_raw(iter)
}

// Note: Empty iterator next is handled inline in vole_array_iter_next
// as it always returns 0 immediately

// =============================================================================
// FromFnIterator - iterator from a generator function
// =============================================================================

/// Create a new from_fn iterator that calls a generator function repeatedly
/// The generator should return T? - when it returns nil, iteration ends
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_from_fn_iter(generator: *const Closure) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::FromFn,
        source: IteratorSource {
            from_fn: FromFnSource { generator },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from from_fn iterator
/// Calls the generator function - returns 1 with value if not nil, 0 if nil
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_from_fn_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &*iter };

    if iter_ref.kind != IteratorKind::FromFn {
        return 0;
    }

    let from_fn_src = unsafe { iter_ref.source.from_fn };

    // Call the generator function
    // The generator returns T? which is a tagged union with layout [tag:1][pad:7][payload:8]
    // Tag 0 = I64 (value present), Tag 1 = Nil
    unsafe {
        let func_ptr = Closure::get_func(from_fn_src.generator);
        let generator_fn: extern "C" fn(*const Closure) -> *mut u8 = std::mem::transmute(func_ptr);
        let result_ptr = generator_fn(from_fn_src.generator);

        if result_ptr.is_null() {
            return 0;
        }

        // Read the tag
        let tag = std::ptr::read(result_ptr);
        let payload_ptr = result_ptr.add(8) as *const i64;
        let payload = std::ptr::read(payload_ptr);

        // Free the result (it was allocated by the generator)
        let layout = Layout::from_size_align(16, 8).expect("valid layout");
        std::alloc::dealloc(result_ptr, layout);

        // Tag 0 = I64 (value), Tag 1 = Nil
        if tag == 0 {
            *out_value = payload;
            1 // Has value
        } else {
            0 // Nil - end iteration
        }
    }
}

// =============================================================================
// RangeIterator - iterator over a range of integers (start..end)
// =============================================================================

/// Create a new range iterator that yields integers from start to end (exclusive)
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_range_iter(start: i64, end: i64) -> *mut UnifiedIterator {
    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::Range,
        source: IteratorSource {
            range: RangeSource {
                current: start,
                end,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next value from range iterator
/// Returns 1 with the value if current < end, 0 if done
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_range_iter_next(iter: *mut UnifiedIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    if iter_ref.kind != IteratorKind::Range {
        return 0;
    }

    let range_src = unsafe { &mut iter_ref.source.range };

    // Check if we've reached the end
    if range_src.current >= range_src.end {
        return 0; // Done
    }

    // Yield current value and increment
    unsafe { *out_value = range_src.current };
    range_src.current += 1;
    1 // Has value
}

// =============================================================================
// StringCharsIterator - iterator over unicode characters of a string
// =============================================================================

/// Create a new string chars iterator that yields each unicode character as a string
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_chars_iter(string: *const RcString) -> *mut UnifiedIterator {
    // Increment ref count on string so it stays alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
    }

    let iter = Box::new(UnifiedIterator {
        kind: IteratorKind::StringChars,
        source: IteratorSource {
            string_chars: StringCharsSource {
                string,
                byte_pos: 0,
            },
        },
    });
    Box::into_raw(iter)
}

/// Get next character from string chars iterator
/// Returns 1 and stores the character string pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_chars_iter_next(
    iter: *mut UnifiedIterator,
    out_value: *mut i64,
) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut *iter };

    if iter_ref.kind != IteratorKind::StringChars {
        return 0;
    }

    let string_chars_src = unsafe { &mut iter_ref.source.string_chars };

    if string_chars_src.string.is_null() {
        return 0;
    }

    unsafe {
        let string_ref = &*string_chars_src.string;
        let byte_len = string_ref.len as i64;

        // Check if we've exhausted the string
        if string_chars_src.byte_pos >= byte_len {
            return 0; // Done
        }

        // Get the string data starting at current byte position
        let data = string_ref.data();
        let remaining = &data[string_chars_src.byte_pos as usize..];

        // Get the next UTF-8 character
        // Safety: RcString stores valid UTF-8
        let remaining_str = std::str::from_utf8_unchecked(remaining);
        let next_char = remaining_str.chars().next();

        if let Some(ch) = next_char {
            // Get the byte length of this character
            let char_len = ch.len_utf8();

            // Create a new RcString containing just this character
            let mut char_buf = [0u8; 4]; // Max UTF-8 bytes per char
            let char_str = ch.encode_utf8(&mut char_buf);
            let new_string = RcString::new(char_str);

            // Update byte position
            string_chars_src.byte_pos += char_len as i64;

            // Return the new string pointer as i64
            *out_value = new_string as i64;
            1 // Has value
        } else {
            0 // Done - should not happen if byte_pos < byte_len
        }
    }
}
