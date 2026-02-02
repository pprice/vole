//! Iterator runtime support
//!
//! Provides runtime representation for iterators.
//! Uses a unified IteratorSource enum to support chaining (e.g., map().map()).

use crate::alloc_track;
use crate::array::RcArray;
use crate::closure::Closure;
use crate::string::RcString;
use crate::value::{RcHeader, TYPE_ITERATOR, rc_dec, rc_inc};
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

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
    /// Interface iterator - wraps a boxed interface implementing Iterator
    Interface = 17,
    /// Enumerate iterator - yields (index, value) pairs
    Enumerate = 18,
    /// Zip iterator - combines two iterators into pairs
    Zip = 19,
    /// String split iterator - splits string by delimiter
    StringSplit = 20,
    /// String lines iterator - splits string by newlines
    StringLines = 21,
    /// String codepoints iterator - yields unicode codepoints as i32
    StringCodepoints = 22,
}

/// Unified iterator source - can be either an array, map, filter, take, skip, chain, flatten, flat_map, unique, chunks, windows, repeat, once, empty, from_fn, range, string_chars, or interface iterator
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
    pub interface: InterfaceSource,
    pub enumerate: EnumerateSource,
    pub zip: ZipSource,
    pub string_split: StringSplitSource,
    pub string_lines: StringLinesSource,
    pub string_codepoints: StringCodepointsSource,
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
    pub source: *mut RcIterator,
    /// Transform closure
    pub transform: *const Closure,
}

/// Source data for filter iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FilterSource {
    /// Pointer to source iterator (could be any iterator type)
    pub source: *mut RcIterator,
    /// Predicate closure that returns bool
    pub predicate: *const Closure,
}

/// Source data for take iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct TakeSource {
    /// Pointer to source iterator (could be any iterator type)
    pub source: *mut RcIterator,
    /// Number of elements remaining to take
    pub remaining: i64,
}

/// Source data for skip iteration
#[repr(C)]
#[derive(Clone, Copy)]
pub struct SkipSource {
    /// Pointer to source iterator (could be any iterator type)
    pub source: *mut RcIterator,
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
    pub first: *mut RcIterator,
    /// Second iterator to consume after first is exhausted
    pub second: *mut RcIterator,
    /// Whether we've exhausted the first iterator (0 = on first, 1 = on second)
    pub on_second: i64,
}

/// Source data for flatten iteration (flattens nested iterables)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FlattenSource {
    /// Outer iterator that yields arrays
    pub outer: *mut RcIterator,
    /// Current inner iterator (null if not started or exhausted)
    pub inner: *mut RcIterator,
}

/// Source data for flat_map iteration (map then flatten)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FlatMapSource {
    /// Source iterator
    pub source: *mut RcIterator,
    /// Transform closure that returns an array
    pub transform: *const Closure,
    /// Current inner iterator (null if not started or exhausted)
    pub inner: *mut RcIterator,
}

/// Source data for unique iteration (filters consecutive duplicates)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct UniqueSource {
    /// Pointer to source iterator
    pub source: *mut RcIterator,
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

/// Source data for interface iteration (wraps a boxed interface implementing Iterator)
/// This allows user-defined types implementing Iterator to use the standard iterator methods.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct InterfaceSource {
    /// Pointer to the boxed interface (layout: [data_ptr, vtable_ptr])
    pub boxed_interface: *const u8,
}

/// Source data for enumerate iteration (yields (index, value) pairs)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct EnumerateSource {
    /// Pointer to source iterator
    pub source: *mut RcIterator,
    /// Current index (0-based)
    pub index: i64,
}

/// Source data for zip iteration (combines two iterators)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ZipSource {
    /// First iterator
    pub first: *mut RcIterator,
    /// Second iterator
    pub second: *mut RcIterator,
}

/// Source data for string split iteration (splits string by delimiter)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct StringSplitSource {
    /// Pointer to the source string
    pub string: *const RcString,
    /// Pointer to the delimiter string
    pub delimiter: *const RcString,
    /// Current byte position in the string (not character position)
    pub byte_pos: i64,
    /// Whether the iterator is exhausted (0 = no, 1 = yes)
    pub exhausted: i64,
}

/// Source data for string lines iteration (splits string by newlines)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct StringLinesSource {
    /// Pointer to the source string
    pub string: *const RcString,
    /// Current byte position in the string (not character position)
    pub byte_pos: i64,
    /// Whether the iterator is exhausted (0 = no, 1 = yes)
    pub exhausted: i64,
}

/// Source data for string codepoints iteration (yields unicode codepoints as i32)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct StringCodepointsSource {
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

/// Reference-counted iterator
///
/// Layout: [RcHeader (16 bytes)] [UnifiedIterator (kind + source)] [elem_tag: u64]
///
/// `elem_tag` is the runtime type tag (e.g., TYPE_STRING) for the element type flowing
/// through this iterator. Used by next() to rc_inc produced values and by filter/take/etc.
/// to rc_dec rejected/discarded values.
#[repr(C)]
pub struct RcIterator {
    pub header: RcHeader,
    pub iter: UnifiedIterator,
    /// Runtime type tag for elements (0 = unset/i64, TYPE_STRING = 1, etc.)
    pub elem_tag: u64,
    /// True if this iterator's next() produces freshly owned values (e.g. generators).
    /// Used to decide whether terminal methods should rc_dec consumed elements.
    pub produces_owned: bool,
}

impl RcIterator {
    /// Allocate a new RcIterator with the given kind and source (elem_tag defaults to 0/i64)
    pub fn new(kind: IteratorKind, source: IteratorSource) -> *mut Self {
        Self::new_with_tag(kind, source, 0)
    }

    /// Allocate a new RcIterator with the given kind, source, and element type tag
    pub fn new_with_tag(kind: IteratorKind, source: IteratorSource, elem_tag: u64) -> *mut Self {
        let layout = Layout::new::<RcIterator>();
        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(TYPE_ITERATOR, iterator_drop),
            );
            ptr::write(&mut (*ptr).iter.kind, kind);
            ptr::write(&mut (*ptr).iter.source, source);
            ptr::write(&mut (*ptr).elem_tag, elem_tag);
            ptr::write(&mut (*ptr).produces_owned, false);
            alloc_track::track_alloc(TYPE_ITERATOR);
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
    /// Safe to call because `rc_dec` handles null pointers.
    /// `ptr` must be null or a valid pointer to an initialized `RcIterator`.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[inline]
    pub fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }

    /// Set the element type tag on this iterator (non-recursive).
    /// Each iterator in the chain stores its OWN element type tag.
    /// The tag represents the type of values this iterator produces.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
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
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_set_elem_tag(iter: *mut RcIterator, tag: u64) {
    RcIterator::set_elem_tag(iter, tag);
}

/// Mark an iterator as producing owned values (e.g. generators).
///
/// # Safety
/// `iter` must be null or a valid pointer to an initialized `RcIterator`.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_iter_set_produces_owned(iter: *mut RcIterator) {
    if !iter.is_null() {
        unsafe {
            (*iter).produces_owned = true;
        }
    }
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
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_interface_iter(boxed_interface: *const u8) -> *mut RcIterator {
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
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_interface_iter_tagged(
    boxed_interface: *const u8,
    elem_tag: u64,
) -> *mut RcIterator {
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
    alloc_track::track_dealloc(TYPE_ITERATOR);
    unsafe {
        let rc_iter = ptr as *mut RcIterator;
        let iter_ref = &(*rc_iter).iter;
        iterator_drop_sources(iter_ref);
        let layout = Layout::new::<RcIterator>();
        dealloc(ptr, layout);
    }
}

/// Release resources owned by an iterator's source (without freeing the iterator itself).
///
/// # Safety
/// `iter_ref` must reference a valid `UnifiedIterator`. Union accesses are gated by `kind`.
fn iterator_drop_sources(iter_ref: &UnifiedIterator) {
    // Safety: all union field accesses are gated by the kind discriminant.
    unsafe {
        match iter_ref.kind {
            IteratorKind::Array => {
                let array = iter_ref.source.array.array;
                if !array.is_null() {
                    RcArray::dec_ref(array as *mut RcArray);
                }
            }
            IteratorKind::Map => {
                RcIterator::dec_ref(iter_ref.source.map.source);
                Closure::free(iter_ref.source.map.transform as *mut Closure);
            }
            IteratorKind::Filter => {
                RcIterator::dec_ref(iter_ref.source.filter.source);
                Closure::free(iter_ref.source.filter.predicate as *mut Closure);
            }
            IteratorKind::Take => {
                RcIterator::dec_ref(iter_ref.source.take.source);
            }
            IteratorKind::Skip => {
                RcIterator::dec_ref(iter_ref.source.skip.source);
            }
            IteratorKind::Chain => {
                RcIterator::dec_ref(iter_ref.source.chain.first);
                RcIterator::dec_ref(iter_ref.source.chain.second);
            }
            IteratorKind::Flatten => {
                RcIterator::dec_ref(iter_ref.source.flatten.outer);
                let inner = iter_ref.source.flatten.inner;
                if !inner.is_null() {
                    RcIterator::dec_ref(inner);
                }
            }
            IteratorKind::FlatMap => {
                RcIterator::dec_ref(iter_ref.source.flat_map.source);
                Closure::free(iter_ref.source.flat_map.transform as *mut Closure);
                let inner = iter_ref.source.flat_map.inner;
                if !inner.is_null() {
                    RcIterator::dec_ref(inner);
                }
            }
            IteratorKind::Unique => {
                RcIterator::dec_ref(iter_ref.source.unique.source);
            }
            IteratorKind::Chunks => {
                let elements = iter_ref.source.chunks.elements;
                if !elements.is_null() {
                    RcArray::dec_ref(elements);
                }
            }
            IteratorKind::Windows => {
                let elements = iter_ref.source.windows.elements;
                if !elements.is_null() {
                    RcArray::dec_ref(elements);
                }
            }
            IteratorKind::Repeat | IteratorKind::Once | IteratorKind::Empty => {}
            IteratorKind::FromFn => {
                Closure::free(iter_ref.source.from_fn.generator as *mut Closure);
            }
            IteratorKind::Range => {}
            IteratorKind::StringChars => {
                let string = iter_ref.source.string_chars.string;
                if !string.is_null() {
                    RcString::dec_ref(string as *mut RcString);
                }
            }
            IteratorKind::Interface => {
                // The boxed interface layout is [data_ptr, vtable_ptr].
                // We need to rc_dec the data_ptr (the actual instance) so the
                // underlying object (e.g., generator state machine) is freed.
                let boxed = iter_ref.source.interface.boxed_interface;
                if !boxed.is_null() {
                    let data_ptr = *(boxed as *const *mut u8);
                    if !data_ptr.is_null() {
                        rc_dec(data_ptr);
                    }
                    // Free the interface box itself (heap-allocated 2-word struct)
                    let layout = Layout::from_size_align(16, 8).unwrap();
                    dealloc(boxed as *mut u8, layout);
                }
            }
            IteratorKind::Enumerate => {
                RcIterator::dec_ref(iter_ref.source.enumerate.source);
            }
            IteratorKind::Zip => {
                RcIterator::dec_ref(iter_ref.source.zip.first);
                RcIterator::dec_ref(iter_ref.source.zip.second);
            }
            IteratorKind::StringSplit => {
                let string = iter_ref.source.string_split.string;
                let delimiter = iter_ref.source.string_split.delimiter;
                if !string.is_null() {
                    RcString::dec_ref(string as *mut RcString);
                }
                if !delimiter.is_null() {
                    RcString::dec_ref(delimiter as *mut RcString);
                }
            }
            IteratorKind::StringLines => {
                let string = iter_ref.source.string_lines.string;
                if !string.is_null() {
                    RcString::dec_ref(string as *mut RcString);
                }
            }
            IteratorKind::StringCodepoints => {
                let string = iter_ref.source.string_codepoints.string;
                if !string.is_null() {
                    RcString::dec_ref(string as *mut RcString);
                }
            }
        }
    }
}

/// Get next value from any iterator (array or map)
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
        IteratorKind::Interface => {
            // For interface iterators, call through the vtable
            vole_interface_iter_next(iter, out_value)
        }
        IteratorKind::Enumerate => {
            // For enumerate iterators, delegate to enumerate_next logic
            vole_enumerate_iter_next(iter, out_value)
        }
        IteratorKind::Zip => {
            // For zip iterators, delegate to zip_next logic
            vole_zip_iter_next(iter, out_value)
        }
        IteratorKind::StringSplit => {
            // For string split iterators, delegate to string_split_next logic
            vole_string_split_iter_next(iter, out_value)
        }
        IteratorKind::StringLines => {
            // For string lines iterators, delegate to string_lines_next logic
            vole_string_lines_iter_next(iter, out_value)
        }
        IteratorKind::StringCodepoints => {
            // For string codepoints iterators, delegate to string_codepoints_next logic
            vole_string_codepoints_iter_next(iter, out_value)
        }
    }
}

/// Get next value from interface iterator by calling through the vtable.
/// The boxed interface has layout: [data_ptr, vtable_ptr]
/// The vtable has method pointers, with next() at slot 0.
/// The next() wrapper returns a tagged union pointer.
/// Union variants are sorted descending: Primitive(T) > Done, so tag 0 = value, tag 1 = Done.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_interface_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &(*iter).iter };
    if iter_ref.kind != IteratorKind::Interface {
        return 0;
    }

    let interface_src = unsafe { iter_ref.source.interface };
    let boxed = interface_src.boxed_interface;
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
            *out_value = payload;
            1
        }
    }
}

/// Get next value from any iterator and return a tagged union pointer.
/// Layout: [tag:1][pad:7][payload:8].
/// Union variants are sorted descending: Primitive(T) > Done, so tag 0 = value, tag 1 = Done.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_next(iter: *mut RcIterator) -> *mut u8 {
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

    // Tag 0 = value, Tag 1 = Done (descending sort order)
    let tag = if has_value == 0 { 1u8 } else { 0u8 };
    unsafe {
        ptr::write(ptr, tag);
        let payload_ptr = ptr.add(8) as *mut i64;
        ptr::write(payload_ptr, if has_value == 0 { 0 } else { value });
    }

    ptr
}

/// Check if an iterator chain produces "owned" values (from map/string_chars/etc.)
/// vs "borrowed" values (from array source with only filter/take/skip in between).
/// This determines whether collect needs to rc_inc values before storing.
fn iter_produces_owned(iter: *mut RcIterator) -> bool {
    if iter.is_null() {
        return false;
    }
    unsafe {
        let kind = (*iter).iter.kind;
        match kind {
            // Creating sources: values are newly created (owned)
            IteratorKind::Map
            | IteratorKind::FlatMap
            | IteratorKind::StringChars
            | IteratorKind::StringSplit
            | IteratorKind::StringLines
            | IteratorKind::StringCodepoints
            | IteratorKind::Chunks
            | IteratorKind::Windows
            | IteratorKind::Enumerate
            | IteratorKind::Zip
            | IteratorKind::FromFn
            | IteratorKind::Repeat
            | IteratorKind::Once
            | IteratorKind::Range => true,

            // Pass-through sources: check what they pass through
            IteratorKind::Filter => iter_produces_owned((*iter).iter.source.filter.source),
            IteratorKind::Take => iter_produces_owned((*iter).iter.source.take.source),
            IteratorKind::Skip => iter_produces_owned((*iter).iter.source.skip.source),
            IteratorKind::Unique => iter_produces_owned((*iter).iter.source.unique.source),
            IteratorKind::Chain => {
                // Chain: both branches must produce owned for us to say owned
                // In practice, if either is borrowed, we need to rc_inc
                false
            }
            IteratorKind::Flatten => {
                // Flatten yields elements from inner arrays - these are borrowed
                false
            }

            // Leaf sources: values are borrowed from the source container
            IteratorKind::Array | IteratorKind::Empty => false,
            // Interface: next() is a function call that returns owned values
            IteratorKind::Interface => true,
        }
    }
}

/// Collect all remaining iterator values into a new array with proper element type tags.
/// `elem_tag` is the runtime type tag for the element type (e.g. TYPE_STRING, TYPE_INSTANCE).
/// This ensures the resulting array properly tracks RC types for cleanup.
/// Handles both "owned" values (from map/string_chars) and "borrowed" values (from array)
/// by rc_inc-ing borrowed RC values so the collected array properly owns them.
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_collect_tagged(iter: *mut RcIterator, elem_tag: u64) -> *mut RcArray {
    use crate::value::{TaggedValue, tag_needs_rc};

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    let needs_rc = tag_needs_rc(elem_tag);
    let values_owned = iter_produces_owned(iter);

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Determine the actual tag for this value.
        // The codegen-provided elem_tag may be wrong for type-transforming iterators
        // like Flatten (which reduces Array<T> to T). Use a pointer alignment check
        // to validate: all RC heap objects are 8-byte aligned, so if the value isn't
        // aligned, it can't be an RC pointer regardless of what the tag says.
        let actual_tag = if needs_rc && !(value as usize).is_multiple_of(8) {
            // Value is not a valid heap pointer - use tag 0 (non-RC)
            0u64
        } else {
            elem_tag
        };
        let actual_needs_rc = tag_needs_rc(actual_tag);

        // For borrowed RC values (from array source), rc_inc so the collected
        // array gets its own reference. For owned values (from map), the value
        // is already at refcount 1 from creation - just transfer ownership.
        if actual_needs_rc && !values_owned && value != 0 {
            rc_inc(value as *mut u8);
        }

        // Push to result array with correct element type tag.
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: actual_tag,
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    result
}

/// Collect all remaining iterator values into a new array
/// Returns pointer to newly allocated array (empty if iterator is null)
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

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
    RcIterator::dec_ref(iter);

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

/// Get next value from map iterator
/// Calls the source iterator's next, applies the transform function, returns result
/// Returns 1 and stores transformed value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_map_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &(*iter).iter };

    // This function should only be called for Map iterators
    // but vole_array_iter_next delegates here for Map kind
    if iter_ref.kind != IteratorKind::Map {
        return 0;
    }

    let map_src = unsafe { iter_ref.source.map };

    // Check if source values are owned RC values that need rc_dec after consumption.
    // The source iterator's elem_tag tells us the type of values it produces.
    // If the source produces owned RC values (from another map, string_chars, etc.),
    // we need to rc_dec them after the transform closure consumes them.
    let source_elem_tag = unsafe { (*map_src.source).elem_tag };
    let source_needs_rc_dec =
        crate::value::tag_needs_rc(source_elem_tag) && iter_produces_owned(map_src.source);

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

    // rc_dec the consumed source value if it was an owned RC value (from another map, etc.).
    // The closure has consumed the value (used it to produce the result).
    if source_needs_rc_dec && source_value != 0 {
        rc_dec(source_value as *mut u8);
    }

    1 // Has value
}

/// Collect all remaining map iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
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
    RcIterator::dec_ref(iter);

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

/// Get next value from filter iterator
/// Calls the source iterator's next, applies the predicate function, skips non-matching elements
/// Returns 1 and stores value in out_value if a matching element is found
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_filter_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &(*iter).iter };

    // This function should only be called for Filter iterators
    if iter_ref.kind != IteratorKind::Filter {
        return 0;
    }

    let filter_src = unsafe { iter_ref.source.filter };

    // Check if rejected values need rc_dec (source produces owned RC values)
    let elem_tag = unsafe { (*iter).elem_tag };
    let rc_dec_rejects =
        crate::value::tag_needs_rc(elem_tag) && iter_produces_owned(filter_src.source);

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
        // Rejected value: rc_dec if it's an owned RC value (from map/etc.)
        if rc_dec_rejects && source_value != 0 {
            rc_dec(source_value as *mut u8);
        }
    }
}

/// Collect all remaining filter iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
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
    RcIterator::dec_ref(iter);

    result
}

// =============================================================================
// Consumer methods - eager evaluation that consumes the entire iterator
// =============================================================================

/// Check if an iterator produces owned RC values that need to be freed when discarded.
/// Returns true if values from this iterator should be rc_dec'd when the consumer doesn't keep them.
fn iter_produces_owned_rc(iter: *mut RcIterator) -> bool {
    if iter.is_null() {
        return false;
    }
    let tag = unsafe { (*iter).elem_tag };
    crate::value::tag_needs_rc(tag) && iter_produces_owned(iter)
}

/// Returns true if the iterator produces borrowed RC values (i.e. values whose
/// elem_tag indicates they need RC but the iterator source doesn't own them).
/// Used by terminal methods (first, last, nth) to rc_inc the returned value
/// before freeing the iterator chain.
fn iter_produces_borrowed_rc(iter: *mut RcIterator) -> bool {
    if iter.is_null() {
        return false;
    }
    let tag = unsafe { (*iter).elem_tag };
    crate::value::tag_needs_rc(tag) && !iter_produces_owned(iter)
}

/// Count the number of elements in any iterator
/// Returns the count as i64
/// Frees the iterator after counting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_count(iter: *mut RcIterator) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let owned_rc = iter_produces_owned_rc(iter);
    let mut count: i64 = 0;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }
        // Free owned RC values that we're discarding (e.g., strings from string iteration)
        if owned_rc && value != 0 {
            rc_dec(value as *mut u8);
        }
        count += 1;
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    count
}

/// Sum all elements in any iterator (assumes i64 elements)
/// Returns the sum as i64
/// Frees the iterator after summing.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_sum(iter: *mut RcIterator) -> i64 {
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
    RcIterator::dec_ref(iter);

    sum
}

/// Call a function for each element in any iterator
/// The callback is a closure that takes one i64 argument and returns nothing
/// Frees the iterator after iteration.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_for_each(iter: *mut RcIterator, callback: *const Closure) {
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
    RcIterator::dec_ref(iter);

    // Free the callback closure (ownership transferred from codegen)
    unsafe { Closure::free(callback as *mut Closure) };
}

/// Reduce all elements in any iterator using an accumulator function, with RC cleanup.
/// `acc_tag` is the runtime type tag for the accumulator type.
/// `elem_tag` is the runtime type tag for the element type.
/// When the accumulator or element is an RC type, old values are properly decremented.
/// Returns the final accumulated value.
/// Frees the iterator after reduction.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_reduce_tagged(
    iter: *mut RcIterator,
    init: i64,
    reducer: *const Closure,
    acc_tag: u64,
    elem_tag: u64,
) -> i64 {
    use crate::value::tag_needs_rc;

    if iter.is_null() || reducer.is_null() {
        return init;
    }

    let acc_is_rc = tag_needs_rc(acc_tag);
    // Use the passed elem_tag to determine if elements need RC cleanup.
    // This is more reliable than checking the iterator's stored elem_tag,
    // which may be unset for interface iterators (generators).
    let elem_is_owned_rc = tag_needs_rc(elem_tag) && iter_produces_owned(iter);

    let mut acc = init;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Call the reducer closure with (acc, value) -> new_acc
        // All lambdas now use closure calling convention (closure ptr as first arg)
        let old_acc = acc;
        unsafe {
            let func_ptr = Closure::get_func(reducer);
            let reducer_fn: extern "C" fn(*const Closure, i64, i64) -> i64 =
                std::mem::transmute(func_ptr);
            acc = reducer_fn(reducer, old_acc, value);
        }

        // Decrement old accumulator if it's an RC type and changed
        if acc_is_rc && old_acc != acc && old_acc != 0 {
            rc_dec(old_acc as *mut u8);
        }
        // Free owned RC element values after the reducer has used them
        if elem_is_owned_rc && value != 0 {
            rc_dec(value as *mut u8);
        }
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    // Free the reducer closure (ownership transferred from codegen)
    unsafe { Closure::free(reducer as *mut Closure) };

    acc
}

/// Reduce all elements in any iterator using an accumulator function
/// Takes initial value and a reducer closure (acc, value) -> new_acc
/// Returns the final accumulated value
/// Frees the iterator after reduction.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_reduce(
    iter: *mut RcIterator,
    init: i64,
    reducer: *const Closure,
) -> i64 {
    // Delegate to the tagged version using the iterator's stored elem_tag.
    // For reduce, the accumulator type equals the element type (T),
    // so both acc_tag and elem_tag use the same value.
    let tag = if iter.is_null() {
        0
    } else {
        unsafe { (*iter).elem_tag }
    };
    vole_iter_reduce_tagged(iter, init, reducer, tag, tag)
}

/// Get the first element from any iterator, returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Note: For T?, variants are sorted by debug string. I64 < Nil alphabetically,
/// so tag 0 = I64 (value), tag 1 = Nil.
/// Frees the iterator after getting the first element.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_first(iter: *mut RcIterator) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() {
        // Return nil
        unsafe {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
        }
        return ptr;
    }

    let mut value: i64 = 0;
    let has_value = vole_array_iter_next(iter, &mut value);

    // rc_inc borrowed RC values before freeing the iterator chain so the
    // returned optional owns its payload.
    if has_value != 0 && iter_produces_borrowed_rc(iter) {
        rc_inc(value as *mut u8);
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    unsafe {
        if has_value != 0 {
            ptr::write(ptr, 0u8); // tag 0 = value present
            ptr::write(ptr.add(8) as *mut i64, value);
        } else {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
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
pub extern "C" fn vole_iter_last(iter: *mut RcIterator) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() {
        // Return nil
        unsafe {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
        }
        return ptr;
    }

    let owned_rc = iter_produces_owned_rc(iter);
    let borrowed_rc = iter_produces_borrowed_rc(iter);
    let mut last_value: i64 = 0;
    let mut found_any = false;

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }
        // Free the previous "last" value if it was an owned RC value
        if owned_rc && found_any && last_value != 0 {
            rc_dec(last_value as *mut u8);
        }
        last_value = value;
        found_any = true;
    }

    // rc_inc borrowed RC values before freeing the iterator chain so the
    // returned optional owns its payload.
    if found_any && borrowed_rc && last_value != 0 {
        rc_inc(last_value as *mut u8);
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    unsafe {
        if found_any {
            ptr::write(ptr, 0u8); // tag 0 = value present
            ptr::write(ptr.add(8) as *mut i64, last_value);
        } else {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
        }
    }

    ptr
}

/// Get the nth element from any iterator (0-indexed), returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the nth element.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_nth(iter: *mut RcIterator, n: i64) -> *mut u8 {
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if iter.is_null() || n < 0 {
        // Return nil for null iterator or negative index
        unsafe {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
        }
        if !iter.is_null() {
            RcIterator::dec_ref(iter);
        }
        return ptr;
    }

    let owned_rc = iter_produces_owned_rc(iter);
    let borrowed_rc = iter_produces_borrowed_rc(iter);

    // Skip n elements
    for _ in 0..n {
        let mut dummy: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut dummy);
        if has_value == 0 {
            // Iterator exhausted before reaching nth element
            RcIterator::dec_ref(iter);
            unsafe {
                ptr::write(ptr, 1u8); // tag 1 = nil
                ptr::write(ptr.add(8) as *mut i64, 0);
            }
            return ptr;
        }
        // Free skipped owned RC values
        if owned_rc && dummy != 0 {
            rc_dec(dummy as *mut u8);
        }
    }

    // Get the nth element
    let mut value: i64 = 0;
    let has_value = vole_array_iter_next(iter, &mut value);

    // rc_inc borrowed RC values before freeing the iterator chain so the
    // returned optional owns its payload.
    if has_value != 0 && borrowed_rc && value != 0 {
        rc_inc(value as *mut u8);
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    unsafe {
        if has_value != 0 {
            ptr::write(ptr, 0u8); // tag 0 = value present
            ptr::write(ptr.add(8) as *mut i64, value);
        } else {
            ptr::write(ptr, 1u8); // tag 1 = nil
            ptr::write(ptr.add(8) as *mut i64, 0);
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

/// Get next value from take iterator
/// Returns 1 and stores value in out_value if available (and remaining > 0)
/// Returns 0 if remaining is 0 or source iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_take_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
    RcIterator::dec_ref(iter);

    result
}

// =============================================================================
// SkipIterator - lazy skip of first n elements
// =============================================================================

/// Create a new skip iterator wrapping any source iterator
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_skip_iter(source: *mut RcIterator, count: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Skip,
        IteratorSource {
            skip: SkipSource {
                source,
                skip_count: count,
                skipped: 0, // Not yet skipped
            },
        },
    )
}

/// Get next value from skip iterator
/// On first call, skips skip_count elements, then returns remaining elements
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_skip_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

    // This function should only be called for Skip iterators
    if iter_ref.kind != IteratorKind::Skip {
        return 0;
    }

    let skip_src = unsafe { &mut iter_ref.source.skip };

    // If we haven't skipped yet, do the initial skip
    if skip_src.skipped == 0 {
        skip_src.skipped = 1;
        let owned_rc = iter_produces_owned_rc(skip_src.source);
        let mut skipped: i64 = 0;
        while skipped < skip_src.skip_count {
            let mut dummy: i64 = 0;
            let has_value = vole_array_iter_next(skip_src.source, &mut dummy);
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
    vole_array_iter_next(skip_src.source, out_value)
}

/// Collect all remaining skip iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
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
    RcIterator::dec_ref(iter);

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
            RcIterator::dec_ref(iter);
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
            RcIterator::dec_ref(iter);

            unsafe {
                ptr::write(ptr, 0u8); // tag 0 = value present
                ptr::write(ptr.add(8) as *mut i64, value);
            }
            return ptr;
        }
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

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
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_any(iter: *mut RcIterator, predicate: *const Closure) -> i8 {
    if iter.is_null() || predicate.is_null() {
        if !iter.is_null() {
            RcIterator::dec_ref(iter);
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
            RcIterator::dec_ref(iter);
            return 1; // true
        }
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

    0 // false - no element matched
}

/// Check if all elements match a predicate, returns bool
/// Short-circuits on first false.
/// Frees the iterator after checking.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_all(iter: *mut RcIterator, predicate: *const Closure) -> i8 {
    if iter.is_null() || predicate.is_null() {
        if !iter.is_null() {
            RcIterator::dec_ref(iter);
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
            RcIterator::dec_ref(iter);
            return 0; // false
        }
    }

    // Free the iterator chain
    RcIterator::dec_ref(iter);

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
    first: *mut RcIterator,
    second: *mut RcIterator,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Chain,
        IteratorSource {
            chain: ChainSource {
                first,
                second,
                on_second: 0, // Start with first iterator
            },
        },
    )
}

/// Get next value from chain iterator
/// First exhausts the first iterator, then yields from the second
/// Returns 1 and stores value in out_value if available
/// Returns 0 if both iterators exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chain_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
    RcIterator::dec_ref(iter);

    result
}

// =============================================================================
// FlattenIterator - lazy flattening of nested iterables
// =============================================================================

/// Create a new flatten iterator wrapping any source iterator that yields arrays
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flatten_iter(source: *mut RcIterator) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Flatten,
        IteratorSource {
            flatten: FlattenSource {
                outer: source,
                inner: ptr::null_mut(),
            },
        },
    )
}

/// Get next value from flatten iterator
/// Yields elements from each inner array until all are exhausted
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flatten_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
            RcIterator::dec_ref(flatten_src.inner);
            flatten_src.inner = ptr::null_mut();
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
pub extern "C" fn vole_flatten_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

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
    RcIterator::dec_ref(iter);

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

/// Get next value from flat_map iterator
/// Applies transform to each source element, then yields elements from resulting arrays
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_flat_map_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
            RcIterator::dec_ref(flat_map_src.inner);
            flat_map_src.inner = ptr::null_mut();
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

        // Create an iterator for the resulting array.
        // vole_array_iter rc_inc's the array (for user arrays).
        // The transform created this array (refcount 1), so dec_ref after wrapping
        // to transfer sole ownership to the inner iterator.
        let inner_array = array_ptr as *mut RcArray;
        flat_map_src.inner = vole_array_iter(inner_array);
        unsafe { RcArray::dec_ref(inner_array) };
        // Continue loop to get first element from this inner iterator
    }
}

/// Collect all remaining flat_map iterator values into a new array
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
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
    RcIterator::dec_ref(iter);

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
    RcIterator::dec_ref(iter);

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
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
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
    RcIterator::dec_ref(iter);

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
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_unique_iter(source: *mut RcIterator) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Unique,
        IteratorSource {
            unique: UniqueSource {
                source,
                prev: 0,
                has_prev: 0,
            },
        },
    )
}

/// Get next value from unique iterator
/// Skips consecutive duplicate values
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_unique_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
pub extern "C" fn vole_chunks_iter(source: *mut RcIterator, chunk_size: i64) -> *mut RcIterator {
    use crate::value::TaggedValue;

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
        RcIterator::dec_ref(source);
    } else if !source.is_null() {
        // Free the source even if chunk_size <= 0
        RcIterator::dec_ref(source);
    }

    RcIterator::new(
        IteratorKind::Chunks,
        IteratorSource {
            chunks: ChunksSource {
                elements,
                chunk_size: if chunk_size > 0 { chunk_size } else { 1 },
                position: 0,
            },
        },
    )
}

/// Get next chunk from chunks iterator
/// Returns 1 and stores array pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_chunks_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    use crate::value::TaggedValue;

    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
pub extern "C" fn vole_chunks_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

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
    RcIterator::dec_ref(iter);

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
pub extern "C" fn vole_windows_iter(source: *mut RcIterator, window_size: i64) -> *mut RcIterator {
    use crate::value::TaggedValue;

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
        RcIterator::dec_ref(source);
    } else if !source.is_null() {
        // Free the source even if window_size <= 0
        RcIterator::dec_ref(source);
    }

    RcIterator::new(
        IteratorKind::Windows,
        IteratorSource {
            windows: WindowsSource {
                elements,
                window_size: if window_size > 0 { window_size } else { 1 },
                position: 0,
            },
        },
    )
}

/// Get next window from windows iterator
/// Returns 1 and stores array pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_windows_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    use crate::value::TaggedValue;

    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
pub extern "C" fn vole_windows_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

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
    RcIterator::dec_ref(iter);

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
pub extern "C" fn vole_repeat_iter(value: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Repeat,
        IteratorSource {
            repeat: RepeatSource { value },
        },
    )
}

/// Get next value from repeat iterator
/// Always returns 1 with the same value (infinite iterator)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_repeat_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &(*iter).iter };

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
pub extern "C" fn vole_once_iter(value: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Once,
        IteratorSource {
            once: OnceSource {
                value,
                exhausted: 0,
            },
        },
    )
}

/// Get next value from once iterator
/// Returns 1 with the value on first call, 0 on subsequent calls
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_once_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
pub extern "C" fn vole_empty_iter() -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Empty,
        IteratorSource {
            empty: EmptySource { _placeholder: 0 },
        },
    )
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
pub extern "C" fn vole_from_fn_iter(generator: *const Closure) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::FromFn,
        IteratorSource {
            from_fn: FromFnSource { generator },
        },
    )
}

/// Get next value from from_fn iterator
/// Calls the generator function - returns 1 with value if not nil, 0 if nil
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_from_fn_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &(*iter).iter };

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
        let tag = ptr::read(result_ptr);
        let payload_ptr = result_ptr.add(8) as *const i64;
        let payload = ptr::read(payload_ptr);

        // Free the result (it was allocated by the generator)
        let layout = Layout::from_size_align(16, 8).expect("valid layout");
        dealloc(result_ptr, layout);

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
pub extern "C" fn vole_range_iter(start: i64, end: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Range,
        IteratorSource {
            range: RangeSource {
                current: start,
                end,
            },
        },
    )
}

/// Get next value from range iterator
/// Returns 1 with the value if current < end, 0 if done
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_range_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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
pub extern "C" fn vole_string_chars_iter(string: *const RcString) -> *mut RcIterator {
    // Increment ref count on string so it stays alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
    }

    RcIterator::new(
        IteratorKind::StringChars,
        IteratorSource {
            string_chars: StringCharsSource {
                string,
                byte_pos: 0,
            },
        },
    )
}

/// Get next character from string chars iterator
/// Returns 1 and stores the character string pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_chars_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

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

// =============================================================================
// EnumerateIterator - yields (index, value) pairs
// =============================================================================

/// Create a new enumerate iterator that wraps any source iterator and yields (index, value) tuples.
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_enumerate_iter(source: *mut RcIterator) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Enumerate,
        IteratorSource {
            enumerate: EnumerateSource { source, index: 0 },
        },
    )
}

/// Get next (index, value) tuple from enumerate iterator.
/// Returns 1 and stores tuple pointer in out_value if available.
/// Returns 0 if iterator exhausted (Done).
/// The tuple layout is: [index:i64][value:i64] (16 bytes total, 8-byte aligned)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_enumerate_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

    if iter_ref.kind != IteratorKind::Enumerate {
        return 0;
    }

    let enum_src = unsafe { &mut iter_ref.source.enumerate };

    // Get next value from source iterator
    let mut source_value: i64 = 0;
    let has_value = vole_array_iter_next(enum_src.source, &mut source_value);

    if has_value == 0 {
        return 0; // Source exhausted
    }

    // Allocate tuple: (i64, T) where T is also i64 for simplicity
    // Layout: [index:8][value:8] = 16 bytes
    let layout = Layout::from_size_align(16, 8).expect("valid tuple layout");
    let tuple_ptr = unsafe { alloc(layout) };
    if tuple_ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Write index and value to tuple
    unsafe {
        ptr::write(tuple_ptr as *mut i64, enum_src.index);
        ptr::write((tuple_ptr as *mut i64).add(1), source_value);
    }

    // Increment index for next call
    enum_src.index += 1;

    // Return tuple pointer
    unsafe { *out_value = tuple_ptr as i64 };
    1 // Has value
}

// =============================================================================
// ZipIterator - combines two iterators into (a, b) pairs
// =============================================================================

/// Create a new zip iterator that combines two iterators.
/// Stops when either iterator is exhausted.
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_zip_iter(
    first: *mut RcIterator,
    second: *mut RcIterator,
) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Zip,
        IteratorSource {
            zip: ZipSource { first, second },
        },
    )
}

/// Get next (a, b) tuple from zip iterator.
/// Returns 1 and stores tuple pointer in out_value if both iterators have values.
/// Returns 0 if either iterator is exhausted (Done).
/// The tuple layout is: [first:i64][second:i64] (16 bytes total, 8-byte aligned)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_zip_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

    if iter_ref.kind != IteratorKind::Zip {
        return 0;
    }

    let zip_src = unsafe { &mut iter_ref.source.zip };

    // Get next value from first iterator
    let mut first_value: i64 = 0;
    let has_first = vole_array_iter_next(zip_src.first, &mut first_value);

    if has_first == 0 {
        return 0; // First iterator exhausted
    }

    // Get next value from second iterator
    let mut second_value: i64 = 0;
    let has_second = vole_array_iter_next(zip_src.second, &mut second_value);

    if has_second == 0 {
        return 0; // Second iterator exhausted
    }

    // Allocate tuple: (T, U) where both are i64 for simplicity
    // Layout: [first:8][second:8] = 16 bytes
    let layout = Layout::from_size_align(16, 8).expect("valid tuple layout");
    let tuple_ptr = unsafe { alloc(layout) };
    if tuple_ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Write values to tuple
    unsafe {
        ptr::write(tuple_ptr as *mut i64, first_value);
        ptr::write((tuple_ptr as *mut i64).add(1), second_value);
    }

    // Return tuple pointer
    unsafe { *out_value = tuple_ptr as i64 };
    1 // Has value
}

// =============================================================================
// StringSplitIterator - splits string by delimiter
// =============================================================================

/// Create a new string split iterator that yields substrings split by delimiter
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_split_iter(
    string: *const RcString,
    delimiter: *const RcString,
) -> *mut RcIterator {
    // Increment ref count on strings so they stay alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
        if !delimiter.is_null() {
            RcString::inc_ref(delimiter as *mut RcString);
        }
    }

    RcIterator::new(
        IteratorKind::StringSplit,
        IteratorSource {
            string_split: StringSplitSource {
                string,
                delimiter,
                byte_pos: 0,
                exhausted: 0,
            },
        },
    )
}

/// Get next substring from string split iterator
/// Returns 1 and stores the substring pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_split_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

    if iter_ref.kind != IteratorKind::StringSplit {
        return 0;
    }

    let split_src = unsafe { &mut iter_ref.source.string_split };

    if split_src.string.is_null() || split_src.exhausted != 0 {
        return 0;
    }

    unsafe {
        let string_ref = &*split_src.string;
        let delim_ref = if split_src.delimiter.is_null() {
            ""
        } else {
            (*split_src.delimiter).as_str()
        };

        let byte_len = string_ref.len as i64;

        // Check if we've exhausted the string
        if split_src.byte_pos > byte_len {
            return 0;
        }

        // Get the string data starting at current byte position
        let data = string_ref.data();
        let remaining = &data[split_src.byte_pos as usize..];

        // Safety: RcString stores valid UTF-8
        let remaining_str = std::str::from_utf8_unchecked(remaining);

        // Find the next delimiter
        if let Some(delim_pos) = remaining_str.find(delim_ref) {
            // Found delimiter - yield substring before it
            let substring = &remaining_str[..delim_pos];
            let new_string = RcString::new(substring);

            // Update byte position to after the delimiter
            split_src.byte_pos += delim_pos as i64 + delim_ref.len() as i64;

            *out_value = new_string as i64;
            1 // Has value
        } else {
            // No more delimiters - yield remaining string and mark exhausted
            let new_string = RcString::new(remaining_str);
            split_src.exhausted = 1;

            *out_value = new_string as i64;
            1 // Has value
        }
    }
}

// =============================================================================
// StringLinesIterator - splits string by newlines
// =============================================================================

/// Create a new string lines iterator that yields lines (split by \n or \r\n)
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_lines_iter(string: *const RcString) -> *mut RcIterator {
    // Increment ref count on string so it stays alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
    }

    RcIterator::new(
        IteratorKind::StringLines,
        IteratorSource {
            string_lines: StringLinesSource {
                string,
                byte_pos: 0,
                exhausted: 0,
            },
        },
    )
}

/// Get next line from string lines iterator
/// Returns 1 and stores the line pointer in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_lines_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

    if iter_ref.kind != IteratorKind::StringLines {
        return 0;
    }

    let lines_src = unsafe { &mut iter_ref.source.string_lines };

    if lines_src.string.is_null() || lines_src.exhausted != 0 {
        return 0;
    }

    unsafe {
        let string_ref = &*lines_src.string;
        let byte_len = string_ref.len as i64;

        // Check if we've exhausted the string
        if lines_src.byte_pos > byte_len {
            return 0;
        }

        // Get the string data starting at current byte position
        let data = string_ref.data();
        let remaining = &data[lines_src.byte_pos as usize..];

        // Safety: RcString stores valid UTF-8
        let remaining_str = std::str::from_utf8_unchecked(remaining);

        // Find the next newline
        if let Some(newline_pos) = remaining_str.find('\n') {
            // Check for \r\n (Windows line endings)
            let line_end = if newline_pos > 0
                && remaining_str.as_bytes().get(newline_pos - 1) == Some(&b'\r')
            {
                newline_pos - 1
            } else {
                newline_pos
            };

            let line = &remaining_str[..line_end];
            let new_string = RcString::new(line);

            // Update byte position to after the newline
            lines_src.byte_pos += newline_pos as i64 + 1;

            *out_value = new_string as i64;
            1 // Has value
        } else {
            // No more newlines - yield remaining string and mark exhausted
            // But only if there's content (don't yield empty string at end)
            if remaining_str.is_empty() {
                return 0;
            }

            // Strip trailing \r if present
            let line = remaining_str.strip_suffix('\r').unwrap_or(remaining_str);
            let new_string = RcString::new(line);
            lines_src.exhausted = 1;

            *out_value = new_string as i64;
            1 // Has value
        }
    }
}

// =============================================================================
// StringCodepointsIterator - yields unicode codepoints as i32
// =============================================================================

/// Create a new string codepoints iterator that yields unicode codepoints as i32
/// Returns pointer to heap-allocated iterator
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_codepoints_iter(string: *const RcString) -> *mut RcIterator {
    // Increment ref count on string so it stays alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
    }

    RcIterator::new(
        IteratorKind::StringCodepoints,
        IteratorSource {
            string_codepoints: StringCodepointsSource {
                string,
                byte_pos: 0,
            },
        },
    )
}

/// Get next codepoint from string codepoints iterator
/// Returns 1 and stores the codepoint (as i32) in out_value if available
/// Returns 0 if iterator exhausted (Done)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_codepoints_iter_next(
    iter: *mut RcIterator,
    out_value: *mut i64,
) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let iter_ref = unsafe { &mut (*iter).iter };

    if iter_ref.kind != IteratorKind::StringCodepoints {
        return 0;
    }

    let codepoints_src = unsafe { &mut iter_ref.source.string_codepoints };

    if codepoints_src.string.is_null() {
        return 0;
    }

    unsafe {
        let string_ref = &*codepoints_src.string;
        let byte_len = string_ref.len as i64;

        // Check if we've exhausted the string
        if codepoints_src.byte_pos >= byte_len {
            return 0; // Done
        }

        // Get the string data starting at current byte position
        let data = string_ref.data();
        let remaining = &data[codepoints_src.byte_pos as usize..];

        // Get the next UTF-8 character
        // Safety: RcString stores valid UTF-8
        let remaining_str = std::str::from_utf8_unchecked(remaining);
        let next_char = remaining_str.chars().next();

        if let Some(ch) = next_char {
            // Get the byte length of this character
            let char_len = ch.len_utf8();

            // Update byte position
            codepoints_src.byte_pos += char_len as i64;

            // Return the codepoint as i32 (cast to i64 for storage)
            *out_value = ch as i32 as i64;
            1 // Has value
        } else {
            0 // Done - should not happen if byte_pos < byte_len
        }
    }
}
