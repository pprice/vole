//! Iterator runtime support
//!
//! Provides runtime representation for iterators.
//! Uses a unified IteratorSource enum to support chaining (e.g., map().map()).
//!
//! # Iterator Kind Definitions
//!
//! All iterator kinds are defined in one place using the `for_all_iterator_kinds!` macro.
//! This ensures that drop logic, next dispatch, and ownership inference stay in sync.
//! When adding a new iterator kind:
//! 1. Add it to `for_all_iterator_kinds!` with its properties
//! 2. Add the corresponding `*Source` struct
//! 3. Add the union field to `IteratorSource`
//! 4. Implement the `vole_*_iter_next` function
//!
//! The macro will automatically generate the enum variant, drop logic, next dispatch,
//! and ownership inference based on the provided properties.

use crate::alloc_track;
use crate::array::RcArray;
use crate::closure::Closure;
use crate::iterator_abi::{NextTag, TaggedNextWord};
use crate::iterator_core::CoreIter;
use crate::string::RcString;
use crate::value::{RcHeader, TYPE_ITERATOR, TYPE_STRING, rc_dec, rc_inc, tag_needs_rc};
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

// =============================================================================
// Central Iterator Kind Definitions
// =============================================================================
//
// This macro is the SINGLE SOURCE OF TRUTH for all iterator kinds.
// It invokes a callback macro with all iterator information.
//
// Format for each kind:
//   $kind:ident = $discriminant:literal,
//   source: $source_field:ident,
//   next: $next_fn:ident,
//   owned: $owned:tt,
//   drop: { $($drop_logic:tt)* }
//
// The `owned` field can be:
//   - `true`  : always produces owned values
//   - `false` : always produces borrowed values
//   - `passthrough($source_accessor:expr)` : recurse on source iterator
//
// The `drop` block contains the unsafe code to release resources.
// It has access to `iter_ref.source.$source_field` for the source data.

/// Invokes the callback macro for each iterator kind with its properties.
/// This is the single source of truth for iterator kind definitions.
///
/// # Adding a New Iterator Kind
///
/// When adding a new iterator kind, you must:
/// 1. Add it here with: discriminant, source field name, next function, and owned behavior
/// 2. Add a corresponding `*Source` struct
/// 3. Add a union field to `IteratorSource`
/// 4. Implement the `vole_*_iter_next` function
/// 5. Add a drop arm to `drop_iter_source!` macro below
///
/// The compiler will catch missing cases via exhaustive matching.
macro_rules! for_all_iterator_kinds {
    ($callback:ident) => {
        $callback! {
            // Leaf sources: values are borrowed from the source container
            Array = 0, source: array, next: vole_array_iter_next_impl, owned: [false];
            // Transform iterators with closure
            Map = 1, source: map, next: vole_map_iter_next, owned: [true];
            // Pass-through iterators: ownership depends on source
            Filter = 2, source: filter, next: vole_filter_iter_next, owned: [passthrough(filter.source)];
            Take = 3, source: take, next: vole_take_iter_next, owned: [passthrough(take.source)];
            Skip = 4, source: skip, next: vole_skip_iter_next, owned: [passthrough(skip.source)];
            // Dual source iterators
            Chain = 5, source: chain, next: vole_chain_iter_next, owned: [false];
            // Flatten yields borrowed elements from inner arrays. When the outer
            // is chunks/windows, flatten_next rc_inc's RC elements because inner
            // arrays are freed on exhaustion.
            Flatten = 6, source: flatten, next: vole_flatten_iter_next, owned: [false];
            FlatMap = 7, source: flat_map, next: vole_flat_map_iter_next, owned: [true];
            Unique = 8, source: unique, next: vole_unique_iter_next, owned: [passthrough(unique.source)];
            // Collected element iterators
            Chunks = 9, source: chunks, next: vole_chunks_iter_next, owned: [true];
            Windows = 10, source: windows, next: vole_windows_iter_next, owned: [true];
            // Value-producing iterators (no resources to free)
            Repeat = 11, source: repeat, next: vole_repeat_iter_next, owned: [true];
            Once = 12, source: once, next: vole_once_iter_next, owned: [true];
            Empty = 13, source: empty, next: vole_empty_iter_next, owned: [false];
            // Generator iterators
            FromFn = 14, source: from_fn, next: vole_from_fn_iter_next, owned: [true];
            Range = 15, source: range, next: vole_range_iter_next, owned: [true];
            // String iterators
            StringChars = 16, source: string_chars, next: vole_string_chars_iter_next, owned: [true];
            // Interface iterator - wraps a boxed interface implementing Iterator
            Interface = 17, source: interface, next: vole_interface_iter_next, owned: [true];
            // Enumerate iterator - yields (index, value) pairs
            Enumerate = 18, source: enumerate, next: vole_enumerate_iter_next, owned: [true];
            // Zip iterator - combines two iterators into pairs
            Zip = 19, source: zip, next: vole_zip_iter_next, owned: [true];
            // String split iterator - splits string by delimiter
            StringSplit = 20, source: string_split, next: vole_string_split_iter_next, owned: [true];
            // String lines iterator - splits string by newlines
            StringLines = 21, source: string_lines, next: vole_string_lines_iter_next, owned: [true];
            // String codepoints iterator - yields unicode codepoints as i32
            StringCodepoints = 22, source: string_codepoints, next: vole_string_codepoints_iter_next, owned: [true];
        }
    };
}

/// Generate the IteratorKind enum from the central definitions.
macro_rules! generate_iterator_kind_enum {
    ($(
        $kind:ident = $discriminant:literal,
        source: $source_field:ident,
        next: $next_fn:ident,
        owned: [ $($owned:tt)* ];
    )*) => {
        /// Enum discriminant for iterator sources
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum IteratorKind {
            $($kind = $discriminant,)*
        }
    };
}

for_all_iterator_kinds!(generate_iterator_kind_enum);

/// Helper macro to perform drop logic for each kind.
/// This macro exists to avoid hygiene issues with expanding drop code
/// that references `iter_ref` from within the callback pattern.
macro_rules! drop_iter_source {
    (Array, $iter_ref:expr) => {
        let array = $iter_ref.source.array.array;
        if !array.is_null() {
            RcArray::dec_ref(array as *mut RcArray);
        }
    };
    (Map, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.map.source);
        Closure::free($iter_ref.source.map.transform as *mut Closure);
    };
    (Filter, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.filter.source);
        Closure::free($iter_ref.source.filter.predicate as *mut Closure);
    };
    (Take, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.take.source);
    };
    (Skip, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.skip.source);
    };
    (Chain, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.chain.first);
        RcIterator::dec_ref($iter_ref.source.chain.second);
    };
    (Flatten, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.flatten.outer);
        let inner = $iter_ref.source.flatten.inner;
        if !inner.is_null() {
            RcIterator::dec_ref(inner);
        }
    };
    (FlatMap, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.flat_map.source);
        Closure::free($iter_ref.source.flat_map.transform as *mut Closure);
        let inner = $iter_ref.source.flat_map.inner;
        if !inner.is_null() {
            RcIterator::dec_ref(inner);
        }
    };
    (Unique, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.unique.source);
    };
    (Chunks, $iter_ref:expr) => {
        let elements = $iter_ref.source.chunks.elements;
        if !elements.is_null() {
            RcArray::dec_ref(elements);
        }
    };
    (Windows, $iter_ref:expr) => {
        let elements = $iter_ref.source.windows.elements;
        if !elements.is_null() {
            RcArray::dec_ref(elements);
        }
    };
    (Repeat, $iter_ref:expr) => {};
    (Once, $iter_ref:expr) => {};
    (Empty, $iter_ref:expr) => {};
    (FromFn, $iter_ref:expr) => {
        Closure::free($iter_ref.source.from_fn.generator as *mut Closure);
    };
    (Range, $iter_ref:expr) => {};
    (StringChars, $iter_ref:expr) => {
        let string = $iter_ref.source.string_chars.string;
        if !string.is_null() {
            RcString::dec_ref(string as *mut RcString);
        }
    };
    (Interface, $iter_ref:expr) => {
        // rc_dec the data_ptr (releases the iterator's own reference,
        // acquired via rc_inc in vole_interface_iter). Do NOT dealloc
        // the boxed interface - the JIT scope cleanup still holds the
        // box pointer and will read data_ptr from it for its own rc_dec.
        let boxed = $iter_ref.source.interface.boxed_interface;
        if !boxed.is_null() {
            let data_ptr = *(boxed as *const *mut u8);
            if !data_ptr.is_null() {
                rc_dec(data_ptr);
            }
        }
    };
    (Enumerate, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.enumerate.source);
    };
    (Zip, $iter_ref:expr) => {
        RcIterator::dec_ref($iter_ref.source.zip.first);
        RcIterator::dec_ref($iter_ref.source.zip.second);
    };
    (StringSplit, $iter_ref:expr) => {
        let string = $iter_ref.source.string_split.string;
        let delimiter = $iter_ref.source.string_split.delimiter;
        if !string.is_null() {
            RcString::dec_ref(string as *mut RcString);
        }
        if !delimiter.is_null() {
            RcString::dec_ref(delimiter as *mut RcString);
        }
    };
    (StringLines, $iter_ref:expr) => {
        let string = $iter_ref.source.string_lines.string;
        if !string.is_null() {
            RcString::dec_ref(string as *mut RcString);
        }
    };
    (StringCodepoints, $iter_ref:expr) => {
        let string = $iter_ref.source.string_codepoints.string;
        if !string.is_null() {
            RcString::dec_ref(string as *mut RcString);
        }
    };
}

/// Generate the iterator_drop_sources match arms from the central definitions.
macro_rules! generate_drop_sources {
    ($(
        $kind:ident = $discriminant:literal,
        source: $source_field:ident,
        next: $next_fn:ident,
        owned: [ $($owned:tt)* ];
    )*) => {
        /// Release resources owned by an iterator's source (without freeing the iterator itself).
        ///
        /// # Safety
        /// `iter_ref` must reference a valid `UnifiedIterator`. Union accesses are gated by `kind`.
        fn iterator_drop_sources(iter_ref: &UnifiedIterator) {
            // Safety: all union field accesses are gated by the kind discriminant.
            unsafe {
                match iter_ref.kind {
                    $(IteratorKind::$kind => { drop_iter_source!($kind, iter_ref); })*
                }
            }
        }
    };
}

/// Generate the vole_array_iter_next dispatch match from the central definitions.
macro_rules! generate_next_dispatch {
    ($(
        $kind:ident = $discriminant:literal,
        source: $source_field:ident,
        next: $next_fn:ident,
        owned: [ $($owned:tt)* ];
    )*) => {
        /// Get next value from any iterator (array or map)
        /// Returns 1 and stores value in out_value if available
        /// Returns 0 if iterator exhausted (Done)
        #[unsafe(no_mangle)]
        pub extern "C" fn vole_array_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
            if iter.is_null() {
                return 0;
            }
            let iter_ref = unsafe { &mut (*iter).iter };
            match iter_ref.kind {
                $(IteratorKind::$kind => $next_fn(iter, out_value),)*
            }
        }
    };
}

/// Helper macro to compute produces_owned for a single owned specification.
/// Note: This is always called within an unsafe block, so pointer dereferences are allowed.
macro_rules! compute_produces_owned {
    // Literal true/false
    (true, $iter:expr) => {
        true
    };
    (false, $iter:expr) => {
        false
    };
    // Passthrough: recurse on source (caller already in unsafe block)
    (passthrough($source_accessor:ident . $field:ident), $iter:expr) => {
        iter_produces_owned((*$iter).iter.source.$source_accessor.$field)
    };
}

/// Generate the iter_produces_owned function from the central definitions.
macro_rules! generate_produces_owned {
    ($(
        $kind:ident = $discriminant:literal,
        source: $source_field:ident,
        next: $next_fn:ident,
        owned: [ $($owned:tt)+ ];
    )*) => {
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
                    $(IteratorKind::$kind => compute_produces_owned!($($owned)+, iter),)*
                }
            }
        }
    };
}

/// Helper macro for defining iterator next functions.
///
/// This macro standardizes the common boilerplate for `vole_*_iter_next` functions:
/// - Null check on the iterator pointer
/// - Kind check to ensure we're operating on the correct iterator type
/// - Access to the typed source data
///
/// # Usage
///
/// ```rust,ignore
/// iter_next_fn!(
///     /// Optional doc comments
///     filter, Filter, filter, mut |src, iter, out_value| {
///         // src: &mut FilterSource
///         // iter: *mut RcIterator (the outer iterator pointer)
///         // out_value: *mut i64 (where to store the result)
///         // Returns i64 (1 for has value, 0 for done)
///     }
/// );
/// ```
///
/// The `mut` modifier indicates whether the source needs mutable access.
/// Without `mut`, the source is borrowed immutably.
macro_rules! iter_next_fn {
    // Mutable source access variant
    (
        $(#[$attr:meta])*
        $name:ident, $kind:ident, $source_field:ident, mut |$src:ident, $iter:ident, $out:ident| $body:block
    ) => {
        $(#[$attr])*
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
            if iter.is_null() {
                return 0;
            }

            let iter_ref = unsafe { &mut (*iter).iter };

            if iter_ref.kind != IteratorKind::$kind {
                return 0;
            }

            let $src = unsafe { &mut iter_ref.source.$source_field };
            let $iter = iter;
            let $out = out_value;
            $body
        }
    };
    // Immutable source access variant
    (
        $(#[$attr:meta])*
        $name:ident, $kind:ident, $source_field:ident, |$src:ident, $iter:ident, $out:ident| $body:block
    ) => {
        $(#[$attr])*
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
            if iter.is_null() {
                return 0;
            }

            let iter_ref = unsafe { &(*iter).iter };

            if iter_ref.kind != IteratorKind::$kind {
                return 0;
            }

            let $src = unsafe { iter_ref.source.$source_field };
            let $iter = iter;
            let $out = out_value;
            $body
        }
    };
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
    /// Pointer to source iterator (could be an array iterator or another map iterator)
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
    /// Whether we've done the initial skip
    pub skipped: bool,
}

/// Source data for chain iteration (concatenates two iterators)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ChainSource {
    /// First iterator to consume
    pub first: *mut RcIterator,
    /// Second iterator to consume after first is exhausted
    pub second: *mut RcIterator,
    /// Whether we've exhausted the first iterator
    pub on_second: bool,
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
    /// Whether we've seen the first element
    pub has_prev: bool,
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
    /// Element type tag for inner elements (e.g. TYPE_F64 for [f64] chunks)
    pub inner_elem_tag: u64,
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
    /// Element type tag for inner elements (e.g. TYPE_F64 for [f64] windows)
    pub inner_elem_tag: u64,
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
    /// Whether the value has been yielded
    pub exhausted: bool,
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
    /// Whether the iterator is exhausted
    pub exhausted: bool,
}

/// Source data for string lines iteration (splits string by newlines)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct StringLinesSource {
    /// Pointer to the source string
    pub string: *const RcString,
    /// Current byte position in the string (not character position)
    pub byte_pos: i64,
    /// Whether the iterator is exhausted
    pub exhausted: bool,
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
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcIterator`.
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }

    /// Set the element type tag on this iterator (non-recursive).
    /// Each iterator in the chain stores its OWN element type tag.
    /// The tag represents the type of values this iterator produces.
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
    alloc_track::track_dealloc(TYPE_ITERATOR);
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

/// Get next value from array iterator (implementation for macro dispatch)
/// Returns 1 and stores value in out_value if available
/// Returns 0 if iterator exhausted (Done)
fn vole_array_iter_next_impl(iter: *mut RcIterator, out_value: *mut i64) -> i64 {
    if iter.is_null() {
        return 0;
    }
    let iter_ref = unsafe { &mut (*iter).iter };
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

/// Get next value from empty iterator - always returns Done (0)
#[inline]
fn vole_empty_iter_next(_iter: *mut RcIterator, _out_value: *mut i64) -> i64 {
    0
}

// Generate vole_array_iter_next dispatch from the central definition
for_all_iterator_kinds!(generate_next_dispatch);

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

    let layout = Layout::from_size_align(TaggedNextWord::SIZE, TaggedNextWord::ALIGN)
        .expect("valid union layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Tag 0 = value, Tag 1 = Done (descending sort order)
    let tag = if has_value == 0 {
        NextTag::Done as u8
    } else {
        NextTag::Value as u8
    };
    unsafe {
        ptr::write(ptr, tag);
        let payload_ptr = ptr.add(8) as *mut i64;
        ptr::write(payload_ptr, if has_value == 0 { 0 } else { value });
    }

    ptr
}

// Generate iter_produces_owned from the central definition
for_all_iterator_kinds!(generate_produces_owned);

fn pack_optional_i64(value: Option<i64>) -> *mut u8 {
    let layout = Layout::from_size_align(TaggedNextWord::SIZE, TaggedNextWord::ALIGN)
        .expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe {
        match value {
            Some(v) => {
                ptr::write(ptr, 0u8);
                ptr::write(ptr.add(TaggedNextWord::PAYLOAD_OFFSET) as *mut i64, v);
            }
            None => {
                ptr::write(ptr, 1u8);
                ptr::write(ptr.add(TaggedNextWord::PAYLOAD_OFFSET) as *mut i64, 0);
            }
        }
    }
    ptr
}

fn consume_values_via_next(iter: *mut RcIterator, limit: Option<usize>) -> Vec<i64> {
    let mut out = Vec::new();
    if iter.is_null() {
        return out;
    }
    loop {
        if let Some(max) = limit
            && out.len() >= max
        {
            break;
        }
        let mut value = 0i64;
        if vole_array_iter_next(iter, &mut value) == 0 {
            break;
        }
        out.push(value);
    }
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }
    out
}

fn cleanup_owned_rc_except(words: &[i64], keep_index: Option<usize>, owned_rc: bool) {
    if !owned_rc {
        return;
    }
    for (idx, &value) in words.iter().enumerate() {
        if Some(idx) != keep_index && value != 0 {
            rc_dec(value as *mut u8);
        }
    }
}

fn try_new_core_collect_tagged(iter: *mut RcIterator, elem_tag: u64) -> Option<*mut RcArray> {
    use crate::value::{TaggedValue, tag_needs_rc};

    if iter.is_null() {
        return Some(RcArray::new());
    }

    let values_owned = iter_produces_owned(iter);
    let needs_rc = tag_needs_rc(elem_tag);
    let words = consume_values_via_next(iter, None);
    let collected = CoreIter::from_i64_slice(&words).collect_i64().ok()?;
    let result = RcArray::new();

    for value in collected {
        let actual_tag = if needs_rc && !(value as usize).is_multiple_of(8) {
            0u64
        } else {
            elem_tag
        };
        let actual_needs_rc = tag_needs_rc(actual_tag);
        if actual_needs_rc && !values_owned && value != 0 {
            rc_inc(value as *mut u8);
        }
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

    Some(result)
}

fn try_new_core_first(iter: *mut RcIterator) -> Option<*mut u8> {
    let borrowed_rc = if iter.is_null() {
        false
    } else {
        iter_produces_borrowed_rc(iter)
    };
    let words = consume_values_via_next(iter, Some(1));
    let value = CoreIter::from_i64_slice(&words).first_i64().ok()?;
    if let Some(v) = value
        && borrowed_rc
        && v != 0
    {
        rc_inc(v as *mut u8);
    }
    Some(pack_optional_i64(value))
}

fn try_new_core_last(iter: *mut RcIterator) -> Option<*mut u8> {
    let owned_rc = if iter.is_null() {
        false
    } else {
        iter_produces_owned_rc(iter)
    };
    let borrowed_rc = if iter.is_null() {
        false
    } else {
        iter_produces_borrowed_rc(iter)
    };
    let words = consume_values_via_next(iter, None);
    let value = CoreIter::from_i64_slice(&words).last_i64().ok()?;
    let keep_index = if value.is_some() && !words.is_empty() {
        Some(words.len() - 1)
    } else {
        None
    };
    cleanup_owned_rc_except(&words, keep_index, owned_rc);
    if let Some(v) = value
        && borrowed_rc
        && v != 0
    {
        rc_inc(v as *mut u8);
    }
    Some(pack_optional_i64(value))
}

fn try_new_core_nth(iter: *mut RcIterator, n: i64) -> Option<*mut u8> {
    if n < 0 {
        if !iter.is_null() {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
        }
        return Some(pack_optional_i64(None));
    }
    let owned_rc = if iter.is_null() {
        false
    } else {
        iter_produces_owned_rc(iter)
    };
    let borrowed_rc = if iter.is_null() {
        false
    } else {
        iter_produces_borrowed_rc(iter)
    };
    let words = consume_values_via_next(iter, Some((n as usize).saturating_add(1)));
    let value = CoreIter::from_i64_slice(&words).nth_i64(n as usize).ok()?;
    let keep_index = if value.is_some() {
        Some(n as usize)
    } else {
        None
    };
    cleanup_owned_rc_except(&words, keep_index, owned_rc);
    if let Some(v) = value
        && borrowed_rc
        && v != 0
    {
        rc_inc(v as *mut u8);
    }
    Some(pack_optional_i64(value))
}

/// Collect all remaining iterator values into a new array with proper element type tags.
/// Reads `elem_tag` from the iterator's stored tag (set by codegen or
/// `interface_iter_tagged`). Used by vtable dispatch where the extra tag
/// parameter is not available in the interface signature.
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    if iter.is_null() {
        return vole_iter_collect_tagged(iter, 0);
    }

    let kind = unsafe { (*iter).iter.kind };
    let tag = unsafe { (*iter).elem_tag };

    // For Flatten iterators, use vole_flatten_iter_collect which reads
    // the correct inner element tag. The codegen-set elem_tag may incorrectly
    // be TYPE_ARRAY (the pre-flatten outer element type) rather than the
    // flattened inner element type (e.g. TYPE_F64).
    if kind == IteratorKind::Flatten {
        return vole_flatten_iter_collect(iter);
    }

    vole_iter_collect_tagged(iter, tag)
}

/// Collect all remaining iterator values into a new array with proper element type tags.
/// `elem_tag` is the runtime type tag for the element type (e.g. TYPE_STRING, TYPE_INSTANCE).
/// This ensures the resulting array properly tracks RC types for cleanup.
/// Handles both "owned" values (from map/string_chars) and "borrowed" values (from array)
/// by rc_inc-ing borrowed RC values so the collected array properly owns them.
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_collect_tagged(iter: *mut RcIterator, elem_tag: u64) -> *mut RcArray {
    try_new_core_collect_tagged(iter, elem_tag).expect("collect path should always produce a value")
}

/// Collect all remaining iterator values into a new array
/// Returns pointer to newly allocated array (empty if iterator is null)
/// Frees the iterator after collecting.
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
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}

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
// Consumer methods - eager evaluation that consumes the entire iterator
// =============================================================================

/// Check if an iterator produces owned RC values that need to be freed when discarded.
/// Returns true if values from this iterator should be rc_dec'd when the consumer doesn't keep them.
fn iter_produces_owned_rc(iter: *mut RcIterator) -> bool {
    if iter.is_null() {
        return false;
    }
    let tag = unsafe { (*iter).elem_tag };
    tag_needs_rc(tag) && iter_produces_owned(iter)
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
    tag_needs_rc(tag) && !iter_produces_owned(iter)
}

/// Count the number of elements in any iterator
/// Returns the count as i64
/// Frees the iterator after counting.
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
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    count
}

/// Sum all elements in any iterator.
/// Reads the iterator's stored `elem_tag` to determine whether to perform
/// integer or floating-point addition.
/// When `elem_tag` == TYPE_F64, interprets raw bits as f64 and returns f64 bits as i64.
/// Otherwise performs integer (i64) addition.
/// Returns the sum as i64 (raw bits).
/// Frees the iterator after summing.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_sum(iter: *mut RcIterator) -> i64 {
    use crate::value::TYPE_F64;

    if iter.is_null() {
        return 0;
    }

    let elem_tag = unsafe { (*iter).elem_tag };

    if elem_tag == TYPE_F64 as u64 {
        // Float summation: interpret raw bits as f64
        let mut sum: f64 = 0.0;
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(iter, &mut value);

            if has_value == 0 {
                break;
            }
            sum += f64::from_bits(value as u64);
        }

        // Free the iterator chain
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(iter);
        }

        sum.to_bits() as i64
    } else {
        // Integer summation — use wrapping_add to match JIT arithmetic semantics
        // (Cranelift iadd wraps by default)
        let mut sum: i64 = 0;
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(iter, &mut value);

            if has_value == 0 {
                break;
            }
            sum = sum.wrapping_add(value);
        }

        // Free the iterator chain
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(iter);
        }

        sum
    }
}

/// Call a function for each element in any iterator
/// The callback is a closure that takes one i64 argument and returns nothing
/// Frees the iterator after iteration.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_for_each(iter: *mut RcIterator, callback: *const Closure) {
    if iter.is_null() || callback.is_null() {
        return;
    }

    let owned_rc = iter_produces_owned_rc(iter);

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

        // Free owned RC values after the callback has used them (callback borrows, doesn't own)
        if owned_rc && value != 0 {
            rc_dec(value as *mut u8);
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // Free the callback closure (ownership transferred from codegen)
    unsafe { Closure::free(callback as *mut Closure) };
}

/// Reduce all elements in any iterator using an accumulator function, with RC cleanup.
/// `acc_tag` is the runtime type tag for the accumulator type.
/// `elem_tag` is the runtime type tag for the element type.
/// When the accumulator or element is an RC type, old values are properly decremented.
/// Returns the final accumulated value.
/// Frees the iterator after reduction.
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
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // Free the reducer closure (ownership transferred from codegen)
    unsafe { Closure::free(reducer as *mut Closure) };

    acc
}

/// Reduce all elements in any iterator using an accumulator function
/// Takes initial value and a reducer closure (acc, value) -> new_acc
/// Returns the final accumulated value
/// Frees the iterator after reduction.
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
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_first(iter: *mut RcIterator) -> *mut u8 {
    try_new_core_first(iter).expect("first path should always produce a value")
}

/// Get the last element from any iterator, returns T? (optional)
/// Consumes the entire iterator to find the last element.
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the last element.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_last(iter: *mut RcIterator) -> *mut u8 {
    try_new_core_last(iter).expect("last path should always produce a value")
}

/// Get the nth element from any iterator (0-indexed), returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the nth element.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_nth(iter: *mut RcIterator, n: i64) -> *mut u8 {
    try_new_core_nth(iter, n).expect("nth path should always produce a value")
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
pub extern "C" fn vole_flatten_iter(source: *mut RcIterator) -> *mut RcIterator {
    // Determine the inner element tag for the flattened output.
    // When the source is a Chunks or Windows iterator, use inner_elem_tag
    // (the element type of the sub-arrays, e.g. TYPE_F64 for [f64] chunks).
    // This is critical because codegen may set elem_tag to TYPE_ARRAY
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
pub extern "C" fn vole_flatten_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    // Determine the inner element type tag. The flatten iterator's elem_tag
    // may be TYPE_ARRAY (incorrectly set by codegen for the pre-flatten type).
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
                    // If the codegen-set tag is TYPE_ARRAY but we're flattening,
                    // the actual elements aren't arrays - use 0 (i64) as fallback
                    if tag == crate::value::TYPE_ARRAY as u64 {
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

// =============================================================================
// Collecting operations: reverse, sorted, unique
// =============================================================================

/// Reverse iterator - collects all elements, reverses them, returns new array iterator
/// This is an eager operation that consumes the entire source iterator.
/// Frees the source iterator after collecting.
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

// =============================================================================
// ChunksIterator - splits into non-overlapping chunks
// =============================================================================

/// Create a new chunks iterator wrapping any source iterator
/// First collects all elements, then yields non-overlapping chunks of the specified size.
/// The last chunk may be smaller than the specified size.
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_chunks_iter(source: *mut RcIterator, chunk_size: i64) -> *mut RcIterator {
    use crate::value::TaggedValue;

    // First, collect all elements from the source iterator
    let elements = RcArray::new();

    // Read the source's elem_tag before consuming it, so sub-arrays
    // preserve the correct element type (critical for f64, string, etc.)
    let source_elem_tag = if !source.is_null() {
        unsafe { (*source).elem_tag }
    } else {
        0
    };

    let needs_rc = tag_needs_rc(source_elem_tag);

    if !source.is_null() && chunk_size > 0 {
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(source, &mut value);
            if has_value == 0 {
                break;
            }
            // The source iterator yields borrowed references.  The elements
            // array will rc_dec on drop, so we must rc_inc to take ownership.
            if needs_rc && value != 0 {
                rc_inc(value as *mut u8);
            }
            unsafe {
                RcArray::push(
                    elements,
                    TaggedValue {
                        tag: source_elem_tag,
                        value: value as u64,
                    },
                );
            }
        }
        // Free the source iterator
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(source);
        }
    } else if !source.is_null() {
        // Free the source even if chunk_size <= 0
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(source);
        }
    }

    // The chunks iterator yields sub-arrays, so its elem_tag should be
    // TYPE_ARRAY (not the inner element type). The inner_elem_tag is stored
    // on ChunksSource so sub-arrays can preserve the correct inner type.

    RcIterator::new_with_tag(
        IteratorKind::Chunks,
        IteratorSource {
            chunks: ChunksSource {
                elements,
                chunk_size: if chunk_size > 0 { chunk_size } else { 1 },
                position: 0,
                inner_elem_tag: source_elem_tag,
            },
        },
        crate::value::TYPE_ARRAY as u64,
    )
}

iter_next_fn!(
    /// Get next chunk from chunks iterator.
    /// Returns 1 and stores array pointer in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_chunks_iter_next, Chunks, chunks, mut |src, _iter, out| {
        use crate::value::TaggedValue;

        let elements_len = unsafe { (*src.elements).len } as i64;

        // Check if we've exhausted all elements
        if src.position >= elements_len {
            return 0;
        }

        // Read the inner element type tag to preserve type info (e.g. f64) in sub-arrays.
        let elem_tag = src.inner_elem_tag;
        let needs_rc = tag_needs_rc(elem_tag);

        // Create a new array for this chunk
        let chunk = RcArray::new();
        let end_pos = std::cmp::min(src.position + src.chunk_size, elements_len);

        for i in src.position..end_pos {
            let value = unsafe {
                let data = (*src.elements).data;
                (*data.add(i as usize)).value
            };
            // The sub-array will rc_dec on drop, so rc_inc to share
            // ownership with the elements array.
            if needs_rc && value != 0 {
                rc_inc(value as *mut u8);
            }
            unsafe {
                RcArray::push(chunk, TaggedValue { tag: elem_tag, value });
            }
        }

        src.position = end_pos;

        unsafe { *out = chunk as i64 };
        1
    }
);

/// Collect all remaining chunks into a new array of arrays
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
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

        // Push chunk array to result with TYPE_ARRAY tag so cleanup
        // properly dec_ref's sub-arrays
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: crate::value::TYPE_ARRAY as u64,
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}

// =============================================================================
// WindowsIterator - sliding window of elements
// =============================================================================

/// Create a new windows iterator wrapping any source iterator
/// First collects all elements, then yields overlapping windows of the specified size.
/// Yields nothing if there are fewer elements than window_size.
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_windows_iter(source: *mut RcIterator, window_size: i64) -> *mut RcIterator {
    use crate::value::TaggedValue;

    // First, collect all elements from the source iterator
    let elements = RcArray::new();

    // Read the source's elem_tag before consuming it, so sub-arrays
    // preserve the correct element type (critical for f64, string, etc.)
    let source_elem_tag = if !source.is_null() {
        unsafe { (*source).elem_tag }
    } else {
        0
    };

    let needs_rc = tag_needs_rc(source_elem_tag);

    if !source.is_null() && window_size > 0 {
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(source, &mut value);
            if has_value == 0 {
                break;
            }
            // The source iterator yields borrowed references.  The elements
            // array will rc_dec on drop, so we must rc_inc to take ownership.
            if needs_rc && value != 0 {
                rc_inc(value as *mut u8);
            }
            unsafe {
                RcArray::push(
                    elements,
                    TaggedValue {
                        tag: source_elem_tag,
                        value: value as u64,
                    },
                );
            }
        }
        // Free the source iterator
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(source);
        }
    } else if !source.is_null() {
        // Free the source even if window_size <= 0
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(source);
        }
    }

    // The windows iterator yields sub-arrays, so its elem_tag should be
    // TYPE_ARRAY (not the inner element type). The inner_elem_tag is stored
    // on WindowsSource so sub-arrays can preserve the correct inner type.

    RcIterator::new_with_tag(
        IteratorKind::Windows,
        IteratorSource {
            windows: WindowsSource {
                elements,
                window_size: if window_size > 0 { window_size } else { 1 },
                position: 0,
                inner_elem_tag: source_elem_tag,
            },
        },
        crate::value::TYPE_ARRAY as u64,
    )
}

iter_next_fn!(
    /// Get next window from windows iterator.
    /// Returns 1 and stores array pointer in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_windows_iter_next, Windows, windows, mut |src, _iter, out| {
        use crate::value::TaggedValue;

        let elements_len = unsafe { (*src.elements).len } as i64;

        // Check if we can produce another window
        // We need at least window_size elements starting from position
        if src.position + src.window_size > elements_len {
            return 0;
        }

        // Read the inner element type tag to preserve type info (e.g. f64) in sub-arrays.
        let elem_tag = src.inner_elem_tag;
        let needs_rc = tag_needs_rc(elem_tag);

        // Create a new array for this window
        let window = RcArray::new();
        for i in 0..src.window_size {
            let value = unsafe {
                let data = (*src.elements).data;
                (*data.add((src.position + i) as usize)).value
            };
            // The sub-array will rc_dec on drop, so rc_inc to share
            // ownership with the elements array.
            if needs_rc && value != 0 {
                rc_inc(value as *mut u8);
            }
            unsafe {
                RcArray::push(window, TaggedValue { tag: elem_tag, value });
            }
        }

        // Move position forward by 1 for sliding window
        src.position += 1;

        unsafe { *out = window as i64 };
        1
    }
);

/// Collect all remaining windows into a new array of arrays
/// Returns pointer to newly allocated array
/// Frees the iterator after collecting.
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

        // Push window array to result with TYPE_ARRAY tag so cleanup
        // properly dec_ref's sub-arrays
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: crate::value::TYPE_ARRAY as u64,
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}

// =============================================================================
// RepeatIterator - infinite iterator yielding the same value
// =============================================================================

/// Create a new repeat iterator that yields the same value forever
/// WARNING: This is an infinite iterator - MUST use with take() or similar
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_repeat_iter(value: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Repeat,
        IteratorSource {
            repeat: RepeatSource { value },
        },
    )
}

iter_next_fn!(
    /// Get next value from repeat iterator.
    /// Always returns 1 with the same value (infinite iterator).
    vole_repeat_iter_next, Repeat, repeat, |src, _iter, out| {
        unsafe { *out = src.value };
        1 // Always has a value (infinite iterator)
    }
);

// =============================================================================
// OnceIterator - iterator that yields a single value
// =============================================================================

/// Create a new once iterator that yields exactly one value
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_once_iter(value: i64) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Once,
        IteratorSource {
            once: OnceSource {
                value,
                exhausted: false,
            },
        },
    )
}

iter_next_fn!(
    /// Get next value from once iterator.
    /// Returns 1 with the value on first call, 0 on subsequent calls.
    vole_once_iter_next, Once, once, mut |src, _iter, out| {
        if src.exhausted {
            return 0; // Already yielded the value
        }

        src.exhausted = true;
        unsafe { *out = src.value };
        1 // Has value
    }
);

// =============================================================================
// EmptyIterator - iterator that yields nothing
// =============================================================================

/// Create a new empty iterator that yields nothing
/// Returns pointer to heap-allocated iterator
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
#[unsafe(no_mangle)]
pub extern "C" fn vole_from_fn_iter(generator: *const Closure) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::FromFn,
        IteratorSource {
            from_fn: FromFnSource { generator },
        },
    )
}

iter_next_fn!(
    /// Get next value from from_fn iterator.
    /// Calls the generator function - returns 1 with value if not nil, 0 if nil.
    vole_from_fn_iter_next, FromFn, from_fn, |src, _iter, out| {
        // Call the generator function
        // The generator returns T? which is a tagged union with layout [tag:1][pad:7][payload:8]
        // Tag 0 = I64 (value present), Tag 1 = Nil
        unsafe {
            let func_ptr = Closure::get_func(src.generator);
            let generator_fn: extern "C" fn(*const Closure) -> *mut u8 =
                std::mem::transmute(func_ptr);
            let result_ptr = generator_fn(src.generator);

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
                *out = payload;
                1 // Has value
            } else {
                0 // Nil - end iteration
            }
        }
    }
);

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

iter_next_fn!(
    /// Get next value from range iterator.
    /// Returns 1 with the value if current < end, 0 if done.
    vole_range_iter_next, Range, range, mut |src, _iter, out| {
        // Check if we've reached the end
        if src.current >= src.end {
            return 0; // Done
        }

        // Yield current value and increment
        unsafe { *out = src.current };
        src.current += 1;
        1 // Has value
    }
);

// =============================================================================
// StringCharsIterator - iterator over unicode characters of a string
// =============================================================================

/// Create a new string chars iterator that yields each unicode character as a string
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_chars_iter(string: *const RcString) -> *mut RcIterator {
    // Increment ref count on string so it stays alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
    }

    RcIterator::new_with_tag(
        IteratorKind::StringChars,
        IteratorSource {
            string_chars: StringCharsSource {
                string,
                byte_pos: 0,
            },
        },
        TYPE_STRING as u64,
    )
}

iter_next_fn!(
    /// Get next character from string chars iterator.
    /// Returns 1 and stores the character string pointer in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_string_chars_iter_next, StringChars, string_chars, mut |src, _iter, out| {
        if src.string.is_null() {
            return 0;
        }

        unsafe {
            let string_ref = &*src.string;
            let byte_len = string_ref.len as i64;

            // Check if we've exhausted the string
            if src.byte_pos >= byte_len {
                return 0; // Done
            }

            // Get the string data starting at current byte position
            let data = string_ref.data();
            let remaining = &data[src.byte_pos as usize..];

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
                src.byte_pos += char_len as i64;

                // Return the new string pointer as i64
                *out = new_string as i64;
                1 // Has value
            } else {
                0 // Done - should not happen if byte_pos < byte_len
            }
        }
    }
);

// =============================================================================
// EnumerateIterator - yields (index, value) pairs
// =============================================================================

/// Create a new enumerate iterator that wraps any source iterator and yields (index, value) tuples.
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_enumerate_iter(source: *mut RcIterator) -> *mut RcIterator {
    RcIterator::new(
        IteratorKind::Enumerate,
        IteratorSource {
            enumerate: EnumerateSource { source, index: 0 },
        },
    )
}

iter_next_fn!(
    /// Get next (index, value) tuple from enumerate iterator.
    /// Returns 1 and stores tuple pointer in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    /// The tuple layout is: [index:i64][value:i64] (16 bytes total, 8-byte aligned).
    vole_enumerate_iter_next, Enumerate, enumerate, mut |src, _iter, out| {
        // Get next value from source iterator
        let mut source_value: i64 = 0;
        let has_value = vole_array_iter_next(src.source, &mut source_value);

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
            ptr::write(tuple_ptr as *mut i64, src.index);
            ptr::write((tuple_ptr as *mut i64).add(1), source_value);
        }

        // Increment index for next call
        src.index += 1;

        // Return tuple pointer
        unsafe { *out = tuple_ptr as i64 };
        1 // Has value
    }
);

// =============================================================================
// ZipIterator - combines two iterators into (a, b) pairs
// =============================================================================

/// Create a new zip iterator that combines two iterators.
/// Stops when either iterator is exhausted.
/// Returns pointer to heap-allocated iterator
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

iter_next_fn!(
    /// Get next (a, b) tuple from zip iterator.
    /// Returns 1 and stores tuple pointer in out_value if both iterators have values.
    /// Returns 0 if either iterator is exhausted (Done).
    /// The tuple layout is: [first:i64][second:i64] (16 bytes total, 8-byte aligned).
    vole_zip_iter_next, Zip, zip, mut |src, _iter, out| {
        // Get next value from first iterator
        let mut first_value: i64 = 0;
        let has_first = vole_array_iter_next(src.first, &mut first_value);

        if has_first == 0 {
            return 0; // First iterator exhausted
        }

        // Get next value from second iterator
        let mut second_value: i64 = 0;
        let has_second = vole_array_iter_next(src.second, &mut second_value);

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
        unsafe { *out = tuple_ptr as i64 };
        1 // Has value
    }
);

// =============================================================================
// StringSplitIterator - splits string by delimiter
// =============================================================================

/// Create a new string split iterator that yields substrings split by delimiter
/// Returns pointer to heap-allocated iterator
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

    RcIterator::new_with_tag(
        IteratorKind::StringSplit,
        IteratorSource {
            string_split: StringSplitSource {
                string,
                delimiter,
                byte_pos: 0,
                exhausted: false,
            },
        },
        TYPE_STRING as u64,
    )
}

iter_next_fn!(
    /// Get next substring from string split iterator.
    /// Returns 1 and stores the substring pointer in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_string_split_iter_next, StringSplit, string_split, mut |src, _iter, out| {
        if src.string.is_null() || src.exhausted {
            return 0;
        }

        unsafe {
            let string_ref = &*src.string;
            let delim_ref = if src.delimiter.is_null() {
                ""
            } else {
                (*src.delimiter).as_str()
            };

            let byte_len = string_ref.len as i64;

            // Check if we've exhausted the string
            if src.byte_pos > byte_len {
                return 0;
            }

            // Get the string data starting at current byte position
            let data = string_ref.data();
            let remaining = &data[src.byte_pos as usize..];

            // Safety: RcString stores valid UTF-8
            let remaining_str = std::str::from_utf8_unchecked(remaining);

            // Find the next delimiter
            if let Some(delim_pos) = remaining_str.find(delim_ref) {
                // Found delimiter - yield substring before it
                let substring = &remaining_str[..delim_pos];
                let new_string = RcString::new(substring);

                // Update byte position to after the delimiter
                src.byte_pos += delim_pos as i64 + delim_ref.len() as i64;

                *out = new_string as i64;
                1 // Has value
            } else {
                // No more delimiters - yield remaining string and mark exhausted
                let new_string = RcString::new(remaining_str);
                src.exhausted = true;

                *out = new_string as i64;
                1 // Has value
            }
        }
    }
);

// =============================================================================
// StringLinesIterator - splits string by newlines
// =============================================================================

/// Create a new string lines iterator that yields lines (split by \n or \r\n)
/// Returns pointer to heap-allocated iterator
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_lines_iter(string: *const RcString) -> *mut RcIterator {
    // Increment ref count on string so it stays alive while iterator exists
    unsafe {
        if !string.is_null() {
            RcString::inc_ref(string as *mut RcString);
        }
    }

    RcIterator::new_with_tag(
        IteratorKind::StringLines,
        IteratorSource {
            string_lines: StringLinesSource {
                string,
                byte_pos: 0,
                exhausted: false,
            },
        },
        TYPE_STRING as u64,
    )
}

iter_next_fn!(
    /// Get next line from string lines iterator.
    /// Returns 1 and stores the line pointer in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_string_lines_iter_next, StringLines, string_lines, mut |src, _iter, out| {
        if src.string.is_null() || src.exhausted {
            return 0;
        }

        unsafe {
            let string_ref = &*src.string;
            let byte_len = string_ref.len as i64;

            // Check if we've exhausted the string
            if src.byte_pos > byte_len {
                return 0;
            }

            // Get the string data starting at current byte position
            let data = string_ref.data();
            let remaining = &data[src.byte_pos as usize..];

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
                src.byte_pos += newline_pos as i64 + 1;

                *out = new_string as i64;
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
                src.exhausted = true;

                *out = new_string as i64;
                1 // Has value
            }
        }
    }
);

// =============================================================================
// StringCodepointsIterator - yields unicode codepoints as i32
// =============================================================================

/// Create a new string codepoints iterator that yields unicode codepoints as i32
/// Returns pointer to heap-allocated iterator
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

iter_next_fn!(
    /// Get next codepoint from string codepoints iterator.
    /// Returns 1 and stores the codepoint (as i32) in out_value if available.
    /// Returns 0 if iterator exhausted (Done).
    vole_string_codepoints_iter_next, StringCodepoints, string_codepoints, mut |src, _iter, out| {
        if src.string.is_null() {
            return 0;
        }

        unsafe {
            let string_ref = &*src.string;
            let byte_len = string_ref.len as i64;

            // Check if we've exhausted the string
            if src.byte_pos >= byte_len {
                return 0; // Done
            }

            // Get the string data starting at current byte position
            let data = string_ref.data();
            let remaining = &data[src.byte_pos as usize..];

            // Get the next UTF-8 character
            // Safety: RcString stores valid UTF-8
            let remaining_str = std::str::from_utf8_unchecked(remaining);
            let next_char = remaining_str.chars().next();

            if let Some(ch) = next_char {
                // Get the byte length of this character
                let char_len = ch.len_utf8();

                // Update byte position
                src.byte_pos += char_len as i64;

                // Return the codepoint as i32 (cast to i64 for storage)
                *out = ch as i32 as i64;
                1 // Has value
            } else {
                0 // Done - should not happen if byte_pos < byte_len
            }
        }
    }
);
