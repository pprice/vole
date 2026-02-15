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

use crate::iterator_abi::{NextTag, TaggedNextWord};
use std::alloc::{Layout, alloc};
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
            // Coroutine-backed iterator - yields values from a VoleCoroutine
            Coroutine = 23, source: coroutine, next: vole_coroutine_iter_next, owned: [true];
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
    (Coroutine, $iter_ref:expr) => {
        let coro = $iter_ref.source.coroutine.coroutine;
        if !coro.is_null() {
            drop(Box::from_raw(coro));
        }
        let closure = $iter_ref.source.coroutine.closure;
        if !closure.is_null() {
            rc_dec(closure as *mut u8);
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
        #[expect(clippy::not_unsafe_ptr_arg_deref)]
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
        #[expect(clippy::not_unsafe_ptr_arg_deref)]
        pub fn iter_produces_owned(iter: *mut RcIterator) -> bool {
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
        #[expect(clippy::not_unsafe_ptr_arg_deref)]
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
        #[expect(clippy::not_unsafe_ptr_arg_deref)]
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

// Sub-modules. Order matters: macros above must be defined before sub-module declarations.
mod chunks_windows;
mod collect_ops;
mod combine;
mod consumers;
mod generators;
mod lifecycle;
mod search;
mod string_iters;
mod terminal;
mod transform;
pub mod types;

// Re-export all public items so `crate::iterator::*` continues to work.
pub use chunks_windows::*;
pub use collect_ops::*;
pub use combine::*;
pub use consumers::*;
pub use generators::*;
pub use lifecycle::*;
pub use search::*;
pub use string_iters::*;
pub use terminal::*;
pub use transform::*;
pub use types::*;

// =============================================================================
// Dispatch and ownership inference
// =============================================================================
//
// These are generated here (after sub-module re-exports) because the dispatch
// function calls all per-kind next functions, which live in different sub-modules.

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

// Generate iter_produces_owned from the central definition
for_all_iterator_kinds!(generate_produces_owned);

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
