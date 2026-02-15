//! Iterator source types and core data structures.

use crate::array::RcArray;
use crate::closure::Closure;
use crate::string::RcString;
use crate::value::RcHeader;

// Re-export IteratorKind so `use super::types::*` brings it into scope.
pub use super::IteratorKind;

/// Unified iterator source - can be any iterator kind.
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
    /// Element type tag for inner elements (e.g. RuntimeTypeId::F64 for [f64] chunks)
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
    /// Element type tag for inner elements (e.g. RuntimeTypeId::F64 for [f64] windows)
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
/// `elem_tag` is the runtime type tag (e.g., RuntimeTypeId::String) for the element type flowing
/// through this iterator. Used by next() to rc_inc produced values and by filter/take/etc.
/// to rc_dec rejected/discarded values.
#[repr(C)]
pub struct RcIterator {
    pub header: RcHeader,
    pub iter: UnifiedIterator,
    /// Runtime type tag for elements (0 = unset/i64, RuntimeTypeId::String = 1, etc.)
    pub elem_tag: u64,
    /// True if this iterator's next() produces freshly owned values (e.g. generators).
    /// Used to decide whether terminal methods should rc_dec consumed elements.
    pub produces_owned: bool,
}
