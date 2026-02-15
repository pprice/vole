//! Generator and adapter iterators: repeat, once, empty, from_fn, range, string_chars, enumerate, zip.

use crate::closure::Closure;
use crate::string::RcString;
use crate::value::RuntimeTypeId;
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

use super::types::*;
use super::vole_array_iter_next;

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
        RuntimeTypeId::String as u64,
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
