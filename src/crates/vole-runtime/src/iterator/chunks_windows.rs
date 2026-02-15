//! Chunked and windowed iterators: chunks, windows.

use crate::array::RcArray;
use crate::value::{RuntimeTypeId, rc_inc, tag_needs_rc};

use super::types::*;
use super::vole_array_iter_next;

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
    // RuntimeTypeId::Array (not the inner element type). The inner_elem_tag is stored
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
        RuntimeTypeId::Array as u64,
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

        // Push chunk array to result with RuntimeTypeId::Array tag so cleanup
        // properly dec_ref's sub-arrays
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: RuntimeTypeId::Array as u64,
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
    // RuntimeTypeId::Array (not the inner element type). The inner_elem_tag is stored
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
        RuntimeTypeId::Array as u64,
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

        // Push window array to result with RuntimeTypeId::Array tag so cleanup
        // properly dec_ref's sub-arrays
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: RuntimeTypeId::Array as u64,
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
