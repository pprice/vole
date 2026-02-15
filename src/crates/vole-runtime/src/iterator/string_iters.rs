//! String iterator implementations: split, lines, codepoints.

use crate::string::RcString;
use crate::value::RuntimeTypeId;

use super::types::*;

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
        RuntimeTypeId::String as u64,
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
        RuntimeTypeId::String as u64,
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
