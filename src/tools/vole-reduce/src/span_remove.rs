// span_remove.rs
//! Span-based source text removal helpers.
//!
//! These utilities remove byte ranges from source text while cleaning up
//! trailing blank lines left behind. They are used by reduction passes
//! (import trimming, declaration elimination, etc.) that operate on
//! AST-derived spans.

// ---------------------------------------------------------------------------
// Single span removal
// ---------------------------------------------------------------------------

/// Remove bytes `[start, end)` from `source`.
///
/// After removal, if the edit leaves a blank line (a line that is entirely
/// whitespace or empty), that line is collapsed — the trailing newline is
/// removed so the output doesn't accumulate blank gaps.
pub fn remove_span(source: &str, start: usize, end: usize) -> String {
    debug_assert!(start <= end, "remove_span: start ({start}) > end ({end})");
    debug_assert!(
        end <= source.len(),
        "remove_span: end ({end}) > source.len() ({})",
        source.len()
    );

    let before = &source[..start];
    let after = &source[end..];

    // Extend the removal to consume the rest of the line (trailing whitespace
    // + newline) if the resulting line would be blank.
    let trimmed = trim_blank_line_after(before, after);

    let mut result = String::with_capacity(before.len() + trimmed.len());
    result.push_str(before);
    result.push_str(trimmed);
    result
}

/// If `before` ends at a line boundary (or is all whitespace on the current
/// line) and `after` starts with optional whitespace then a newline, skip
/// past that newline so we don't leave a blank line.
fn trim_blank_line_after<'a>(before: &str, after: &'a str) -> &'a str {
    // Check whether `before` is at a line start (or the only content on the
    // current line is whitespace).
    let at_line_start = before.is_empty() || line_prefix_is_blank(before);

    if !at_line_start {
        return after;
    }

    // If the remaining text on this line (in `after`) is blank up to a
    // newline, consume through that newline.
    let rest_on_line = after.len() - after.trim_start_matches([' ', '\t']).len();
    let remaining = &after[rest_on_line..];

    if let Some(stripped) = remaining.strip_prefix("\r\n") {
        stripped
    } else if let Some(stripped) = remaining.strip_prefix('\n') {
        stripped
    } else if remaining.is_empty() {
        // End of file — strip trailing whitespace-only prefix.
        remaining
    } else {
        after
    }
}

/// Check whether the text on the current line (the portion of `before` after
/// the last newline) is entirely whitespace.
fn line_prefix_is_blank(before: &str) -> bool {
    // Find the start of the current line.
    let line_start = match before.rfind('\n') {
        Some(pos) => pos + 1,
        None => 0,
    };
    before[line_start..]
        .bytes()
        .all(|b| b == b' ' || b == b'\t')
}

// ---------------------------------------------------------------------------
// Multiple span removal
// ---------------------------------------------------------------------------

/// Remove multiple non-overlapping byte ranges from `source`.
///
/// Available for future reduction passes (declaration elimination, etc.).
///
/// Spans are sorted by start offset and applied from end to start so that
/// earlier offsets remain valid after later removals.
#[allow(dead_code)] // Reusable helper for future passes (e.g. declaration elimination).
pub fn remove_spans(source: &str, spans: &[(usize, usize)]) -> String {
    if spans.is_empty() {
        return source.to_string();
    }

    // Sort by start offset descending so we can apply removals back-to-front.
    let mut sorted: Vec<(usize, usize)> = spans.to_vec();
    sorted.sort_by(|a, b| b.0.cmp(&a.0));

    let mut result = source.to_string();
    for (start, end) in sorted {
        result = remove_span(&result, start, end);
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remove_single_line() {
        let src = "line1\nline2\nline3\n";
        // Remove "line2\n" (bytes 6..12)
        let result = remove_span(src, 6, 12);
        assert_eq!(result, "line1\nline3\n");
    }

    #[test]
    fn remove_first_line() {
        let src = "line1\nline2\nline3\n";
        let result = remove_span(src, 0, 6);
        assert_eq!(result, "line2\nline3\n");
    }

    #[test]
    fn remove_last_line_no_trailing_newline() {
        let src = "line1\nline2";
        // Remove "line2" (bytes 6..11)
        let result = remove_span(src, 6, 11);
        assert_eq!(result, "line1\n");
    }

    #[test]
    fn remove_middle_content_leaves_no_blank_line() {
        let src = "let a = 1\nlet b = import \"foo\"\nlet c = 3\n";
        // Remove the import line content: "let b = import \"foo\""
        let start = "let a = 1\n".len();
        let end = start + "let b = import \"foo\"".len();
        let result = remove_span(src, start, end);
        // Should collapse the blank line
        assert_eq!(result, "let a = 1\nlet c = 3\n");
    }

    #[test]
    fn remove_partial_line_preserves_rest() {
        let src = "hello world\n";
        // Remove "hello " (bytes 0..6) — but "world" remains on the same line
        let result = remove_span(src, 0, 6);
        assert_eq!(result, "world\n");
    }

    #[test]
    fn remove_multiple_spans() {
        let src = "aaa\nbbb\nccc\nddd\n";
        // Remove "bbb\n" (4..8) and "ddd\n" (12..16)
        let result = remove_spans(src, &[(4, 8), (12, 16)]);
        assert_eq!(result, "aaa\nccc\n");
    }

    #[test]
    fn remove_spans_empty() {
        let src = "hello\n";
        let result = remove_spans(src, &[]);
        assert_eq!(result, "hello\n");
    }

    #[test]
    fn remove_entire_content() {
        let src = "only line\n";
        let result = remove_span(src, 0, src.len());
        assert_eq!(result, "");
    }
}
