// span.rs
//
// Source location span for diagnostics.

/// Source location span
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Span {
    pub start: usize,    // Byte offset
    pub end: usize,      // Byte offset (exclusive)
    pub line: u32,       // Start line (1-indexed)
    pub column: u32,     // Start column (1-indexed)
    pub end_line: u32,   // End line (1-indexed)
    pub end_column: u32, // End column (1-indexed, exclusive)
}

impl Span {
    /// Create a new span with explicit end position
    pub fn new_with_end(
        start: usize,
        end: usize,
        line: u32,
        column: u32,
        end_line: u32,
        end_column: u32,
    ) -> Self {
        Self {
            start,
            end,
            line,
            column,
            end_line,
            end_column,
        }
    }

    /// Create a new span, computing end position for single-line tokens
    pub fn new(start: usize, end: usize, line: u32, column: u32) -> Self {
        // For backwards compatibility, compute end_column from byte length
        // This assumes single-line, ASCII tokens
        let length = end.saturating_sub(start);
        Self {
            start,
            end,
            line,
            column,
            end_line: line,
            end_column: column + length as u32,
        }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start,
            end: other.end,
            line: self.line,
            column: self.column,
            end_line: other.end_line,
            end_column: other.end_column,
        }
    }
}

impl From<Span> for miette::SourceSpan {
    fn from(span: Span) -> Self {
        // miette uses (offset, length)
        (span.start, span.end - span.start).into()
    }
}

impl From<&Span> for miette::SourceSpan {
    fn from(span: &Span) -> Self {
        (span.start, span.end - span.start).into()
    }
}
