// src/frontend/token.rs

/// All token types in the Vole language
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    // Literals
    IntLiteral,
    FloatLiteral,
    StringLiteral,
    StringInterpStart,  // "text{
    StringInterpMiddle, // }text{
    StringInterpEnd,    // }text"
    Identifier,

    // Keywords (subset for Phase 1)
    KwFunc,
    KwLet,
    KwMut,
    KwWhile,
    KwIf,
    KwElse,
    KwBreak,
    KwReturn,
    KwTrue,
    KwFalse,
    KwTests,
    KwTest,

    // Type keywords
    KwI32,
    KwI64,
    KwF64,
    KwBool,
    KwString,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    EqEq,
    BangEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    Eq,

    // Delimiters
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Arrow, // ->

    // Special
    Newline,
    Eof,
    Error,
}

impl TokenType {
    /// Get string representation for error messages
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::IntLiteral => "integer",
            Self::FloatLiteral => "float",
            Self::StringLiteral => "string",
            Self::StringInterpStart => "string interpolation",
            Self::StringInterpMiddle => "string interpolation",
            Self::StringInterpEnd => "string interpolation",
            Self::Identifier => "identifier",
            Self::KwFunc => "func",
            Self::KwLet => "let",
            Self::KwMut => "mut",
            Self::KwWhile => "while",
            Self::KwIf => "if",
            Self::KwElse => "else",
            Self::KwBreak => "break",
            Self::KwReturn => "return",
            Self::KwTrue => "true",
            Self::KwFalse => "false",
            Self::KwTests => "tests",
            Self::KwTest => "test",
            Self::KwI32 => "i32",
            Self::KwI64 => "i64",
            Self::KwF64 => "f64",
            Self::KwBool => "bool",
            Self::KwString => "string",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::EqEq => "==",
            Self::BangEq => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::LtEq => "<=",
            Self::GtEq => ">=",
            Self::Eq => "=",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::Comma => ",",
            Self::Colon => ":",
            Self::Arrow => "->",
            Self::Newline => "newline",
            Self::Eof => "end of file",
            Self::Error => "error",
        }
    }

    /// Get precedence for binary operators (Pratt parsing)
    pub fn precedence(&self) -> u8 {
        match self {
            Self::Eq => 1,
            Self::EqEq | Self::BangEq => 2,
            Self::Lt | Self::Gt | Self::LtEq | Self::GtEq => 3,
            Self::Plus | Self::Minus => 4,
            Self::Star | Self::Slash | Self::Percent => 5,
            _ => 0,
        }
    }
}

/// Source location span
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
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

/// A token with its location in source code
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub ty: TokenType,
    pub lexeme: String,
    pub span: Span,
}

impl Token {
    pub fn new(ty: TokenType, lexeme: impl Into<String>, span: Span) -> Self {
        Self {
            ty,
            lexeme: lexeme.into(),
            span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn span_with_end_position() {
        // Create a span for a 5-character token starting at byte 0, column 1
        let span = Span::new(0, 5, 1, 1);
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 5);
        assert_eq!(span.line, 1);
        assert_eq!(span.column, 1);
        assert_eq!(span.end_line, 1);
        // end_column should be column + length = 1 + 5 = 6
        assert_eq!(span.end_column, 6);
    }

    #[test]
    fn span_new_with_end_explicit() {
        // Create a span with explicit end position
        let span = Span::new_with_end(10, 20, 2, 5, 3, 8);
        assert_eq!(span.start, 10);
        assert_eq!(span.end, 20);
        assert_eq!(span.line, 2);
        assert_eq!(span.column, 5);
        assert_eq!(span.end_line, 3);
        assert_eq!(span.end_column, 8);
    }

    #[test]
    fn span_merge_preserves_end_position() {
        let span1 = Span::new_with_end(0, 5, 1, 1, 1, 6);
        let span2 = Span::new_with_end(10, 15, 2, 3, 2, 8);
        let merged = span1.merge(span2);

        // Start position comes from span1
        assert_eq!(merged.start, 0);
        assert_eq!(merged.line, 1);
        assert_eq!(merged.column, 1);

        // End position comes from span2
        assert_eq!(merged.end, 15);
        assert_eq!(merged.end_line, 2);
        assert_eq!(merged.end_column, 8);
    }
}
