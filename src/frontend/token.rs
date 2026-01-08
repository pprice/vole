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
    KwFor,
    KwIn,
    KwContinue,
    KwMatch,
    KwNil,        // nil keyword (literal and type)
    KwIs,         // is keyword (type test)
    KwClass,      // class keyword
    KwRecord,     // record keyword
    KwInterface,  // interface keyword
    KwImplements, // implements keyword (record implements Trait)
    KwImplement,  // implement keyword (implement Trait for Type)
    KwExtends,    // extends keyword (interface inheritance)
    KwSelfType,   // Self keyword (implementing type in interface)
    KwVal,        // val keyword (value comparison in match patterns)
    KwError,      // error keyword
    KwSuccess,    // success keyword
    KwFallible,   // fallible keyword
    KwRaise,      // raise keyword
    KwTry,        // try keyword (propagation operator)
    KwExternal,   // external keyword
    KwAs,         // as keyword (for external func mapping)
    KwImport,     // import keyword
    KwDone,       // Done keyword (iterator termination sentinel)
    KwYield,      // yield keyword (generator yield expression)
    KwDefault,    // default keyword (interface default methods)

    // Type keywords
    KwI8,
    KwI16,
    KwI32,
    KwI64,
    KwI128,
    KwU8,
    KwU16,
    KwU32,
    KwU64,
    KwF32,
    KwF64,
    KwBool,
    KwString,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusEq,    // +=
    MinusEq,   // -=
    StarEq,    // *=
    SlashEq,   // /=
    PercentEq, // %=
    EqEq,
    BangEq,
    Bang,     // !
    AmpAmp,   // &&
    PipePipe, // ||
    Lt,
    Gt,
    LtEq,
    GtEq,
    Eq,

    // Bitwise operators
    Ampersand,        // &
    Pipe,             // |
    Caret,            // ^
    Tilde,            // ~
    LessLess,         // <<
    GreaterGreater,   // >>
    Question,         // ?
    QuestionDot,      // ?.
    QuestionQuestion, // ??

    // Delimiters
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket, // [
    RBracket, // ]
    Comma,
    Colon,
    Dot,
    DotDot,      // ..
    DotDotEqual, // ..=
    Arrow,       // ->
    FatArrow,    // =>

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
            Self::KwFor => "for",
            Self::KwIn => "in",
            Self::KwContinue => "continue",
            Self::KwMatch => "match",
            Self::KwNil => "nil",
            Self::KwIs => "is",
            Self::KwClass => "class",
            Self::KwRecord => "record",
            Self::KwInterface => "interface",
            Self::KwImplements => "implements",
            Self::KwImplement => "implement",
            Self::KwExtends => "extends",
            Self::KwSelfType => "Self",
            Self::KwVal => "val",
            Self::KwError => "error",
            Self::KwSuccess => "success",
            Self::KwFallible => "fallible",
            Self::KwRaise => "raise",
            Self::KwTry => "try",
            Self::KwExternal => "external",
            Self::KwAs => "as",
            Self::KwImport => "import",
            Self::KwDone => "Done",
            Self::KwYield => "yield",
            Self::KwDefault => "default",
            Self::KwI8 => "i8",
            Self::KwI16 => "i16",
            Self::KwI32 => "i32",
            Self::KwI64 => "i64",
            Self::KwI128 => "i128",
            Self::KwU8 => "u8",
            Self::KwU16 => "u16",
            Self::KwU32 => "u32",
            Self::KwU64 => "u64",
            Self::KwF32 => "f32",
            Self::KwF64 => "f64",
            Self::KwBool => "bool",
            Self::KwString => "string",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::PlusEq => "+=",
            Self::MinusEq => "-=",
            Self::StarEq => "*=",
            Self::SlashEq => "/=",
            Self::PercentEq => "%=",
            Self::EqEq => "==",
            Self::BangEq => "!=",
            Self::Bang => "!",
            Self::AmpAmp => "&&",
            Self::PipePipe => "||",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::LtEq => "<=",
            Self::GtEq => ">=",
            Self::Eq => "=",
            Self::Ampersand => "&",
            Self::Pipe => "|",
            Self::Caret => "^",
            Self::Tilde => "~",
            Self::LessLess => "<<",
            Self::GreaterGreater => ">>",
            Self::Question => "?",
            Self::QuestionDot => "?.",
            Self::QuestionQuestion => "??",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::Comma => ",",
            Self::Colon => ":",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::DotDotEqual => "..=",
            Self::Arrow => "->",
            Self::FatArrow => "=>",
            Self::Newline => "newline",
            Self::Eof => "end of file",
            Self::Error => "error",
        }
    }

    /// Get precedence for binary operators (Pratt parsing)
    pub fn precedence(&self) -> u8 {
        match self {
            Self::Eq
            | Self::PlusEq
            | Self::MinusEq
            | Self::StarEq
            | Self::SlashEq
            | Self::PercentEq => 1, // assignment (lowest)
            Self::PipePipe | Self::QuestionQuestion => 2, // logical or, null coalescing
            Self::AmpAmp => 3,                            // logical and
            Self::Pipe => 4,                              // bitwise or
            Self::Caret => 5,                             // bitwise xor
            Self::Ampersand => 6,                         // bitwise and
            Self::EqEq | Self::BangEq => 7,               // equality
            Self::Lt | Self::Gt | Self::LtEq | Self::GtEq | Self::KwIs => 8, // comparison
            Self::LessLess | Self::GreaterGreater => 9,   // shifts
            Self::Plus | Self::Minus => 10,               // additive
            Self::Star | Self::Slash | Self::Percent => 11, // multiplicative
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

/// A token with its location in source code
#[derive(Debug, Clone, PartialEq, Eq)]
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
