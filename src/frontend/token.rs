// src/frontend/token.rs

/// All token types in the Vole language
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    // Literals
    IntLiteral,
    FloatLiteral,
    StringLiteral,
    StringInterpStart,   // "text{
    StringInterpMiddle,  // }text{
    StringInterpEnd,     // }text"
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
    Arrow,  // ->

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
    pub start: usize,  // Byte offset
    pub end: usize,    // Byte offset (exclusive)
    pub line: u32,
    pub column: u32,
}

impl Span {
    pub fn new(start: usize, end: usize, line: u32, column: u32) -> Self {
        Self { start, end, line, column }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start,
            end: other.end,
            line: self.line,
            column: self.column,
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
