// src/frontend/token.rs

/// Single source of truth for keyword-to-token mapping.
///
/// Each entry `"text" => Variant` generates:
/// - A match arm in `TokenType::keyword_type`: `"text" => Some(TokenType::Variant)`
/// - A match arm in `TokenType::as_str`:       `Self::Variant => "text"`
macro_rules! define_keywords {
    ( $( $text:literal => $variant:ident ),+ $(,)? ) => {
        impl TokenType {
            /// Check if a string is a keyword and return its token type.
            pub fn keyword_type(text: &str) -> Option<TokenType> {
                match text {
                    $( $text => Some(TokenType::$variant), )+
                    _ => None,
                }
            }

            /// String representation for keyword tokens (used by `as_str`).
            fn keyword_as_str(&self) -> Option<&'static str> {
                match self {
                    $( Self::$variant => Some($text), )+
                    _ => None,
                }
            }
        }
    };
}

define_keywords! {
    // Language keywords
    "func"        => KwFunc,
    "let"         => KwLet,
    "mut"         => KwMut,
    "while"       => KwWhile,
    "if"          => KwIf,
    "else"        => KwElse,
    "break"       => KwBreak,
    "return"      => KwReturn,
    "true"        => KwTrue,
    "false"       => KwFalse,
    "tests"       => KwTests,
    "test"        => KwTest,
    "for"         => KwFor,
    "in"          => KwIn,
    "continue"    => KwContinue,
    "match"       => KwMatch,
    "is"          => KwIs,
    "class"       => KwClass,
    "struct"      => KwStruct,
    "interface"   => KwInterface,
    "implements"  => KwImplements,
    "implement"   => KwImplement,
    "extends"     => KwExtends,
    "Self"        => KwSelfType,
    "val"         => KwVal,
    "error"       => KwError,
    "success"     => KwSuccess,
    "fallible"    => KwFallible,
    "raise"       => KwRaise,
    "try"         => KwTry,
    "external"    => KwExternal,
    "as"          => KwAs,
    "import"      => KwImport,
    "yield"       => KwYield,
    "default"     => KwDefault,
    "statics"     => KwStatics,
    "static"      => KwStatic,
    "when"        => KwWhen,
    "where"       => KwWhere,
    "unreachable" => KwUnreachable,
    "sentinel"    => KwSentinel,
    // Type keywords
    "i8"          => KwI8,
    "i16"         => KwI16,
    "i32"         => KwI32,
    "i64"         => KwI64,
    "i128"        => KwI128,
    "u8"          => KwU8,
    "u16"         => KwU16,
    "u32"         => KwU32,
    "u64"         => KwU64,
    "f32"         => KwF32,
    "f64"         => KwF64,
    "bool"        => KwBool,
    "string"      => KwString,
    "handle"      => KwHandle,
    "never"       => KwNever,
    "unknown"     => KwUnknown,
}

/// All token types in the Vole language
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    // Literals
    IntLiteral,
    FloatLiteral,
    StringLiteral,
    RawStringLiteral,   // @"..."
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
    KwIs,          // is keyword (type test)
    KwClass,       // class keyword
    KwStruct,      // struct keyword
    KwInterface,   // interface keyword
    KwImplements,  // implements keyword (class implements Trait)
    KwImplement,   // implement keyword (implement Trait for Type)
    KwExtends,     // extends keyword (interface inheritance)
    KwSelfType,    // Self keyword (implementing type in interface)
    KwVal,         // val keyword (value comparison in match patterns)
    KwError,       // error keyword
    KwSuccess,     // success keyword
    KwFallible,    // fallible keyword
    KwRaise,       // raise keyword
    KwTry,         // try keyword (propagation operator)
    KwExternal,    // external keyword
    KwAs,          // as keyword (for external func mapping)
    KwImport,      // import keyword
    KwYield,       // yield keyword (generator yield expression)
    KwDefault,     // default keyword (interface default methods)
    KwStatics,     // statics keyword (static method blocks)
    KwStatic,      // static keyword (static interface sugar)
    KwWhen,        // when keyword (conditional expressions)
    KwWhere,       // where keyword (generic type mappings)
    KwUnreachable, // unreachable keyword (bottom type expression)
    KwSentinel,    // sentinel keyword (sentinel type declarations)

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
    KwHandle,  // handle type (opaque native pointer)
    KwNever,   // never type (bottom type - no values)
    KwUnknown, // unknown type (top type - any value)

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
    Semicolon, // ;
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
        // Keywords are defined once in `define_keywords!`; delegate to the
        // generated helper so they never diverge from `keyword_type()`.
        if let Some(s) = self.keyword_as_str() {
            return s;
        }
        match self {
            Self::IntLiteral => "integer",
            Self::FloatLiteral => "float",
            Self::StringLiteral => "string",
            Self::RawStringLiteral => "raw string",
            Self::StringInterpStart => "string interpolation",
            Self::StringInterpMiddle => "string interpolation",
            Self::StringInterpEnd => "string interpolation",
            Self::Identifier => "identifier",
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
            Self::Semicolon => ";",
            Self::Colon => ":",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::DotDotEqual => "..=",
            Self::Arrow => "->",
            Self::FatArrow => "=>",
            Self::Newline => "newline",
            Self::Eof => "end of file",
            Self::Error => "error",
            // All keyword variants are handled by `keyword_as_str()` above.
            _ => unreachable!("keyword variant not covered by define_keywords! macro"),
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

// Re-export Span from vole-identity (canonical definition)
pub use vole_identity::Span;

/// A token with its location in source code
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'src> {
    pub ty: TokenType,
    pub lexeme: std::borrow::Cow<'src, str>,
    pub span: Span,
}

impl<'src> Token<'src> {
    pub fn new(ty: TokenType, lexeme: impl Into<std::borrow::Cow<'src, str>>, span: Span) -> Self {
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
