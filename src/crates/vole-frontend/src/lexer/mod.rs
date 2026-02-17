// src/frontend/lexer/mod.rs

mod numbers;
mod strings;

use crate::errors::LexerError;
use crate::{Span, Token, TokenType};

/// Smallest byte value that starts a multi-byte UTF-8 sequence (non-ASCII).
const UTF8_MULTIBYTE: u8 = 0x80;

#[derive(Clone)]
pub struct Lexer<'src> {
    pub(crate) source: &'src str,
    pub(crate) bytes: &'src [u8],
    pub(crate) current: usize,
    pub(crate) start: usize,
    pub(crate) line: u32,
    pub(crate) column: u32,
    pub(crate) start_column: u32,
    pub(crate) start_line: u32,
    // Interpolation state
    pub(crate) interp_brace_depth: u32,
    pub(crate) in_interp_string: bool,
    // Error collection
    pub(crate) errors: Vec<LexerError>,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        let mut lexer = Self {
            source,
            bytes: source.as_bytes(),
            start: 0,
            current: 0,
            line: 1,
            column: 1,
            start_column: 1,
            start_line: 1,
            interp_brace_depth: 0,
            in_interp_string: false,
            errors: Vec::new(),
        };
        lexer.skip_shebang();
        lexer
    }

    /// Skip a shebang line (`#!...`) if present at the very start of the source.
    fn skip_shebang(&mut self) {
        if self.source.starts_with("#!") {
            // Consume characters until end of line or end of source
            while let Some(c) = self.advance() {
                if c == '\n' {
                    self.line += 1;
                    self.column = 1;
                    break;
                }
            }
            // Reset start to after the shebang line
            self.start = self.current;
        }
    }

    /// Take all collected errors, leaving the internal list empty.
    pub fn take_errors(&mut self) -> Vec<LexerError> {
        std::mem::take(&mut self.errors)
    }

    /// Check if any errors have been collected.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the source string being lexed.
    pub fn source(&self) -> &'src str {
        self.source
    }

    /// Get the next token from the source
    pub fn next_token(&mut self) -> Token<'src> {
        self.skip_whitespace();

        self.start = self.current;
        self.start_column = self.column;
        self.start_line = self.line;

        let Some(c) = self.advance() else {
            return self.make_token(TokenType::Eof);
        };

        match c {
            // Single character tokens
            '(' => self.make_token(TokenType::LParen),
            ')' => self.make_token(TokenType::RParen),
            '{' => {
                if self.in_interp_string {
                    self.interp_brace_depth += 1;
                }
                self.make_token(TokenType::LBrace)
            }
            '}' => {
                if self.in_interp_string && self.interp_brace_depth > 0 {
                    self.interp_brace_depth -= 1;
                    if self.interp_brace_depth == 0 {
                        return self.string_interp_continue();
                    }
                }
                self.make_token(TokenType::RBrace)
            }
            '[' => self.make_token(TokenType::LBracket),
            ']' => self.make_token(TokenType::RBracket),
            ',' => self.make_token(TokenType::Comma),
            ';' => self.make_token(TokenType::Semicolon),
            ':' => self.make_token(TokenType::Colon),
            '+' => {
                if self.match_byte(b'=') {
                    self.make_token(TokenType::PlusEq)
                } else {
                    self.make_token(TokenType::Plus)
                }
            }
            '*' => {
                if self.match_byte(b'=') {
                    self.make_token(TokenType::StarEq)
                } else {
                    self.make_token(TokenType::Star)
                }
            }
            '%' => {
                if self.match_byte(b'=') {
                    self.make_token(TokenType::PercentEq)
                } else {
                    self.make_token(TokenType::Percent)
                }
            }

            // Single or double character tokens
            '-' => {
                if self.match_byte(b'>') {
                    self.make_token(TokenType::Arrow)
                } else if self.match_byte(b'=') {
                    self.make_token(TokenType::MinusEq)
                } else {
                    self.make_token(TokenType::Minus)
                }
            }
            '=' => {
                if self.match_byte(b'=') {
                    self.make_token(TokenType::EqEq)
                } else if self.match_byte(b'>') {
                    self.make_token(TokenType::FatArrow)
                } else {
                    self.make_token(TokenType::Eq)
                }
            }
            '!' => {
                if self.match_byte(b'=') {
                    self.make_token(TokenType::BangEq)
                } else {
                    self.make_token(TokenType::Bang)
                }
            }
            '&' => {
                if self.match_byte(b'&') {
                    self.make_token(TokenType::AmpAmp)
                } else {
                    self.make_token(TokenType::Ampersand)
                }
            }
            '|' => {
                if self.match_byte(b'|') {
                    self.make_token(TokenType::PipePipe)
                } else {
                    self.make_token(TokenType::Pipe)
                }
            }
            '?' => {
                if self.match_byte(b'?') {
                    self.make_token(TokenType::QuestionQuestion)
                } else if self.match_byte(b'.') {
                    self.make_token(TokenType::QuestionDot)
                } else {
                    self.make_token(TokenType::Question)
                }
            }
            '^' => self.make_token(TokenType::Caret),
            '~' => self.make_token(TokenType::Tilde),
            '<' => {
                if self.match_byte(b'<') {
                    self.make_token(TokenType::LessLess)
                } else if self.match_byte(b'=') {
                    self.make_token(TokenType::LtEq)
                } else {
                    self.make_token(TokenType::Lt)
                }
            }
            '>' => {
                if self.match_byte(b'>') {
                    self.make_token(TokenType::GreaterGreater)
                } else if self.match_byte(b'=') {
                    self.make_token(TokenType::GtEq)
                } else {
                    self.make_token(TokenType::Gt)
                }
            }

            // Slash or comment
            '/' => {
                if self.match_byte(b'/') {
                    // Comment - skip to end of line using byte scanning
                    self.skip_line_comment();
                    // Don't consume the newline, let next_token handle it
                    self.next_token()
                } else if self.match_byte(b'=') {
                    self.make_token(TokenType::SlashEq)
                } else {
                    self.make_token(TokenType::Slash)
                }
            }

            // Newline
            '\n' => {
                let token = self.make_token(TokenType::Newline);
                self.line += 1;
                self.column = 1;
                token
            }

            // String literal
            '"' => self.string(),

            // Dot, range operators
            '.' => {
                if self.match_byte(b'.') {
                    if self.match_byte(b'=') {
                        self.make_token(TokenType::DotDotEqual)
                    } else {
                        self.make_token(TokenType::DotDot)
                    }
                } else {
                    self.make_token(TokenType::Dot)
                }
            }

            // Number literal
            c if c.is_ascii_digit() => self.number(),

            // Identifier or keyword (supports Unicode XID, bans invisible chars)
            c if c == '_' || (unicode_ident::is_xid_start(c) && !Self::is_banned_unicode(c)) => {
                self.identifier()
            }

            // Raw string literal: @"..."
            '@' => {
                if self.match_byte(b'"') {
                    self.raw_string()
                } else {
                    self.error_unexpected_char(c)
                }
            }

            _ => self.error_unexpected_char(c),
        }
    }

    /// Skip whitespace (spaces, tabs, carriage returns) using direct byte access
    #[inline]
    fn skip_whitespace(&mut self) {
        while self.current < self.bytes.len() {
            match self.bytes[self.current] {
                b' ' | b'\t' | b'\r' => {
                    self.current += 1;
                    self.column += 1;
                }
                _ => break,
            }
        }
    }

    /// Advance to the next character and return it.
    /// Fast path for ASCII bytes (no UTF-8 decoding needed).
    #[inline]
    pub(crate) fn advance(&mut self) -> Option<char> {
        if self.current >= self.bytes.len() {
            return None;
        }
        let b = self.bytes[self.current];
        if b < UTF8_MULTIBYTE {
            // ASCII fast path: single byte, no UTF-8 decoding
            self.current += 1;
            self.column += 1;
            Some(b as char)
        } else {
            // Non-ASCII: decode UTF-8 from the source str
            let remaining = &self.source[self.current..];
            let c = remaining.chars().next().expect("non-empty source slice");
            self.current += c.len_utf8();
            self.column += 1;
            Some(c)
        }
    }

    /// Peek at the next byte directly (for ASCII-only comparisons).
    #[inline]
    pub(crate) fn peek_byte(&self) -> Option<u8> {
        self.bytes.get(self.current).copied()
    }

    /// Peek at the character after the next one
    pub(crate) fn peek_next(&self) -> Option<char> {
        if self.current >= self.bytes.len() {
            return None;
        }
        let b = self.bytes[self.current];
        if b < UTF8_MULTIBYTE {
            // Current char is ASCII (1 byte), look at next position
            let next_pos = self.current + 1;
            if next_pos >= self.bytes.len() {
                return None;
            }
            let b2 = self.bytes[next_pos];
            if b2 < UTF8_MULTIBYTE {
                Some(b2 as char)
            } else {
                let remaining = &self.source[next_pos..];
                remaining.chars().next()
            }
        } else {
            // Current char is multi-byte, decode to find where next char starts
            let remaining = &self.source[self.current..];
            let mut iter = remaining.chars();
            iter.next(); // skip current
            iter.next()
        }
    }

    /// Consume the next character if it matches the expected byte.
    /// All callers use ASCII characters, so we compare bytes directly.
    #[inline]
    fn match_byte(&mut self, expected: u8) -> bool {
        debug_assert!(expected < UTF8_MULTIBYTE, "match_byte only works for ASCII");
        if self.current < self.bytes.len() && self.bytes[self.current] == expected {
            self.current += 1;
            self.column += 1;
            true
        } else {
            false
        }
    }

    /// Create a token from start to current position
    pub(crate) fn make_token(&self, ty: TokenType) -> Token<'src> {
        let lexeme = &self.source[self.start..self.current];
        Token::new(
            ty,
            lexeme,
            Span::new_with_end(
                self.start,
                self.current,
                self.start_line,
                self.start_column,
                self.line,
                self.column,
            ),
        )
    }

    /// Create an error token and collect an error for an unexpected character.
    fn error_unexpected_char(&mut self, c: char) -> Token<'src> {
        let span = Span::new_with_end(
            self.start,
            self.current,
            self.start_line,
            self.start_column,
            self.line,
            self.column,
        );
        let error = LexerError::UnexpectedCharacter {
            ch: c,
            span: span.into(),
        };
        tracing::debug!(char = %c, line = self.start_line, col = self.start_column, "lexer error: unexpected character");
        let message = format!("unexpected character '{}'", c);
        self.errors.push(error);
        Token::new(TokenType::Error, message, span)
    }

    /// Scan an identifier or keyword (supports Unicode XID).
    /// Uses a byte-level fast path for ASCII identifier characters.
    fn identifier(&mut self) -> Token<'src> {
        // Fast ASCII loop: consume [a-zA-Z0-9_] bytes without UTF-8 decoding
        while self.current < self.bytes.len() {
            let b = self.bytes[self.current];
            if b.is_ascii_alphanumeric() || b == b'_' {
                self.current += 1;
                self.column += 1;
            } else if b >= UTF8_MULTIBYTE {
                // Non-ASCII: decode and check Unicode XID
                let remaining = &self.source[self.current..];
                let c = remaining.chars().next().expect("non-empty source slice");
                if unicode_ident::is_xid_continue(c) && !Self::is_banned_unicode(c) {
                    self.current += c.len_utf8();
                    self.column += 1;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        let text = &self.source[self.start..self.current];
        let ty = TokenType::keyword_type(text).unwrap_or(TokenType::Identifier);
        self.make_token(ty)
    }

    /// Skip a line comment (everything until newline or EOF) using byte scanning.
    #[inline]
    fn skip_line_comment(&mut self) {
        while self.current < self.bytes.len() && self.bytes[self.current] != b'\n' {
            self.current += 1;
            self.column += 1;
        }
    }

    /// Check if a Unicode character is banned from identifiers
    /// (invisible, zero-width, or potentially confusing)
    fn is_banned_unicode(c: char) -> bool {
        matches!(
            c,
            // Zero-width characters
            '\u{200B}'   // Zero Width Space
            | '\u{200C}' // Zero Width Non-Joiner (ZWNJ)
            | '\u{200D}' // Zero Width Joiner (ZWJ)
            | '\u{FEFF}' // Zero Width No-Break Space (BOM)
            // Invisible formatting
            | '\u{00AD}' // Soft Hyphen
            | '\u{034F}' // Combining Grapheme Joiner
            | '\u{061C}' // Arabic Letter Mark
            | '\u{115F}'..='\u{1160}' // Hangul fillers
            | '\u{17B4}'..='\u{17B5}' // Khmer invisible
            | '\u{180B}'..='\u{180E}' // Mongolian format
            | '\u{2060}'..='\u{206F}' // General punctuation invisibles (includes LRI, RLI, FSI, PDI)
            | '\u{3164}' // Hangul Filler
            | '\u{FFA0}' // Halfwidth Hangul Filler
            // Bidirectional overrides (security risk)
            | '\u{202A}'..='\u{202E}' // LRE, RLE, PDF, LRO, RLO
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::LexerError;

    #[test]
    fn lex_single_char_tokens() {
        let mut lexer = Lexer::new("( ) { } , :");
        assert_eq!(lexer.next_token().ty, TokenType::LParen);
        assert_eq!(lexer.next_token().ty, TokenType::RParen);
        assert_eq!(lexer.next_token().ty, TokenType::LBrace);
        assert_eq!(lexer.next_token().ty, TokenType::RBrace);
        assert_eq!(lexer.next_token().ty, TokenType::Comma);
        assert_eq!(lexer.next_token().ty, TokenType::Colon);
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_operators() {
        let mut lexer = Lexer::new("+ - * / == != < > <= >=");
        assert_eq!(lexer.next_token().ty, TokenType::Plus);
        assert_eq!(lexer.next_token().ty, TokenType::Minus);
        assert_eq!(lexer.next_token().ty, TokenType::Star);
        assert_eq!(lexer.next_token().ty, TokenType::Slash);
        assert_eq!(lexer.next_token().ty, TokenType::EqEq);
        assert_eq!(lexer.next_token().ty, TokenType::BangEq);
        assert_eq!(lexer.next_token().ty, TokenType::Lt);
        assert_eq!(lexer.next_token().ty, TokenType::Gt);
        assert_eq!(lexer.next_token().ty, TokenType::LtEq);
        assert_eq!(lexer.next_token().ty, TokenType::GtEq);
    }

    #[test]
    fn lex_keywords() {
        let mut lexer = Lexer::new("func let mut while if else break return");
        assert_eq!(lexer.next_token().ty, TokenType::KwFunc);
        assert_eq!(lexer.next_token().ty, TokenType::KwLet);
        assert_eq!(lexer.next_token().ty, TokenType::KwMut);
        assert_eq!(lexer.next_token().ty, TokenType::KwWhile);
        assert_eq!(lexer.next_token().ty, TokenType::KwIf);
        assert_eq!(lexer.next_token().ty, TokenType::KwElse);
        assert_eq!(lexer.next_token().ty, TokenType::KwBreak);
        assert_eq!(lexer.next_token().ty, TokenType::KwReturn);
    }

    #[test]
    fn lex_numbers() {
        let mut lexer = Lexer::new("42 3.14 0 1000");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "42");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::FloatLiteral);
        assert_eq!(t2.lexeme, "3.14");
    }

    #[test]
    fn lex_f128_keyword_and_suffix() {
        let mut lexer = Lexer::new("f128 3.5_f128");
        assert_eq!(lexer.next_token().ty, TokenType::KwF128);
        let lit = lexer.next_token();
        assert_eq!(lit.ty, TokenType::FloatLiteral);
        assert_eq!(lit.lexeme, "3.5_f128");
    }

    #[test]
    fn lex_string() {
        let mut lexer = Lexer::new("\"hello world\"");
        let t = lexer.next_token();
        assert_eq!(t.ty, TokenType::StringLiteral);
        assert_eq!(t.lexeme, "\"hello world\"");
    }

    #[test]
    fn lex_arrow() {
        let mut lexer = Lexer::new("-> func");
        assert_eq!(lexer.next_token().ty, TokenType::Arrow);
        assert_eq!(lexer.next_token().ty, TokenType::KwFunc);
    }

    #[test]
    fn lex_comments() {
        let mut lexer = Lexer::new("42 // this is a comment\n43");
        assert_eq!(lexer.next_token().ty, TokenType::IntLiteral);
        assert_eq!(lexer.next_token().ty, TokenType::Newline);
        assert_eq!(lexer.next_token().ty, TokenType::IntLiteral);
    }

    #[test]
    fn lex_string_interpolation() {
        let mut lexer = Lexer::new("\"hello {name}!\"");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::StringInterpStart);
        assert_eq!(t1.lexeme, "\"hello {");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::Identifier);
        assert_eq!(t2.lexeme, "name");

        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::StringInterpEnd);
        assert_eq!(t3.lexeme, "}!\"");
    }

    #[test]
    fn lex_string_interpolation_multiple() {
        let mut lexer = Lexer::new("\"x={x}, y={y}\"");
        assert_eq!(lexer.next_token().ty, TokenType::StringInterpStart); // "x={
        assert_eq!(lexer.next_token().ty, TokenType::Identifier); // x
        assert_eq!(lexer.next_token().ty, TokenType::StringInterpMiddle); // }, y={
        assert_eq!(lexer.next_token().ty, TokenType::Identifier); // y
        assert_eq!(lexer.next_token().ty, TokenType::StringInterpEnd); // }"
    }

    #[test]
    fn lexer_sets_span_end_position() {
        let mut lexer = Lexer::new("hello");
        let token = lexer.next_token();

        assert_eq!(token.ty, TokenType::Identifier);
        assert_eq!(token.lexeme, "hello");

        // Span should cover "hello" (5 characters)
        assert_eq!(token.span.start, 0);
        assert_eq!(token.span.end, 5);
        assert_eq!(token.span.line, 1);
        assert_eq!(token.span.column, 1);
        assert_eq!(token.span.end_line, 1);
        // After consuming 5 chars, column is at 6
        assert_eq!(token.span.end_column, 6);
    }

    #[test]
    fn lexer_multi_char_operator_span() {
        let mut lexer = Lexer::new("==");
        let token = lexer.next_token();

        assert_eq!(token.ty, TokenType::EqEq);
        assert_eq!(token.lexeme, "==");

        // Span should cover "==" (2 characters)
        assert_eq!(token.span.column, 1);
        assert_eq!(token.span.end_column, 3);
    }

    #[test]
    fn lexer_collects_unexpected_char_error() {
        let mut lexer = Lexer::new("@");
        let token = lexer.next_token();

        assert_eq!(token.ty, TokenType::Error);
        assert!(lexer.has_errors());

        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            &errors[0],
            LexerError::UnexpectedCharacter { ch: '@', .. }
        ));
    }

    #[test]
    fn lexer_collects_unterminated_string_error() {
        let mut lexer = Lexer::new("\"hello");
        let token = lexer.next_token();

        assert_eq!(token.ty, TokenType::Error);
        assert!(lexer.has_errors());

        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);
        assert!(matches!(&errors[0], LexerError::UnterminatedString { .. }));
    }

    #[test]
    fn lexer_continues_after_errors() {
        // Test that lexer continues lexing after encountering errors
        let mut lexer = Lexer::new("let @ x = 42");

        assert_eq!(lexer.next_token().ty, TokenType::KwLet);
        assert_eq!(lexer.next_token().ty, TokenType::Error); // @
        assert_eq!(lexer.next_token().ty, TokenType::Identifier); // x
        assert_eq!(lexer.next_token().ty, TokenType::Eq);
        assert_eq!(lexer.next_token().ty, TokenType::IntLiteral); // 42
        assert_eq!(lexer.next_token().ty, TokenType::Eof);

        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);
    }

    #[test]
    fn lexer_collects_multiple_errors() {
        let mut lexer = Lexer::new("@ # $");

        assert_eq!(lexer.next_token().ty, TokenType::Error);
        assert_eq!(lexer.next_token().ty, TokenType::Error);
        assert_eq!(lexer.next_token().ty, TokenType::Error);
        assert_eq!(lexer.next_token().ty, TokenType::Eof);

        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 3);
    }

    #[test]
    fn lexer_take_errors_clears_errors() {
        let mut lexer = Lexer::new("@");
        lexer.next_token();

        assert!(lexer.has_errors());
        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);

        // After taking, errors should be cleared
        assert!(!lexer.has_errors());
        assert!(lexer.take_errors().is_empty());
    }

    #[test]
    fn lexer_new_creates_errors() {
        let mut lexer = Lexer::new("@");
        lexer.next_token();

        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);
        // File is attached when creating Report, not stored in error
        assert!(matches!(
            &errors[0],
            LexerError::UnexpectedCharacter { ch: '@', .. }
        ));
    }

    #[test]
    fn lex_bang() {
        let mut lexer = Lexer::new("!true");
        assert_eq!(lexer.next_token().ty, TokenType::Bang);
        assert_eq!(lexer.next_token().ty, TokenType::KwTrue);
    }

    #[test]
    fn lex_logical_operators() {
        let mut lexer = Lexer::new("&& ||");
        assert_eq!(lexer.next_token().ty, TokenType::AmpAmp);
        assert_eq!(lexer.next_token().ty, TokenType::PipePipe);
    }

    #[test]
    fn lex_nil_is_optional() {
        // nil and Done are no longer keywords - they lex as identifiers
        // (they are prelude-defined sentinels)
        let mut lexer = Lexer::new("nil is i32? ?? 0");
        assert_eq!(lexer.next_token().ty, TokenType::Identifier);
        assert_eq!(lexer.next_token().ty, TokenType::KwIs);
        assert_eq!(lexer.next_token().ty, TokenType::KwI32);
        assert_eq!(lexer.next_token().ty, TokenType::Question);
        assert_eq!(lexer.next_token().ty, TokenType::QuestionQuestion);
        assert_eq!(lexer.next_token().ty, TokenType::IntLiteral);
    }

    #[test]
    fn lex_compound_assignment() {
        let mut lexer = Lexer::new("+= -= *= /= %=");
        assert_eq!(lexer.next_token().ty, TokenType::PlusEq);
        assert_eq!(lexer.next_token().ty, TokenType::MinusEq);
        assert_eq!(lexer.next_token().ty, TokenType::StarEq);
        assert_eq!(lexer.next_token().ty, TokenType::SlashEq);
        assert_eq!(lexer.next_token().ty, TokenType::PercentEq);
    }

    #[test]
    fn lex_class_keyword() {
        let mut lexer = Lexer::new("class");
        assert_eq!(lexer.next_token().ty, TokenType::KwClass);
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_record_is_identifier() {
        // "record" is no longer a keyword; it should lex as an identifier
        let mut lexer = Lexer::new("record");
        let token = lexer.next_token();
        assert_eq!(token.ty, TokenType::Identifier);
        assert_eq!(token.lexeme, "record");
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_never_unknown_keywords() {
        let mut lexer = Lexer::new("never unknown");
        assert_eq!(lexer.next_token().ty, TokenType::KwNever);
        assert_eq!(lexer.next_token().ty, TokenType::KwUnknown);
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_sentinel_keyword() {
        let mut lexer = Lexer::new("sentinel");
        let token = lexer.next_token();
        assert_eq!(token.ty, TokenType::KwSentinel);
        assert_eq!(token.lexeme, "sentinel");
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_hex_literals() {
        let mut lexer = Lexer::new("0xFF 0x1A2B 0X00 0xDEAD_BEEF");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "0xFF");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::IntLiteral);
        assert_eq!(t2.lexeme, "0x1A2B");

        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::IntLiteral);
        assert_eq!(t3.lexeme, "0X00");

        let t4 = lexer.next_token();
        assert_eq!(t4.ty, TokenType::IntLiteral);
        assert_eq!(t4.lexeme, "0xDEAD_BEEF");

        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_binary_literals() {
        let mut lexer = Lexer::new("0b1010 0B11110000 0b1111_0000");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "0b1010");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::IntLiteral);
        assert_eq!(t2.lexeme, "0B11110000");

        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::IntLiteral);
        assert_eq!(t3.lexeme, "0b1111_0000");

        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_underscore_separators() {
        let mut lexer = Lexer::new("1_000_000 1_0 99_99");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "1_000_000");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::IntLiteral);
        assert_eq!(t2.lexeme, "1_0");

        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::IntLiteral);
        assert_eq!(t3.lexeme, "99_99");

        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_float_with_underscores() {
        let mut lexer = Lexer::new("1_000.5 3.14_15");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::FloatLiteral);
        assert_eq!(t1.lexeme, "1_000.5");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::FloatLiteral);
        assert_eq!(t2.lexeme, "3.14_15");

        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_scientific_notation() {
        let mut lexer = Lexer::new("1e10 1.5e-3 2E+6 1e0");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::FloatLiteral);
        assert_eq!(t1.lexeme, "1e10");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::FloatLiteral);
        assert_eq!(t2.lexeme, "1.5e-3");

        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::FloatLiteral);
        assert_eq!(t3.lexeme, "2E+6");

        let t4 = lexer.next_token();
        assert_eq!(t4.ty, TokenType::FloatLiteral);
        assert_eq!(t4.lexeme, "1e0");

        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_scientific_notation_with_underscores() {
        let mut lexer = Lexer::new("1_000e10 1.5_0e-3");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::FloatLiteral);
        assert_eq!(t1.lexeme, "1_000e10");

        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::FloatLiteral);
        assert_eq!(t2.lexeme, "1.5_0e-3");

        assert_eq!(lexer.next_token().ty, TokenType::Eof);
    }

    #[test]
    fn lex_invalid_hex_no_digits() {
        let mut lexer = Lexer::new("0x");
        let t = lexer.next_token();
        assert_eq!(t.ty, TokenType::Error);
        assert!(lexer.has_errors());
        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);
        assert!(matches!(&errors[0], LexerError::InvalidNumber { .. }));
    }

    #[test]
    fn lex_invalid_binary_no_digits() {
        let mut lexer = Lexer::new("0b");
        let t = lexer.next_token();
        assert_eq!(t.ty, TokenType::Error);
        assert!(lexer.has_errors());
        let errors = lexer.take_errors();
        assert_eq!(errors.len(), 1);
        assert!(matches!(&errors[0], LexerError::InvalidNumber { .. }));
    }

    #[test]
    fn lex_hex_followed_by_operator() {
        let mut lexer = Lexer::new("0xFF+1");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "0xFF");
        assert_eq!(lexer.next_token().ty, TokenType::Plus);
        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::IntLiteral);
        assert_eq!(t3.lexeme, "1");
    }

    #[test]
    fn lex_binary_followed_by_operator() {
        let mut lexer = Lexer::new("0b1010&0b1100");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "0b1010");
        assert_eq!(lexer.next_token().ty, TokenType::Ampersand);
        let t3 = lexer.next_token();
        assert_eq!(t3.ty, TokenType::IntLiteral);
        assert_eq!(t3.lexeme, "0b1100");
    }

    #[test]
    fn lex_zero_is_still_valid() {
        let mut lexer = Lexer::new("0 00");
        let t1 = lexer.next_token();
        assert_eq!(t1.ty, TokenType::IntLiteral);
        assert_eq!(t1.lexeme, "0");
        let t2 = lexer.next_token();
        assert_eq!(t2.ty, TokenType::IntLiteral);
        assert_eq!(t2.lexeme, "00");
    }

    #[test]
    fn lex_shebang_skipped_at_start() {
        let mut lexer = Lexer::new("#!/usr/bin/env vole\nlet x = 42");
        // Shebang line should be completely skipped
        assert_eq!(lexer.next_token().ty, TokenType::KwLet);
        assert_eq!(lexer.next_token().ty, TokenType::Identifier);
        assert_eq!(lexer.next_token().ty, TokenType::Eq);
        let t = lexer.next_token();
        assert_eq!(t.ty, TokenType::IntLiteral);
        assert_eq!(t.lexeme, "42");
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
        assert!(!lexer.has_errors());
    }

    #[test]
    fn lex_shebang_line_number_starts_at_two() {
        let mut lexer = Lexer::new("#!/usr/bin/env vole\nlet x = 42");
        let token = lexer.next_token(); // `let`
        assert_eq!(token.span.line, 2);
    }

    #[test]
    fn lex_shebang_only_at_position_zero() {
        // #! not at the start of the file should produce errors, not be treated as shebang
        let mut lexer = Lexer::new("let x\n#!/usr/bin/env vole");
        assert_eq!(lexer.next_token().ty, TokenType::KwLet);
        assert_eq!(lexer.next_token().ty, TokenType::Identifier);
        assert_eq!(lexer.next_token().ty, TokenType::Newline);
        // '#' and '!' are not valid tokens; they should produce errors
        assert_eq!(lexer.next_token().ty, TokenType::Error); // #
        assert_eq!(lexer.next_token().ty, TokenType::Bang); // !
    }

    #[test]
    fn lex_no_shebang_normal_source() {
        // Regular source without shebang should work as before
        let mut lexer = Lexer::new("let x = 1");
        assert_eq!(lexer.next_token().ty, TokenType::KwLet);
        assert_eq!(lexer.next_token().ty, TokenType::Identifier);
        assert_eq!(lexer.next_token().ty, TokenType::Eq);
        assert_eq!(lexer.next_token().ty, TokenType::IntLiteral);
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
        assert!(!lexer.has_errors());
    }

    #[test]
    fn lex_shebang_eof_without_newline() {
        // A file that is only a shebang line with no trailing newline
        let mut lexer = Lexer::new("#!/usr/bin/env vole");
        assert_eq!(lexer.next_token().ty, TokenType::Eof);
        assert!(!lexer.has_errors());
    }
}
