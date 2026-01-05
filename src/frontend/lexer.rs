// src/frontend/lexer.rs

use crate::errors::LexerError;
use crate::frontend::{Span, Token, TokenType};

pub struct Lexer<'src> {
    source: &'src str,
    chars: std::iter::Peekable<std::str::CharIndices<'src>>,
    start: usize,
    current: usize,
    line: u32,
    column: u32,
    start_column: u32,
    start_line: u32,
    // Interpolation state
    interp_brace_depth: u32,
    in_interp_string: bool,
    // Error collection
    errors: Vec<LexerError>,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        Self::new_with_file(source, "<input>")
    }

    pub fn new_with_file(source: &'src str, _filename: &str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
            start: 0,
            current: 0,
            line: 1,
            column: 1,
            start_column: 1,
            start_line: 1,
            interp_brace_depth: 0,
            in_interp_string: false,
            errors: Vec::new(),
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
    pub fn next_token(&mut self) -> Token {
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
            ':' => self.make_token(TokenType::Colon),
            '+' => {
                if self.match_char('=') {
                    self.make_token(TokenType::PlusEq)
                } else {
                    self.make_token(TokenType::Plus)
                }
            }
            '*' => {
                if self.match_char('=') {
                    self.make_token(TokenType::StarEq)
                } else {
                    self.make_token(TokenType::Star)
                }
            }
            '%' => {
                if self.match_char('=') {
                    self.make_token(TokenType::PercentEq)
                } else {
                    self.make_token(TokenType::Percent)
                }
            }

            // Single or double character tokens
            '-' => {
                if self.match_char('>') {
                    self.make_token(TokenType::Arrow)
                } else if self.match_char('=') {
                    self.make_token(TokenType::MinusEq)
                } else {
                    self.make_token(TokenType::Minus)
                }
            }
            '=' => {
                if self.match_char('=') {
                    self.make_token(TokenType::EqEq)
                } else if self.match_char('>') {
                    self.make_token(TokenType::FatArrow)
                } else {
                    self.make_token(TokenType::Eq)
                }
            }
            '!' => {
                if self.match_char('=') {
                    self.make_token(TokenType::BangEq)
                } else {
                    self.make_token(TokenType::Bang)
                }
            }
            '&' => {
                if self.match_char('&') {
                    self.make_token(TokenType::AmpAmp)
                } else {
                    self.make_token(TokenType::Ampersand)
                }
            }
            '|' => {
                if self.match_char('|') {
                    self.make_token(TokenType::PipePipe)
                } else {
                    self.make_token(TokenType::Pipe)
                }
            }
            '?' => {
                if self.match_char('?') {
                    self.make_token(TokenType::QuestionQuestion)
                } else {
                    self.make_token(TokenType::Question)
                }
            }
            '^' => self.make_token(TokenType::Caret),
            '~' => self.make_token(TokenType::Tilde),
            '<' => {
                if self.match_char('<') {
                    self.make_token(TokenType::LessLess)
                } else if self.match_char('=') {
                    self.make_token(TokenType::LtEq)
                } else {
                    self.make_token(TokenType::Lt)
                }
            }
            '>' => {
                if self.match_char('>') {
                    self.make_token(TokenType::GreaterGreater)
                } else if self.match_char('=') {
                    self.make_token(TokenType::GtEq)
                } else {
                    self.make_token(TokenType::Gt)
                }
            }

            // Slash or comment
            '/' => {
                if self.match_char('/') {
                    // Comment - skip to end of line
                    while self.peek() != Some('\n') && self.peek().is_some() {
                        self.advance();
                    }
                    // Don't consume the newline, let next_token handle it
                    self.next_token()
                } else if self.match_char('=') {
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
                if self.match_char('.') {
                    if self.match_char('=') {
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

            // Identifier or keyword
            c if c.is_ascii_alphabetic() || c == '_' => self.identifier(),

            _ => self.error_unexpected_char(c),
        }
    }

    /// Skip whitespace (spaces and tabs) and comments
    fn skip_whitespace(&mut self) {
        while let Some(' ') | Some('\t') | Some('\r') = self.peek() {
            self.advance();
        }
    }

    /// Advance to the next character and return it
    fn advance(&mut self) -> Option<char> {
        if let Some((idx, c)) = self.chars.next() {
            self.current = idx + c.len_utf8();
            self.column += 1;
            Some(c)
        } else {
            None
        }
    }

    /// Peek at the next character without consuming it
    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    /// Peek at the character after the next one
    fn peek_next(&self) -> Option<char> {
        let mut iter = self.source[self.current..].chars();
        iter.next(); // skip current
        iter.next()
    }

    /// Consume the next character if it matches the expected character
    fn match_char(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Create a token from start to current position
    fn make_token(&self, ty: TokenType) -> Token {
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
    fn error_unexpected_char(&mut self, c: char) -> Token {
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
        let message = format!("unexpected character '{}'", c);
        self.errors.push(error);
        Token::new(TokenType::Error, message, span)
    }

    /// Create an error token and collect an error for an unterminated string.
    fn error_unterminated_string(&mut self) -> Token {
        let span = Span::new_with_end(
            self.start,
            self.current,
            self.start_line,
            self.start_column,
            self.line,
            self.column,
        );
        let error = LexerError::UnterminatedString { span: span.into() };
        let message = "unterminated string literal".to_string();
        self.errors.push(error);
        Token::new(TokenType::Error, message, span)
    }

    /// Create an error token and collect an error for an invalid number literal.
    #[allow(dead_code)] // Available for future use
    fn error_invalid_number(&mut self) -> Token {
        let span = Span::new_with_end(
            self.start,
            self.current,
            self.start_line,
            self.start_column,
            self.line,
            self.column,
        );
        let error = LexerError::InvalidNumber { span: span.into() };
        let message = "invalid number literal".to_string();
        self.errors.push(error);
        Token::new(TokenType::Error, message, span)
    }

    /// Scan an identifier or keyword
    fn identifier(&mut self) -> Token {
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let text = &self.source[self.start..self.current];
        let ty = Self::keyword_type(text).unwrap_or(TokenType::Identifier);
        self.make_token(ty)
    }

    /// Check if a string is a keyword and return its token type
    fn keyword_type(text: &str) -> Option<TokenType> {
        match text {
            "func" => Some(TokenType::KwFunc),
            "let" => Some(TokenType::KwLet),
            "mut" => Some(TokenType::KwMut),
            "while" => Some(TokenType::KwWhile),
            "if" => Some(TokenType::KwIf),
            "else" => Some(TokenType::KwElse),
            "break" => Some(TokenType::KwBreak),
            "return" => Some(TokenType::KwReturn),
            "true" => Some(TokenType::KwTrue),
            "false" => Some(TokenType::KwFalse),
            "tests" => Some(TokenType::KwTests),
            "test" => Some(TokenType::KwTest),
            "for" => Some(TokenType::KwFor),
            "in" => Some(TokenType::KwIn),
            "continue" => Some(TokenType::KwContinue),
            "match" => Some(TokenType::KwMatch),
            "nil" => Some(TokenType::KwNil),
            "is" => Some(TokenType::KwIs),
            "class" => Some(TokenType::KwClass),
            "record" => Some(TokenType::KwRecord),
            "interface" => Some(TokenType::KwInterface),
            "implements" => Some(TokenType::KwImplements),
            "implement" => Some(TokenType::KwImplement),
            "extends" => Some(TokenType::KwExtends),
            "Self" => Some(TokenType::KwSelfType),
            "val" => Some(TokenType::KwVal),
            "error" => Some(TokenType::KwError),
            "success" => Some(TokenType::KwSuccess),
            "fallible" => Some(TokenType::KwFallible),
            "raise" => Some(TokenType::KwRaise),
            "try" => Some(TokenType::KwTry),
            "external" => Some(TokenType::KwExternal),
            "as" => Some(TokenType::KwAs),
            "import" => Some(TokenType::KwImport),
            "i8" => Some(TokenType::KwI8),
            "i16" => Some(TokenType::KwI16),
            "i32" => Some(TokenType::KwI32),
            "i64" => Some(TokenType::KwI64),
            "i128" => Some(TokenType::KwI128),
            "u8" => Some(TokenType::KwU8),
            "u16" => Some(TokenType::KwU16),
            "u32" => Some(TokenType::KwU32),
            "u64" => Some(TokenType::KwU64),
            "f32" => Some(TokenType::KwF32),
            "f64" => Some(TokenType::KwF64),
            "bool" => Some(TokenType::KwBool),
            "string" => Some(TokenType::KwString),
            _ => None,
        }
    }

    /// Scan a number literal (integer or float)
    fn number(&mut self) -> Token {
        // Consume integer part
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }

        // Check for decimal point followed by digit
        if self.peek() == Some('.')
            && let Some(next) = self.peek_next()
            && next.is_ascii_digit()
        {
            // Consume the dot
            self.advance();
            // Consume the fractional part
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    self.advance();
                } else {
                    break;
                }
            }
            return self.make_token(TokenType::FloatLiteral);
        }

        self.make_token(TokenType::IntLiteral)
    }

    /// Scan a string literal (basic, with interpolation start support)
    fn string(&mut self) -> Token {
        loop {
            match self.peek() {
                None => {
                    return self.error_unterminated_string();
                }
                Some('"') => {
                    self.advance();
                    return self.make_token(TokenType::StringLiteral);
                }
                Some('\\') => {
                    // Escape sequence - consume backslash and next char
                    self.advance();
                    if self.peek().is_some() {
                        self.advance();
                    }
                }
                Some('{') => {
                    // String interpolation start
                    self.advance();
                    self.in_interp_string = true;
                    self.interp_brace_depth = 1;
                    return self.make_token(TokenType::StringInterpStart);
                }
                Some('\n') => {
                    return self.error_unterminated_string();
                }
                Some(_) => {
                    self.advance();
                }
            }
        }
    }

    /// Continue scanning after an interpolation expression closes
    fn string_interp_continue(&mut self) -> Token {
        // We just consumed '}', now continue scanning the string
        self.start = self.current - 1; // Include the '}'

        loop {
            match self.peek() {
                Some('"') => {
                    self.advance();
                    self.in_interp_string = false;
                    return self.make_token(TokenType::StringInterpEnd);
                }
                Some('{') => {
                    self.advance();
                    self.interp_brace_depth = 1;
                    return self.make_token(TokenType::StringInterpMiddle);
                }
                Some('\n') | None => {
                    return self.error_unterminated_string();
                }
                Some('\\') => {
                    self.advance();
                    if self.peek().is_some() {
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }
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
    fn lexer_new_with_file_creates_errors() {
        let mut lexer = Lexer::new_with_file("@", "test.vole");
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
        let mut lexer = Lexer::new("nil is i32? ?? 0");
        assert_eq!(lexer.next_token().ty, TokenType::KwNil);
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
    fn lex_class_record_keywords() {
        let mut lexer = Lexer::new("class record");
        assert_eq!(lexer.next_token().ty, TokenType::KwClass);
        assert_eq!(lexer.next_token().ty, TokenType::KwRecord);
    }
}
