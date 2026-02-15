// src/frontend/lexer/strings.rs
//
// String literal lexing: basic strings, raw strings, and interpolation.

use crate::{Token, TokenType};

use super::Lexer;

impl<'src> Lexer<'src> {
    /// Scan a string literal (basic, with interpolation start support)
    pub(super) fn string(&mut self) -> Token<'src> {
        loop {
            match self.peek_byte() {
                None => {
                    return self.error_unterminated_string();
                }
                Some(b'"') => {
                    self.advance();
                    return self.make_token(TokenType::StringLiteral);
                }
                Some(b'\\') => {
                    // Escape sequence - consume backslash and next char
                    self.advance();
                    if self.current < self.bytes.len() {
                        self.advance();
                    }
                }
                Some(b'{') => {
                    // Check for escaped brace {{
                    if self.bytes.get(self.current + 1) == Some(&b'{') {
                        // Escaped brace - consume both and continue
                        self.advance();
                        self.advance();
                    } else {
                        // String interpolation start
                        self.advance();
                        self.in_interp_string = true;
                        self.interp_brace_depth = 1;
                        return self.make_token(TokenType::StringInterpStart);
                    }
                }
                Some(b'}') => {
                    // Check for escaped brace }}
                    if self.bytes.get(self.current + 1) == Some(&b'}') {
                        // Escaped brace - consume both and continue
                        self.advance();
                        self.advance();
                    } else {
                        // Stray } in string - just include it
                        self.advance();
                    }
                }
                Some(b'\n') => {
                    return self.error_unterminated_string();
                }
                Some(_) => {
                    self.advance();
                }
            }
        }
    }

    /// Scan a raw string literal @"..." (no escape processing)
    pub(super) fn raw_string(&mut self) -> Token<'src> {
        // Opening @" already consumed
        loop {
            match self.peek_byte() {
                None => {
                    return self.error_unterminated_string();
                }
                Some(b'"') => {
                    self.advance();
                    return self.make_token(TokenType::RawStringLiteral);
                }
                Some(b'\n') => {
                    // Raw strings can span multiple lines
                    self.line += 1;
                    self.column = 1;
                    self.advance();
                }
                Some(_) => {
                    self.advance();
                }
            }
        }
    }

    /// Continue scanning after an interpolation expression closes
    pub(super) fn string_interp_continue(&mut self) -> Token<'src> {
        // We just consumed '}', now continue scanning the string
        self.start = self.current - 1; // Include the '}'

        loop {
            match self.peek_byte() {
                Some(b'"') => {
                    self.advance();
                    self.in_interp_string = false;
                    return self.make_token(TokenType::StringInterpEnd);
                }
                Some(b'{') => {
                    // Check for escaped brace {{
                    if self.bytes.get(self.current + 1) == Some(&b'{') {
                        // Escaped brace - consume both and continue
                        self.advance();
                        self.advance();
                    } else {
                        self.advance();
                        self.interp_brace_depth = 1;
                        return self.make_token(TokenType::StringInterpMiddle);
                    }
                }
                Some(b'}') => {
                    // Check for escaped brace }}
                    if self.bytes.get(self.current + 1) == Some(&b'}') {
                        // Escaped brace - consume both and continue
                        self.advance();
                        self.advance();
                    } else {
                        // Stray } in string - just include it
                        self.advance();
                    }
                }
                Some(b'\n') | None => {
                    return self.error_unterminated_string();
                }
                Some(b'\\') => {
                    self.advance();
                    if self.current < self.bytes.len() {
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }
    }

    /// Create an error token and collect an error for an unterminated string.
    pub(super) fn error_unterminated_string(&mut self) -> Token<'src> {
        let span = crate::Span::new_with_end(
            self.start,
            self.current,
            self.start_line,
            self.start_column,
            self.line,
            self.column,
        );
        let error = crate::errors::LexerError::UnterminatedString { span: span.into() };
        tracing::debug!(
            line = self.start_line,
            col = self.start_column,
            "lexer error: unterminated string"
        );
        let message = "unterminated string literal".to_string();
        self.errors.push(error);
        Token::new(TokenType::Error, message, span)
    }
}
