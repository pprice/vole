// src/frontend/lexer/numbers.rs
//
// Number literal lexing: integers, floats, hex, binary, scientific notation,
// underscore separators, and type suffixes.

use crate::{Token, TokenType};

use super::Lexer;

impl<'src> Lexer<'src> {
    /// After consuming the integer part of a decimal number, check if it extends
    /// to a float literal via a decimal point or scientific notation.
    /// Returns a FloatLiteral token if extended, IntLiteral otherwise.
    pub(super) fn try_extend_to_float(&mut self) -> Token<'src> {
        // Check for decimal point followed by digit
        if self.peek_byte() == Some(b'.')
            && let Some(next) = self.peek_next()
            && next.is_ascii_digit()
        {
            // Consume the dot
            self.current += 1;
            self.column += 1;
            // Consume the fractional part
            while let Some(&b) = self.bytes.get(self.current) {
                if b.is_ascii_digit() {
                    self.current += 1;
                    self.column += 1;
                } else if b == b'_' {
                    // Check if this underscore starts a type suffix
                    if self.is_type_suffix_ahead() {
                        self.current += 1;
                        self.column += 1;
                        self.consume_suffix_name();
                        return self.make_token(TokenType::FloatLiteral);
                    }
                    self.current += 1;
                    self.column += 1;
                } else {
                    break;
                }
            }

            // Check for scientific notation exponent on float
            if let Some(&e) = self.bytes.get(self.current)
                && (e == b'e' || e == b'E')
            {
                self.current += 1;
                self.column += 1;
                // Optional sign
                if let Some(&sign) = self.bytes.get(self.current)
                    && (sign == b'+' || sign == b'-')
                {
                    self.current += 1;
                    self.column += 1;
                }
                // Consume exponent digits
                while let Some(&b) = self.bytes.get(self.current) {
                    if b.is_ascii_digit() {
                        self.current += 1;
                        self.column += 1;
                    } else if b == b'_' {
                        // Check if this underscore starts a type suffix
                        if self.is_type_suffix_ahead() {
                            self.current += 1;
                            self.column += 1;
                            self.consume_suffix_name();
                            return self.make_token(TokenType::FloatLiteral);
                        }
                        self.current += 1;
                        self.column += 1;
                    } else {
                        break;
                    }
                }
            }

            return self.make_token(TokenType::FloatLiteral);
        }

        // Check for scientific notation on integer (makes it a float)
        if let Some(&e) = self.bytes.get(self.current)
            && (e == b'e' || e == b'E')
        {
            self.current += 1;
            self.column += 1;
            // Optional sign
            if let Some(&sign) = self.bytes.get(self.current)
                && (sign == b'+' || sign == b'-')
            {
                self.current += 1;
                self.column += 1;
            }
            // Consume exponent digits
            while let Some(&b) = self.bytes.get(self.current) {
                if b.is_ascii_digit() {
                    self.current += 1;
                    self.column += 1;
                } else if b == b'_' {
                    // Check if this underscore starts a type suffix
                    if self.is_type_suffix_ahead() {
                        self.current += 1;
                        self.column += 1;
                        self.consume_suffix_name();
                        return self.make_token(TokenType::FloatLiteral);
                    }
                    self.current += 1;
                    self.column += 1;
                } else {
                    break;
                }
            }
            return self.make_token(TokenType::FloatLiteral);
        }

        self.make_token(TokenType::IntLiteral)
    }

    /// Scan a number literal (integer or float)
    ///
    /// Supports:
    /// - Decimal: `42`, `1_000_000`
    /// - Hex: `0xFF`, `0xFF_FF`
    /// - Binary: `0b1010`, `0b1111_0000`
    /// - Float: `3.14`, `1_000.5`
    /// - Scientific: `1e10`, `1.5e-3`, `2E+6`
    /// - Underscores as separators in all formats
    /// - Type suffixes: `100_u8`, `3.14_f32`, `0xFF_i32`
    pub(super) fn number(&mut self) -> Token<'src> {
        // The first digit has already been consumed by next_token().
        // Check if it was '0' to detect hex/binary prefix.
        let first_char = self.bytes[self.start];

        if first_char == b'0'
            && let Some(prefix) = self.peek_byte()
        {
            if prefix == b'x' || prefix == b'X' {
                return self.hex_literal();
            } else if prefix == b'b' || prefix == b'B' {
                return self.binary_literal();
            }
        }

        // Decimal integer part (continue consuming digits and underscores)
        while let Some(&b) = self.bytes.get(self.current) {
            if b.is_ascii_digit() {
                self.current += 1;
                self.column += 1;
            } else if b == b'_' {
                // Check if this underscore starts a type suffix
                if self.is_type_suffix_ahead() {
                    self.current += 1;
                    self.column += 1;
                    self.consume_suffix_name();
                    // After consuming suffix, check if this is a float suffix on a decimal
                    // (we haven't seen a dot yet, so we're still in integer parsing)
                    return self.make_token(TokenType::IntLiteral);
                }
                self.current += 1;
                self.column += 1;
            } else {
                break;
            }
        }

        self.try_extend_to_float()
    }

    /// Scan a hex literal: 0x...
    fn hex_literal(&mut self) -> Token<'src> {
        // Consume the 'x' or 'X'
        self.current += 1;
        self.column += 1;
        let mut has_digits = false;
        while let Some(&b) = self.bytes.get(self.current) {
            if b.is_ascii_hexdigit() {
                has_digits = true;
                self.current += 1;
                self.column += 1;
            } else if b == b'_' {
                // Check if this underscore starts a type suffix
                if self.is_type_suffix_ahead() {
                    self.current += 1;
                    self.column += 1;
                    self.consume_suffix_name();
                    break;
                }
                self.current += 1;
                self.column += 1;
            } else {
                break;
            }
        }
        if !has_digits {
            return self.error_invalid_number();
        }
        self.make_token(TokenType::IntLiteral)
    }

    /// Scan a binary literal: 0b...
    fn binary_literal(&mut self) -> Token<'src> {
        // Consume the 'b' or 'B'
        self.current += 1;
        self.column += 1;
        let mut has_digits = false;
        while let Some(&b) = self.bytes.get(self.current) {
            if b == b'0' || b == b'1' {
                has_digits = true;
                self.current += 1;
                self.column += 1;
            } else if b == b'_' {
                // Check if this underscore starts a type suffix
                if self.is_type_suffix_ahead() {
                    self.current += 1;
                    self.column += 1;
                    self.consume_suffix_name();
                    break;
                }
                self.current += 1;
                self.column += 1;
            } else {
                break;
            }
        }
        if !has_digits {
            return self.error_invalid_number();
        }
        self.make_token(TokenType::IntLiteral)
    }

    /// Check if the characters after the current `_` position form a known type suffix.
    /// This peeks at the chars after the underscore (which is at peek position).
    /// We look for patterns like `_u8`, `_i32`, `_f64` etc.
    pub(super) fn is_type_suffix_ahead(&self) -> bool {
        // We're at a '_' which is at peek position.
        // We need to look at what follows the underscore.
        // peek() returns '_', peek_next() returns the char after that.
        let remaining = &self.source[self.current..];
        // remaining starts at the '_'
        if remaining.len() < 2 {
            return false;
        }
        // Skip the underscore itself
        let after_underscore = &remaining[1..];
        // Check if it starts with a known suffix that is NOT followed by an alphanumeric or underscore
        for suffix in &[
            "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "i128", "f32", "f64",
        ] {
            if after_underscore.starts_with(suffix) {
                let suffix_end = suffix.len();
                // Make sure the suffix is not followed by alphanumeric or underscore
                // (to avoid matching _u8foo as a suffix)
                if suffix_end >= after_underscore.len() {
                    return true;
                }
                let next_char = after_underscore.as_bytes()[suffix_end];
                if !next_char.is_ascii_alphanumeric() && next_char != b'_' {
                    return true;
                }
            }
        }
        false
    }

    /// Consume the alphabetic/numeric suffix name after the underscore has been consumed.
    /// Expects to be called after the `_` has been consumed.
    pub(super) fn consume_suffix_name(&mut self) {
        while self.current < self.bytes.len() && self.bytes[self.current].is_ascii_alphanumeric() {
            self.current += 1;
            self.column += 1;
        }
    }

    /// Create an error token and collect an error for an invalid number literal.
    pub(super) fn error_invalid_number(&mut self) -> Token<'src> {
        let span = crate::Span::new_with_end(
            self.start,
            self.current,
            self.start_line,
            self.start_column,
            self.line,
            self.column,
        );
        let error = crate::errors::LexerError::InvalidNumber { span: span.into() };
        tracing::debug!(
            line = self.start_line,
            col = self.start_column,
            "lexer error: invalid number"
        );
        let message = "invalid number literal".to_string();
        self.errors.push(error);
        Token::new(TokenType::Error, message, span)
    }
}
