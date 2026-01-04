// src/frontend/parse_string.rs
//
// String parsing functionality for the Vole parser.
// This module contains methods for parsing string literals and interpolated strings.

use super::TokenType;
use super::ast::{Expr, ExprKind, StringPart};
use super::parser::{ParseError, Parser};
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse an interpolated string
    pub(crate) fn parse_interpolated_string(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        let mut parts = Vec::new();

        // Process the start token: "text{
        let start_content = self.process_interp_start(&self.current.lexeme.clone());
        if !start_content.is_empty() {
            parts.push(StringPart::Literal(start_content));
        }
        self.advance();

        loop {
            // Parse the expression inside {}
            let expr = self.expression(0)?;
            parts.push(StringPart::Expr(Box::new(expr)));

            match self.current.ty {
                TokenType::StringInterpMiddle => {
                    // }text{ - there's more
                    let middle_content = self.process_interp_middle(&self.current.lexeme.clone());
                    if !middle_content.is_empty() {
                        parts.push(StringPart::Literal(middle_content));
                    }
                    self.advance();
                }
                TokenType::StringInterpEnd => {
                    // }text" - we're done
                    let end_content = self.process_interp_end(&self.current.lexeme.clone());
                    if !end_content.is_empty() {
                        parts.push(StringPart::Literal(end_content));
                    }
                    let end_span = self.current.span;
                    self.advance();
                    let span = start_span.merge(end_span);
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::InterpolatedString(parts),
                        span,
                    });
                }
                _ => {
                    return Err(ParseError::new(
                        ParserError::UnexpectedToken {
                            token: "unterminated string interpolation".to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
            }
        }
    }

    /// Process a string literal content (remove quotes, handle escapes)
    pub(crate) fn process_string_content(&self, lexeme: &str) -> String {
        // Remove surrounding quotes
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process the start of an interpolated string: "text{ -> text
    fn process_interp_start(&self, lexeme: &str) -> String {
        // Remove leading " and trailing {
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process the middle of an interpolated string: }text{ -> text
    fn process_interp_middle(&self, lexeme: &str) -> String {
        // Remove leading } and trailing {
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process the end of an interpolated string: }text" -> text
    fn process_interp_end(&self, lexeme: &str) -> String {
        // Remove leading } and trailing "
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process escape sequences in a string
    fn process_escapes(&self, s: &str) -> String {
        let mut result = String::new();
        let mut chars = s.chars();

        while let Some(c) = chars.next() {
            if c == '\\' {
                match chars.next() {
                    Some('n') => result.push('\n'),
                    Some('t') => result.push('\t'),
                    Some('r') => result.push('\r'),
                    Some('\\') => result.push('\\'),
                    Some('"') => result.push('"'),
                    Some('{') => result.push('{'),
                    Some('}') => result.push('}'),
                    Some(other) => {
                        result.push('\\');
                        result.push(other);
                    }
                    None => result.push('\\'),
                }
            } else {
                result.push(c);
            }
        }

        result
    }
}
