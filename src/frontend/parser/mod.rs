// src/frontend/parser/mod.rs

use crate::errors::{LexerError, ParserError};
use crate::frontend::{Interner, Lexer, Span, Token, TokenType, ast::*};

pub struct Parser<'src> {
    pub(super) lexer: Lexer<'src>,
    pub(super) current: Token,
    pub(super) previous: Token,
    pub(super) interner: Interner,
    next_node_id: u32,
}

/// A parse error wrapping a miette-enabled ParserError
#[derive(Debug)]
pub struct ParseError {
    pub error: ParserError,
    pub span: Span,
}

impl ParseError {
    /// Create a new parse error
    pub fn new(error: ParserError, span: Span) -> Self {
        Self { error, span }
    }
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        let mut interner = Interner::new();
        // Pre-intern "self" so it's always available for method bodies
        interner.intern("self");
        Self {
            lexer,
            current,
            previous: Token::new(TokenType::Eof, "", Span::default()),
            interner,
            next_node_id: 0,
        }
    }

    /// Create a parser with a custom file name for diagnostics
    pub fn with_file(source: &'src str, file: &str) -> Self {
        let mut lexer = Lexer::new_with_file(source, file);
        let current = lexer.next_token();
        let mut interner = Interner::new();
        // Pre-intern "self" so it's always available for method bodies
        interner.intern("self");
        Self {
            lexer,
            current,
            previous: Token::new(TokenType::Eof, "", Span::default()),
            interner,
            next_node_id: 0,
        }
    }

    /// Generate a unique node ID
    pub(super) fn next_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    pub fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.expression(0)
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut declarations = Vec::new();
        self.skip_newlines();

        while !self.check(TokenType::Eof) {
            declarations.push(self.declaration()?);
            self.skip_newlines();
        }

        Ok(Program { declarations })
    }

    pub(super) fn skip_newlines(&mut self) {
        while self.current.ty == TokenType::Newline {
            self.current = self.lexer.next_token();
        }
    }

    /// Get a reference to the interner
    pub fn interner(&self) -> &Interner {
        &self.interner
    }

    /// Get a mutable reference to the interner
    pub fn interner_mut(&mut self) -> &mut Interner {
        &mut self.interner
    }

    /// Consume the parser and return the interner
    pub fn into_interner(self) -> Interner {
        self.interner
    }

    /// Take lexer errors (for diagnostic rendering)
    pub fn take_lexer_errors(&mut self) -> Vec<LexerError> {
        self.lexer.take_errors()
    }

    /// Advance to the next token
    pub(super) fn advance(&mut self) {
        self.previous = std::mem::replace(&mut self.current, self.lexer.next_token());
    }

    /// Check if the current token matches the given type
    pub(super) fn check(&self, ty: TokenType) -> bool {
        self.current.ty == ty
    }

    /// Consume the current token if it matches, otherwise return false
    pub(super) fn match_token(&mut self, ty: TokenType) -> bool {
        if self.check(ty) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Require a token of the given type, or return an error
    pub(super) fn consume(&mut self, ty: TokenType, msg: &str) -> Result<(), ParseError> {
        if self.check(ty) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::new(
                ParserError::ExpectedToken {
                    expected: msg.to_string(),
                    found: self.current.ty.as_str().to_string(),
                    span: self.current.span.into(),
                },
                self.current.span,
            ))
        }
    }

    /// Create an unexpected token error at the current position
    #[allow(dead_code)] // Will be used in subsequent refactor tasks
    pub(super) fn unexpected_token_error(&self) -> ParseError {
        ParseError::new(
            ParserError::UnexpectedToken {
                token: self.current.ty.as_str().to_string(),
                span: self.current.span.into(),
            },
            self.current.span,
        )
    }
}

#[cfg(test)]
mod tests;
