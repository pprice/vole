// src/frontend/parse_external.rs
//
// External block parsing: external("provider:module") { func declarations }

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::TokenType;
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse an external block: external("module_path") { funcs }
    pub(super) fn parse_external_block(&mut self) -> Result<ExternalBlock, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'external'

        // Parse ("module_path")
        self.consume(TokenType::LParen, "expected '(' after 'external'")?;

        if !self.check(TokenType::StringLiteral) {
            return Err(ParseError::new(
                ParserError::ExpectedModulePath {
                    span: self.current.span.into(),
                },
                self.current.span,
            ));
        }

        let path_token = self.current.clone();
        self.advance();
        let module_path = self.process_string_content(&path_token.lexeme);

        // Validate module path format (provider:module)
        if !module_path.contains(':') {
            return Err(ParseError::new(
                ParserError::InvalidExternalModulePath {
                    span: path_token.span.into(),
                },
                path_token.span,
            ));
        }

        self.consume(TokenType::RParen, "expected ')' after module path")?;
        self.consume(TokenType::LBrace, "expected '{' to start external block")?;
        self.skip_newlines();

        // Parse external function declarations
        let mut functions = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            functions.push(self.parse_external_func()?);
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close external block")?;
        let span = start_span.merge(self.previous.span);

        Ok(ExternalBlock {
            module_path,
            functions,
            is_default: false, // Caller sets to true if 'default' keyword was present
            span,
        })
    }

    /// Parse a single external function declaration
    /// Forms:
    ///   func name(params) -> type
    ///   func "native_name" as name(params) -> type
    pub(super) fn parse_external_func(&mut self) -> Result<ExternalFunc, ParseError> {
        let start_span = self.current.span;
        self.consume(TokenType::KwFunc, "expected 'func' in external block")?;

        // Check for "native_name" as vole_name syntax
        let native_name = if self.check(TokenType::StringLiteral) {
            let name_token = self.current.clone();
            self.advance();
            let name = self.process_string_content(&name_token.lexeme);

            // Expect 'as' keyword
            if !self.match_token(TokenType::KwAs) {
                return Err(ParseError::new(
                    ParserError::ExpectedAs {
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ));
            }
            Some(name)
        } else {
            None
        };

        // Parse vole-facing function name
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected function name")?;
        let vole_name = self.interner.intern(&name_token.lexeme);

        // Parse parameter list
        self.consume(TokenType::LParen, "expected '(' after function name")?;
        let mut params = Vec::new();
        if !self.check(TokenType::RParen) {
            loop {
                params.push(self.parse_param()?);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RParen, "expected ')' after parameters")?;

        // Parse optional return type
        let return_type = if self.match_token(TokenType::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let span = start_span.merge(self.previous.span);

        Ok(ExternalFunc {
            native_name,
            vole_name,
            params,
            return_type,
            span,
        })
    }
}
