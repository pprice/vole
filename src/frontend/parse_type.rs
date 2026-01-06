// src/frontend/parse_type.rs
//
// Type parsing functionality for the Vole parser.
// This module contains methods for parsing type expressions and function parameters.

use super::TokenType;
use super::ast::{Param, PrimitiveType, TypeExpr};
use super::parser::{ParseError, Parser};
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse a function parameter (name: Type)
    pub(super) fn parse_param(&mut self) -> Result<Param, ParseError> {
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected parameter name")?;
        let name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::Colon, "expected ':' after parameter name")?;
        let ty = self.parse_type()?;

        Ok(Param {
            name,
            ty,
            span: name_token.span,
        })
    }

    /// Parse a type expression, handling optionals (T?) and unions (A | B)
    pub(super) fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        // Parse the base type first
        let mut base = self.parse_base_type()?;

        // Check for optional suffix: T?
        while self.match_token(TokenType::Question) {
            base = TypeExpr::Optional(Box::new(base));
        }

        // Check for union: A | B | C
        if self.check(TokenType::Pipe) {
            let mut variants = vec![base];
            while self.match_token(TokenType::Pipe) {
                let mut variant = self.parse_base_type()?;
                // Handle optional on each variant
                while self.match_token(TokenType::Question) {
                    variant = TypeExpr::Optional(Box::new(variant));
                }
                variants.push(variant);
            }
            return Ok(TypeExpr::Union(variants));
        }

        Ok(base)
    }

    /// Parse a base type (primitives, arrays, function types, named types)
    fn parse_base_type(&mut self) -> Result<TypeExpr, ParseError> {
        let token = self.current.clone();
        match token.ty {
            TokenType::LParen => {
                // Function type: (T, T) -> R
                self.advance(); // consume '('

                let mut param_types = Vec::new();
                if !self.check(TokenType::RParen) {
                    param_types.push(self.parse_type()?);
                    while self.match_token(TokenType::Comma) {
                        param_types.push(self.parse_type()?);
                    }
                }
                self.consume(
                    TokenType::RParen,
                    "expected ')' after function parameter types",
                )?;
                self.consume(TokenType::Arrow, "expected '->' after function parameters")?;
                let return_type = self.parse_type()?;

                Ok(TypeExpr::Function {
                    params: param_types,
                    return_type: Box::new(return_type),
                })
            }
            TokenType::LBracket => {
                self.advance(); // consume '['
                let elem_type = self.parse_type()?;
                self.consume(TokenType::RBracket, "expected ']' after array element type")?;
                Ok(TypeExpr::Array(Box::new(elem_type)))
            }
            TokenType::KwNil => {
                self.advance();
                Ok(TypeExpr::Nil)
            }
            TokenType::KwDone => {
                self.advance();
                Ok(TypeExpr::Done)
            }
            TokenType::KwIterator => {
                self.advance(); // consume 'Iterator'
                self.consume(TokenType::Lt, "expected '<' after Iterator")?;
                let elem_type = self.parse_type()?;
                self.consume(TokenType::Gt, "expected '>' after Iterator element type")?;
                Ok(TypeExpr::Iterator(Box::new(elem_type)))
            }
            TokenType::KwI8 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I8))
            }
            TokenType::KwI16 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I16))
            }
            TokenType::KwI32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I32))
            }
            TokenType::KwI64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I64))
            }
            TokenType::KwI128 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I128))
            }
            TokenType::KwU8 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U8))
            }
            TokenType::KwU16 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U16))
            }
            TokenType::KwU32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U32))
            }
            TokenType::KwU64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U64))
            }
            TokenType::KwF32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::F32))
            }
            TokenType::KwF64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::F64))
            }
            TokenType::KwBool => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::Bool))
            }
            TokenType::KwString => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::String))
            }
            TokenType::KwSelfType => {
                self.advance();
                Ok(TypeExpr::SelfType)
            }
            TokenType::KwFallible => {
                self.advance(); // consume 'fallible'
                self.consume(TokenType::LParen, "expected '(' after fallible")?;
                let success_type = self.parse_type()?;
                self.consume(TokenType::Comma, "expected ',' in fallible type")?;
                let error_type = self.parse_type()?;
                self.consume(TokenType::RParen, "expected ')' after fallible type")?;
                Ok(TypeExpr::Fallible {
                    success_type: Box::new(success_type),
                    error_type: Box::new(error_type),
                })
            }
            TokenType::Identifier => {
                self.advance();
                let sym = self.interner.intern(&token.lexeme);

                // Check for generic arguments: Foo<T, U>
                if self.check(TokenType::Lt) {
                    self.advance(); // consume '<'
                    let mut args = Vec::new();
                    if !self.check(TokenType::Gt) {
                        args.push(self.parse_type()?);
                        while self.match_token(TokenType::Comma) {
                            args.push(self.parse_type()?);
                        }
                    }
                    self.consume(TokenType::Gt, "expected '>' after type arguments")?;
                    Ok(TypeExpr::Generic { name: sym, args })
                } else {
                    Ok(TypeExpr::Named(sym))
                }
            }
            _ => Err(ParseError::new(
                ParserError::ExpectedType {
                    span: token.span.into(),
                },
                token.span,
            )),
        }
    }
}
