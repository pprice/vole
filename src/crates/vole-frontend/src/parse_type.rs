// src/frontend/parse_type.rs
//
// Type parsing functionality for the Vole parser.
// This module contains methods for parsing type expressions and function parameters.

use super::TokenType;
use super::ast::{Param, StructuralField, StructuralMethod, TypeExpr, TypeExprKind};
use super::parser::{ParseError, Parser};
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse a function parameter (name: Type)
    pub(super) fn parse_param(&mut self) -> Result<Param, ParseError> {
        // Parse optional annotations before the parameter
        let annotations = if self.check(TokenType::At) {
            self.parse_annotations()?
        } else {
            Vec::new()
        };

        let param_span = annotations
            .first()
            .map(|a| a.span)
            .unwrap_or(self.current.span);
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected parameter name")?;
        let name = self.interner.intern(&name_token.lexeme);

        // Check for missing type annotation
        if !self.check(TokenType::Colon) {
            return Err(ParseError::new(
                ParserError::MissingTypeAnnotation {
                    name: name_token.lexeme.to_string(),
                    span: name_token.span.into(),
                },
                name_token.span,
            ));
        }
        self.advance(); // consume ':'
        let ty = self.parse_type()?;

        // Parse optional default value: param: Type = expr
        let default_value = if self.match_token(TokenType::Eq) {
            Some(Box::new(self.expression(0)?))
        } else {
            None
        };

        Ok(Param {
            name,
            ty,
            default_value,
            annotations,
            span: param_span,
        })
    }

    /// Parse a type expression, handling optionals (T?) and unions (A | B)
    pub(super) fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        let start_span = self.current.span;

        // Parse the base type first
        let mut base = self.parse_base_type()?;

        // Check for optional suffix: T?
        while self.match_token(TokenType::Question) {
            let span = start_span.merge(self.previous.span);
            base = TypeExpr::new(TypeExprKind::Optional(Box::new(base)), span);
        }

        // Check for type combination: A + B + C (binds tighter than |)
        if self.check(TokenType::Plus) {
            let mut parts = vec![base];
            while self.match_token(TokenType::Plus) {
                let mut part = self.parse_base_type()?;
                // Handle optional on each part
                while self.match_token(TokenType::Question) {
                    let span = start_span.merge(self.previous.span);
                    part = TypeExpr::new(TypeExprKind::Optional(Box::new(part)), span);
                }
                parts.push(part);
            }
            let span = start_span.merge(self.previous.span);
            return Ok(TypeExpr::new(TypeExprKind::Combination(parts), span));
        }

        // Check for union: A | B | C
        if self.check(TokenType::Pipe) {
            let mut variants = vec![base];
            while self.match_token(TokenType::Pipe) {
                let mut variant = self.parse_base_type()?;
                // Handle optional on each variant
                while self.match_token(TokenType::Question) {
                    let span = start_span.merge(self.previous.span);
                    variant = TypeExpr::new(TypeExprKind::Optional(Box::new(variant)), span);
                }
                variants.push(variant);
            }
            let span = start_span.merge(self.previous.span);
            return Ok(TypeExpr::new(TypeExprKind::Union(variants), span));
        }

        Ok(base)
    }

    /// Parse a base type (primitives, arrays, function types, named types)
    /// Public within the crate so parse_generic.rs can use it for constraint parsing.
    pub(super) fn parse_base_type(&mut self) -> Result<TypeExpr, ParseError> {
        let token = self.current.clone();

        // Check for primitive type keywords first
        if let Some(prim) = token.ty.to_primitive_type() {
            self.advance();
            return Ok(TypeExpr::new(TypeExprKind::Primitive(prim), token.span));
        }

        match token.ty {
            TokenType::LParen => {
                // Could be:
                // - Function type: (T, T) -> R
                // - Grouping parentheses: (A | B)
                self.advance(); // consume '('

                let mut param_types = Vec::new();
                if !self.check(TokenType::RParen) {
                    param_types.push(self.parse_type()?);
                    while self.match_token(TokenType::Comma) {
                        param_types.push(self.parse_type()?);
                    }
                }
                self.consume(TokenType::RParen, "expected ')' after type expression")?;

                // If followed by ->, it's a function type
                if self.match_token(TokenType::Arrow) {
                    let return_type = self.parse_type()?;
                    let span = token.span.merge(self.previous.span);
                    Ok(TypeExpr::new(
                        TypeExprKind::Function {
                            params: param_types,
                            return_type: Box::new(return_type),
                        },
                        span,
                    ))
                } else if param_types.len() == 1 {
                    // Single type in parens - grouping
                    Ok(param_types.into_iter().next().expect("len == 1"))
                } else {
                    // Multiple types without -> is ambiguous/invalid
                    // (could be tuple, but we use [] for tuples)
                    Err(ParseError::new(
                        ParserError::ExpectedToken {
                            expected: "'->' for function type".to_string(),
                            found: self.current.ty.as_str().to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ))
                }
            }
            TokenType::LBracket => {
                self.advance(); // consume '['
                let first_type = self.parse_type()?;

                // Check what follows the first type
                match self.current.ty {
                    TokenType::RBracket => {
                        // [T] - dynamic array
                        self.advance(); // consume ']'
                        let span = token.span.merge(self.previous.span);
                        Ok(TypeExpr::new(
                            TypeExprKind::Array(Box::new(first_type)),
                            span,
                        ))
                    }
                    TokenType::Semicolon => {
                        // [T; N] - fixed-size array
                        self.advance(); // consume ';'
                        let size = self.parse_fixed_array_size()?;
                        self.consume(TokenType::RBracket, "expected ']' after fixed array size")?;
                        let span = token.span.merge(self.previous.span);
                        Ok(TypeExpr::new(
                            TypeExprKind::FixedArray {
                                element: Box::new(first_type),
                                size,
                            },
                            span,
                        ))
                    }
                    TokenType::Comma => {
                        // [T, U, ...] - tuple
                        let mut elements = vec![first_type];
                        while self.check(TokenType::Comma) {
                            self.advance(); // consume ','
                            // Allow trailing comma
                            if self.check(TokenType::RBracket) {
                                break;
                            }
                            elements.push(self.parse_type()?);
                        }
                        self.consume(TokenType::RBracket, "expected ']' after tuple types")?;
                        let span = token.span.merge(self.previous.span);
                        Ok(TypeExpr::new(TypeExprKind::Tuple(elements), span))
                    }
                    _ => {
                        self.consume(
                            TokenType::RBracket,
                            "expected ']', ';', or ',' in bracket type",
                        )?;
                        let span = token.span.merge(self.previous.span);
                        Ok(TypeExpr::new(
                            TypeExprKind::Array(Box::new(first_type)),
                            span,
                        )) // unreachable
                    }
                }
            }
            TokenType::KwNever => {
                self.advance();
                Ok(TypeExpr::new(TypeExprKind::Never, token.span))
            }
            TokenType::KwUnknown => {
                self.advance();
                Ok(TypeExpr::new(TypeExprKind::Unknown, token.span))
            }
            TokenType::KwHandle => {
                self.advance();
                Ok(TypeExpr::new(TypeExprKind::Handle, token.span))
            }
            TokenType::KwSelfType => {
                self.advance();
                Ok(TypeExpr::new(TypeExprKind::SelfType, token.span))
            }
            TokenType::KwFallible => {
                self.advance(); // consume 'fallible'
                self.consume(TokenType::LParen, "expected '(' after fallible")?;
                let success_type = self.parse_type()?;
                self.consume(TokenType::Comma, "expected ',' in fallible type")?;
                let error_type = self.parse_type()?;
                self.consume(TokenType::RParen, "expected ')' after fallible type")?;
                let span = token.span.merge(self.previous.span);
                Ok(TypeExpr::new(
                    TypeExprKind::Fallible {
                        success_type: Box::new(success_type),
                        error_type: Box::new(error_type),
                    },
                    span,
                ))
            }
            TokenType::LBrace => {
                // Structural type: { name: Type, func method() -> Type }
                self.advance(); // consume '{'
                self.parse_structural_type(token.span)
            }
            TokenType::Identifier => {
                self.advance();
                let first_sym = self.interner.intern(&token.lexeme);

                // Check for dotted path: mod.Type or mod.Type<T>
                if self.check(TokenType::Dot) {
                    let mut segments = vec![first_sym];
                    while self.match_token(TokenType::Dot) {
                        let seg_token = self.current.clone();
                        self.consume(TokenType::Identifier, "expected identifier after '.'")?;
                        segments.push(self.interner.intern(&seg_token.lexeme));
                    }

                    // Check for generic arguments: mod.Type<T>
                    let args = if self.check(TokenType::Lt) {
                        self.advance(); // consume '<'
                        let mut type_args = Vec::new();
                        if !self.check_gt_in_type_context() {
                            type_args.push(self.parse_type()?);
                            while self.match_token(TokenType::Comma) {
                                type_args.push(self.parse_type()?);
                            }
                        }
                        self.consume_gt_in_type_context()?;
                        type_args
                    } else {
                        Vec::new()
                    };

                    let span = token.span.merge(self.previous.span);
                    return Ok(TypeExpr::new(
                        TypeExprKind::QualifiedPath { segments, args },
                        span,
                    ));
                }

                // Check for generic arguments: Foo<T, U>
                if self.check(TokenType::Lt) {
                    self.advance(); // consume '<'
                    let mut args = Vec::new();
                    if !self.check_gt_in_type_context() {
                        args.push(self.parse_type()?);
                        while self.match_token(TokenType::Comma) {
                            args.push(self.parse_type()?);
                        }
                    }
                    self.consume_gt_in_type_context()?;
                    let span = token.span.merge(self.previous.span);
                    Ok(TypeExpr::new(
                        TypeExprKind::Generic {
                            name: first_sym,
                            args,
                        },
                        span,
                    ))
                } else {
                    Ok(TypeExpr::new(TypeExprKind::Named(first_sym), token.span))
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

    /// Parse the size part of a fixed array type [T; SIZE]
    fn parse_fixed_array_size(&mut self) -> Result<usize, ParseError> {
        self.parse_usize_literal()
    }

    /// Parse a structural method parameter: either `name: Type` or bare `Type`.
    /// In both cases, only the type is kept (parameter names are discarded).
    fn parse_structural_method_param(&mut self) -> Result<TypeExpr, ParseError> {
        // Check for `name: Type` pattern (identifier followed by colon)
        if self.check(TokenType::Identifier) {
            let next = self.peek_token();
            if next.ty == TokenType::Colon {
                // Skip the parameter name and colon, parse just the type
                self.advance(); // consume identifier (param name)
                self.advance(); // consume ':'
                return self.parse_type();
            }
        }
        // Otherwise parse as bare type
        self.parse_type()
    }

    /// Parse a structural type: { name: Type, func method() -> Type }
    /// Called after consuming the opening '{'.
    fn parse_structural_type(&mut self, start_span: crate::Span) -> Result<TypeExpr, ParseError> {
        let mut fields = Vec::new();
        let mut methods = Vec::new();

        // Handle empty structural type
        if self.check(TokenType::RBrace) {
            self.advance(); // consume '}'
            let span = start_span.merge(self.previous.span);
            return Ok(TypeExpr::new(
                TypeExprKind::Structural { fields, methods },
                span,
            ));
        }

        loop {
            let member_token = self.current.clone();

            if self.check(TokenType::KwFunc) {
                // Method: func name(params) -> ReturnType
                self.advance(); // consume 'func'
                let name_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected method name")?;
                let name = self.interner.intern(&name_token.lexeme);

                self.consume(TokenType::LParen, "expected '(' after method name")?;
                let mut params = Vec::new();
                if !self.check(TokenType::RParen) {
                    params.push(self.parse_structural_method_param()?);
                    while self.match_token(TokenType::Comma) {
                        if self.check(TokenType::RParen) {
                            break; // trailing comma
                        }
                        params.push(self.parse_structural_method_param()?);
                    }
                }
                self.consume(TokenType::RParen, "expected ')' after method parameters")?;

                self.consume(TokenType::Arrow, "expected '->' after method parameters")?;
                let return_type = self.parse_type()?;

                methods.push(StructuralMethod {
                    name,
                    params,
                    return_type,
                    span: name_token.span,
                });
            } else if self.check(TokenType::Identifier) {
                // Field: name: Type
                self.advance(); // consume identifier
                let name = self.interner.intern(&member_token.lexeme);

                self.consume(TokenType::Colon, "expected ':' after field name")?;
                let ty = self.parse_type()?;

                fields.push(StructuralField {
                    name,
                    ty,
                    span: member_token.span,
                });
            } else {
                return Err(ParseError::new(
                    ParserError::ExpectedToken {
                        expected: "field or method".to_string(),
                        found: self.current.ty.as_str().to_string(),
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ));
            }

            // Check for comma or end
            if self.match_token(TokenType::Comma) {
                // Allow trailing comma
                if self.check(TokenType::RBrace) {
                    break;
                }
            } else {
                break;
            }
        }

        self.consume(TokenType::RBrace, "expected '}' after structural type")?;
        let span = start_span.merge(self.previous.span);
        Ok(TypeExpr::new(
            TypeExprKind::Structural { fields, methods },
            span,
        ))
    }
}
