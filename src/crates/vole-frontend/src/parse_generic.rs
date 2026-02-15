// src/frontend/parse_generic.rs
//
// Generic type parameter parsing for Vole.

use crate::errors::ParserError;

use super::TokenType;
use super::ast::{ConstraintInterface, TypeConstraint, TypeExpr, TypeExprKind, TypeParam};
use super::parser::{ParseError, Parser};

impl<'src> Parser<'src> {
    /// Try to parse type arguments at a call site: method<T, U>(...)
    /// Returns empty Vec if what follows '<' doesn't look like type args.
    /// Uses lookahead to disambiguate from comparison operators.
    pub(super) fn try_parse_call_type_args(&mut self) -> Result<Vec<TypeExpr>, ParseError> {
        self.try_parse_type_args_followed_by(TokenType::LParen)
    }

    /// Try to parse type arguments for a struct literal: Name<T, U> { ... }
    /// Returns empty Vec if what follows '<' doesn't look like type args for a struct.
    pub(super) fn try_parse_struct_type_args(&mut self) -> Result<Vec<TypeExpr>, ParseError> {
        self.try_parse_type_args_followed_by(TokenType::LBrace)
    }

    /// Parse type arguments (`<T, U>`) followed by the expected disambiguating token.
    /// Returns empty Vec and backtracks if parsing fails or the expected token is absent.
    fn try_parse_type_args_followed_by(
        &mut self,
        expected: TokenType,
    ) -> Result<Vec<TypeExpr>, ParseError> {
        if !self.check(TokenType::Lt) {
            return Ok(Vec::new());
        }

        // Save position for backtracking
        let saved_lexer = self.lexer.clone();
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        self.advance(); // consume '<'

        // Try to parse type list
        let mut types = Vec::new();
        if !self.check_gt_in_type_context() {
            loop {
                // Try to parse a type - if this fails, it's not type args
                let ty = match self.parse_type() {
                    Ok(t) => t,
                    Err(_) => {
                        // Restore and return empty
                        self.lexer = saved_lexer;
                        self.current = saved_current;
                        self.previous = saved_previous;
                        return Ok(Vec::new());
                    }
                };
                types.push(ty);

                if !self.match_token(TokenType::Comma) {
                    break;
                }
                // Allow trailing comma
                if self.check_gt_in_type_context() {
                    break;
                }
            }
        }

        // Must be followed by '>'
        if !self.check_gt_in_type_context() {
            // Restore and return empty
            self.lexer = saved_lexer;
            self.current = saved_current;
            self.previous = saved_previous;
            return Ok(Vec::new());
        }
        self.consume_gt_in_type_context()?;

        // Must be followed by the expected disambiguating token
        if !self.check(expected) {
            // Restore and return empty - this was comparison, not type args
            self.lexer = saved_lexer;
            self.current = saved_current;
            self.previous = saved_previous;
            return Ok(Vec::new());
        }

        Ok(types)
    }

    /// Parse optional type parameters: <T>, <T: Foo>, <A, B: Bar>
    /// Returns empty Vec if no '<' present.
    pub(super) fn parse_type_params(&mut self) -> Result<Vec<TypeParam>, ParseError> {
        if !self.check(TokenType::Lt) {
            return Ok(Vec::new());
        }
        self.advance(); // consume '<'

        let mut params = Vec::new();

        if !self.check_gt_in_type_context() {
            loop {
                let param = self.parse_type_param()?;
                params.push(param);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
                // Allow trailing comma
                if self.check_gt_in_type_context() {
                    break;
                }
            }
        }

        self.consume_gt_in_type_context()?;
        Ok(params)
    }

    /// Parse a single type parameter: T or T: Constraint
    fn parse_type_param(&mut self) -> Result<TypeParam, ParseError> {
        // Check for digit-starting type parameter (e.g., 1T)
        if self.current.ty == TokenType::IntLiteral {
            let digit_token = self.current.clone();
            let next = self.peek_token();
            // If next token is an identifier immediately adjacent, combine them
            let param_name =
                if next.ty == TokenType::Identifier && digit_token.span.end == next.span.start {
                    format!("{}{}", digit_token.lexeme, next.lexeme)
                } else {
                    digit_token.lexeme.to_string()
                };
            return Err(ParseError::new(
                ParserError::TypeParamStartsWithDigit {
                    name: param_name,
                    span: digit_token.span.into(),
                },
                digit_token.span,
            ));
        }

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected type parameter name")?;

        // Check for reserved __ prefix (used for synthetic types)
        if name_token.lexeme.starts_with("__") {
            return Err(ParseError::new(
                ParserError::TypeParamReservedPrefix {
                    name: name_token.lexeme.to_string(),
                    span: name_token.span.into(),
                },
                name_token.span,
            ));
        }

        let name = self.interner.intern(&name_token.lexeme);

        let constraint = if self.match_token(TokenType::Colon) {
            Some(self.parse_type_constraint()?)
        } else {
            None
        };

        Ok(TypeParam {
            name,
            constraint,
            span: name_token.span,
        })
    }

    /// Parse a type constraint: Interface, Interface + Interface, Type1 | Type2, or { fields/methods }
    fn parse_type_constraint(&mut self) -> Result<TypeConstraint, ParseError> {
        // Use parse_base_type instead of parse_type to avoid consuming '+' as type combination.
        // For constraints, '+' means multiple interface requirements, not type combination.
        let first = self.parse_base_type()?;

        // Check for union constraint: T: i32 | i64
        if self.check(TokenType::Pipe) {
            let mut types = vec![first];
            while self.match_token(TokenType::Pipe) {
                types.push(self.parse_base_type()?);
            }
            return Ok(TypeConstraint::Union(types));
        }

        // Check for multiple interface constraints: T: Hashable + Eq
        if self.check(TokenType::Plus) {
            // First must be a named type (interface), possibly parameterized
            let first_iface = match first.kind {
                TypeExprKind::Named(sym) => ConstraintInterface {
                    name: sym,
                    type_args: vec![],
                },
                TypeExprKind::Generic { name, args } => ConstraintInterface {
                    name,
                    type_args: args,
                },
                _ => {
                    return Err(ParseError::new(
                        ParserError::ExpectedToken {
                            expected: "interface name before '+'".to_string(),
                            found: "non-interface type".to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
            };
            let mut interfaces = vec![first_iface];
            while self.match_token(TokenType::Plus) {
                let next = self.parse_base_type()?;
                let iface = match next.kind {
                    TypeExprKind::Named(sym) => ConstraintInterface {
                        name: sym,
                        type_args: vec![],
                    },
                    TypeExprKind::Generic { name, args } => ConstraintInterface {
                        name,
                        type_args: args,
                    },
                    _ => {
                        return Err(ParseError::new(
                            ParserError::ExpectedToken {
                                expected: "interface name after '+'".to_string(),
                                found: "non-interface type".to_string(),
                                span: self.previous.span.into(),
                            },
                            self.previous.span,
                        ));
                    }
                };
                interfaces.push(iface);
            }
            return Ok(TypeConstraint::Interface(interfaces));
        }

        // Check what kind of constraint we have
        match first.kind {
            TypeExprKind::Named(sym) => Ok(TypeConstraint::Interface(vec![ConstraintInterface {
                name: sym,
                type_args: vec![],
            }])),
            TypeExprKind::Generic { name, args } => {
                Ok(TypeConstraint::Interface(vec![ConstraintInterface {
                    name,
                    type_args: args,
                }]))
            }
            TypeExprKind::Structural { fields, methods } => {
                Ok(TypeConstraint::Structural { fields, methods })
            }
            _ => Ok(TypeConstraint::Union(vec![first])),
        }
    }
}
