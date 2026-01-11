// src/frontend/parse_generic.rs
//
// Generic type parameter parsing for Vole.

use super::TokenType;
use super::ast::{TypeConstraint, TypeExpr, TypeParam};
use super::parser::{ParseError, Parser};

impl<'src> Parser<'src> {
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
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected type parameter name")?;
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

    /// Parse a type constraint: Interface, Type1 | Type2, or { fields/methods }
    fn parse_type_constraint(&mut self) -> Result<TypeConstraint, ParseError> {
        // Parse first type
        let first = self.parse_type()?;

        // Check for union constraint: T: i32 | i64
        if self.check(TokenType::Pipe) {
            let mut types = vec![first];
            while self.match_token(TokenType::Pipe) {
                types.push(self.parse_type()?);
            }
            return Ok(TypeConstraint::Union(types));
        }

        // Check what kind of constraint we have
        match first {
            TypeExpr::Named(sym) => Ok(TypeConstraint::Interface(sym)),
            TypeExpr::Structural { fields, methods } => {
                Ok(TypeConstraint::Structural { fields, methods })
            }
            _ => Ok(TypeConstraint::Union(vec![first])),
        }
    }
}
