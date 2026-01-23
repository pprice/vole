use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;
use crate::Span;
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse a when expression (subject-less conditional chains)
    /// Syntax: `when { cond1 => result1, cond2 => result2, _ => default }`
    pub(super) fn when_expr(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'when'

        // Expect opening brace
        self.consume(TokenType::LBrace, "expected '{' after when")?;
        self.skip_newlines();

        // Parse arms
        let mut arms = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            arms.push(self.when_arm()?);
            self.skip_newlines();
        }

        let end_span = self.current.span;
        self.consume(TokenType::RBrace, "expected '}' after when arms")?;

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::When(Box::new(WhenExpr {
                arms,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse a single when arm
    fn when_arm(&mut self) -> Result<WhenArm, ParseError> {
        let start_span = self.current.span;

        // Check for wildcard `_` (always matches)
        let condition = if self.check(TokenType::Identifier) && self.current.lexeme == "_" {
            self.advance(); // consume '_'
            None
        } else {
            // Parse condition expression
            Some(self.expression(0)?)
        };

        // Expect fat arrow
        self.consume(TokenType::FatArrow, "expected '=>' after when condition")?;

        // Parse body expression
        let body = self.expression(0)?;

        let end_span = body.span;
        Ok(WhenArm {
            condition,
            body,
            span: start_span.merge(end_span),
        })
    }

    /// Parse a match expression
    pub(super) fn match_expr(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'match'

        // Parse the scrutinee (the value being matched)
        let scrutinee = self.expression(0)?;

        // Expect opening brace
        self.consume(TokenType::LBrace, "expected '{' after match expression")?;
        self.skip_newlines();

        // Parse arms
        let mut arms = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            arms.push(self.match_arm()?);
            self.skip_newlines();
        }

        let end_span = self.current.span;
        self.consume(TokenType::RBrace, "expected '}' after match arms")?;

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Match(Box::new(MatchExpr {
                scrutinee,
                arms,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse a single match arm
    fn match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;

        // Parse pattern
        let pattern = self.pattern()?;

        // Optional guard: `if <cond>`
        let guard = if self.match_token(TokenType::KwIf) {
            Some(self.expression(0)?)
        } else {
            None
        };

        // Expect fat arrow
        self.consume(TokenType::FatArrow, "expected '=>' after pattern")?;

        // Parse body expression
        let body = self.expression(0)?;

        let end_span = body.span;
        Ok(MatchArm {
            pattern,
            guard,
            body,
            span: start_span.merge(end_span),
        })
    }

    /// Parse a pattern
    pub(super) fn pattern(&mut self) -> Result<Pattern, ParseError> {
        let token = self.current.clone();

        // Handle success pattern: success, success x, success Type
        if token.ty == TokenType::KwSuccess {
            let start_span = token.span;
            self.advance(); // consume 'success'

            // Check if there's an inner pattern (look for => or if which end a pattern)
            if self.check(TokenType::FatArrow) || self.check(TokenType::KwIf) {
                // Bare success pattern
                return Ok(Pattern::Success {
                    inner: None,
                    span: start_span,
                });
            }

            // Parse inner pattern
            let inner = self.pattern()?;
            let end_span = self.get_pattern_span(&inner);
            return Ok(Pattern::Success {
                inner: Some(Box::new(inner)),
                span: start_span.merge(end_span),
            });
        }

        // Handle error pattern: error, error e, error DivByZero, error DivByZero { x }
        if token.ty == TokenType::KwError {
            let start_span = token.span;
            self.advance(); // consume 'error'

            // Check if there's an inner pattern
            if self.check(TokenType::FatArrow) || self.check(TokenType::KwIf) {
                // Bare error pattern
                return Ok(Pattern::Error {
                    inner: None,
                    span: start_span,
                });
            }

            // Parse inner pattern
            let inner = self.pattern()?;
            let end_span = self.get_pattern_span(&inner);
            return Ok(Pattern::Error {
                inner: Some(Box::new(inner)),
                span: start_span.merge(end_span),
            });
        }

        // Check for type keyword patterns (primitives and nil)
        if let Some(type_expr) = self.token_to_type_expr(&token) {
            self.advance();
            return Ok(Pattern::Type {
                type_expr,
                span: token.span,
            });
        }

        match token.ty {
            // Val pattern: val x (compares against existing variable)
            TokenType::KwVal => {
                let start_span = token.span;
                self.advance(); // consume 'val'
                let name_token = self.current.clone();
                if name_token.ty != TokenType::Identifier {
                    return Err(ParseError::new(
                        ParserError::ExpectedExpression {
                            found: name_token.ty.as_str().to_string(),
                            span: name_token.span.into(),
                        },
                        name_token.span,
                    ));
                }
                self.advance(); // consume identifier
                let name = self.interner.intern(&name_token.lexeme);
                Ok(Pattern::Val {
                    name,
                    span: start_span.merge(name_token.span),
                })
            }
            // Wildcard: _
            TokenType::Identifier if token.lexeme == "_" => {
                self.advance();
                Ok(Pattern::Wildcard(token.span))
            }
            // Identifier - could be binding pattern, type pattern, or type destructure (resolved in analyzer)
            TokenType::Identifier => {
                self.advance();
                let name = self.interner.intern(&token.lexeme);

                // Check for record destructure pattern: TypeName { x, y }
                if self.check(TokenType::LBrace) {
                    return self.parse_typed_record_pattern(name, token.span);
                }

                Ok(Pattern::Identifier {
                    name,
                    span: token.span,
                })
            }
            // Integer literal pattern
            TokenType::IntLiteral => {
                let expr = self.primary()?;
                Ok(Pattern::Literal(expr))
            }
            // Negative integer pattern: -5
            TokenType::Minus => {
                let start_span = self.current.span;
                self.advance(); // consume '-'
                let operand = self.primary()?;
                let span = start_span.merge(operand.span);
                Ok(Pattern::Literal(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Unary(Box::new(UnaryExpr {
                        op: UnaryOp::Neg,
                        operand,
                    })),
                    span,
                }))
            }
            // Float literal pattern
            TokenType::FloatLiteral => {
                let expr = self.primary()?;
                Ok(Pattern::Literal(expr))
            }
            // String literal pattern
            TokenType::StringLiteral | TokenType::RawStringLiteral => {
                let expr = self.primary()?;
                Ok(Pattern::Literal(expr))
            }
            // Boolean literal patterns
            TokenType::KwTrue | TokenType::KwFalse => {
                let expr = self.primary()?;
                Ok(Pattern::Literal(expr))
            }
            _ => Err(ParseError::new(
                ParserError::ExpectedExpression {
                    found: token.ty.as_str().to_string(),
                    span: token.span.into(),
                },
                token.span,
            )),
        }
    }

    /// Parse a typed record destructure pattern: TypeName { x, y } or TypeName { x: a, y: b }
    fn parse_typed_record_pattern(
        &mut self,
        type_name: Symbol,
        start_span: Span,
    ) -> Result<Pattern, ParseError> {
        self.advance(); // consume '{'
        self.skip_newlines();

        let mut fields = Vec::new();

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Parse field: name or name: binding
            let field_token = self.current.clone();
            self.consume(TokenType::Identifier, "expected field name")?;
            let field_name = self.interner.intern(&field_token.lexeme);
            let mut field_end_span = field_token.span;

            let binding = if self.match_token(TokenType::Colon) {
                // Renamed binding: { x: alias }
                let binding_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected binding name after ':'")?;
                field_end_span = binding_token.span;
                self.interner.intern(&binding_token.lexeme)
            } else {
                // Same name binding: { x }
                field_name
            };

            fields.push(RecordFieldPattern {
                field_name,
                binding,
                span: field_token.span.merge(field_end_span),
            });

            if !self.match_token(TokenType::Comma) {
                break;
            }
            self.skip_newlines();
        }

        let end_span = self.current.span;
        self.consume(TokenType::RBrace, "expected '}' after record pattern")?;

        Ok(Pattern::Record {
            type_name: Some(type_name),
            fields,
            span: start_span.merge(end_span),
        })
    }

    /// Get the span from a pattern
    pub(super) fn get_pattern_span(&self, pattern: &Pattern) -> Span {
        match pattern {
            Pattern::Wildcard(s) => *s,
            Pattern::Identifier { span, .. } => *span,
            Pattern::Type { span, .. } => *span,
            Pattern::Val { span, .. } => *span,
            Pattern::Success { span, .. } => *span,
            Pattern::Error { span, .. } => *span,
            Pattern::Tuple { span, .. } => *span,
            Pattern::Record { span, .. } => *span,
            Pattern::Literal(expr) => expr.span,
        }
    }
}
