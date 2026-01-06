use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;
use crate::errors::ParserError;
use crate::frontend::Span;

impl<'src> Parser<'src> {
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
            // Identifier - could be binding pattern or type pattern (resolved in analyzer)
            TokenType::Identifier => {
                self.advance();
                let name = self.interner.intern(&token.lexeme);
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
            TokenType::StringLiteral => {
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

    /// Get the span from a pattern
    pub(super) fn get_pattern_span(&self, pattern: &Pattern) -> Span {
        match pattern {
            Pattern::Wildcard(s) => *s,
            Pattern::Identifier { span, .. } => *span,
            Pattern::Type { span, .. } => *span,
            Pattern::Val { span, .. } => *span,
            Pattern::Success { span, .. } => *span,
            Pattern::Error { span, .. } => *span,
            Pattern::Literal(expr) => expr.span,
        }
    }
}
