use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;

impl<'src> Parser<'src> {
    /// Parse a call expression (function call), index expressions, field access, and method calls
    pub(super) fn call(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.primary()?;

        loop {
            // Allow method chains to span multiple lines:
            // arr.iter()
            //    .map(...)
            //    .filter(...)
            // Only skip newlines if followed by . or ?. to continue the chain
            if self.check(TokenType::Newline) {
                // Peek past newlines to check for continuation tokens
                let mut peek_lexer = self.lexer.clone();
                loop {
                    let next = peek_lexer.next_token();
                    if next.ty != TokenType::Newline {
                        // Found non-newline token - check if continuation
                        if next.ty == TokenType::Dot || next.ty == TokenType::QuestionDot {
                            // It's a continuation - consume newlines and continue
                            self.skip_newlines();
                        } else {
                            // Not a continuation - break without consuming newlines
                            break;
                        }
                        break;
                    }
                }
                if self.check(TokenType::Newline) {
                    // We didn't consume newlines, so break
                    break;
                }
            }

            if self.match_token(TokenType::LParen) {
                expr = self.finish_call(expr)?;
            } else if self.match_token(TokenType::LBracket) {
                // Index expression: expr[index]
                let index = self.expression(0)?;
                let end_span = self.current.span;
                self.consume(TokenType::RBracket, "expected ']' after index")?;

                let span = expr.span.merge(end_span);
                expr = Expr {
                    id: self.next_id(),
                    kind: ExprKind::Index(Box::new(IndexExpr {
                        object: expr,
                        index,
                    })),
                    span,
                };
            } else if self.match_token(TokenType::Dot) {
                // Field access or method call: expr.field or expr.method()
                let field_span = self.current.span;
                let field_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected field name after '.'")?;
                let field = self.interner.intern(&field_token.lexeme);

                // Check for type args: expr.method<T, U>(...) or direct call: expr.method(...)
                let type_args = if self.check(TokenType::Lt) {
                    // Try to parse type args with lookahead
                    self.try_parse_call_type_args()?
                } else {
                    Vec::new()
                };

                if self.check(TokenType::LParen) {
                    // Method call: expr.method(args) or expr.method<T>(args)
                    self.advance(); // consume '('
                    let mut args = Vec::new();
                    if !self.check(TokenType::RParen) {
                        loop {
                            args.push(self.expression(0)?);
                            if !self.match_token(TokenType::Comma) {
                                break;
                            }
                            // Allow trailing comma
                            if self.check(TokenType::RParen) {
                                break;
                            }
                        }
                    }
                    let end_span = self.current.span;
                    self.consume(TokenType::RParen, "expected ')' after arguments")?;

                    let span = expr.span.merge(end_span);
                    expr = Expr {
                        id: self.next_id(),
                        kind: ExprKind::MethodCall(Box::new(MethodCallExpr {
                            object: expr,
                            method: field,
                            type_args,
                            args,
                            method_span: field_span,
                        })),
                        span,
                    };
                } else if !type_args.is_empty() {
                    // Had type args but no parens - syntax error
                    return Err(ParseError::new(
                        crate::errors::ParserError::ExpectedToken {
                            expected: "'(' after type arguments".to_string(),
                            found: self.current.ty.as_str().to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                } else {
                    // Field access: expr.field
                    let span = expr.span.merge(field_span);
                    expr = Expr {
                        id: self.next_id(),
                        kind: ExprKind::FieldAccess(Box::new(FieldAccessExpr {
                            object: expr,
                            field,
                            field_span,
                        })),
                        span,
                    };
                }
            } else if self.match_token(TokenType::QuestionDot) {
                // Optional chaining: expr?.field
                let field_span = self.current.span;
                let field_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected field name after '?.'")?;
                let field = self.interner.intern(&field_token.lexeme);

                let span = expr.span.merge(field_span);
                expr = Expr {
                    id: self.next_id(),
                    kind: ExprKind::OptionalChain(Box::new(OptionalChainExpr {
                        object: expr,
                        field,
                        field_span,
                    })),
                    span,
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    /// Finish parsing a function call (after the opening paren)
    pub(crate) fn finish_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        let mut args = Vec::new();

        if !self.check(TokenType::RParen) {
            loop {
                args.push(self.expression(0)?);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
                // Allow trailing comma
                if self.check(TokenType::RParen) {
                    break;
                }
            }
        }

        let end_span = self.current.span;
        self.consume(TokenType::RParen, "expected ')' after arguments")?;

        let span = callee.span.merge(end_span);
        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Call(Box::new(CallExpr { callee, args })),
            span,
        })
    }
}
