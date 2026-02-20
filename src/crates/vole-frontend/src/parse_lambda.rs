// src/frontend/parse_lambda.rs
//
// Lambda parsing functionality for the Vole parser.
// This module contains methods for parsing lambda expressions and related disambiguation.

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::{Span, Token, TokenType};

impl<'src> Parser<'src> {
    /// Parse a lambda expression: (params) => body
    /// We've already consumed '(' at this point
    pub(super) fn lambda_expr(&mut self, start_span: Span) -> Result<Expr, ParseError> {
        // We've already consumed '(' - parse parameters
        let mut params = Vec::new();

        if !self.check(TokenType::RParen) {
            loop {
                let param_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected parameter name")?;
                let name = self.interner.intern(&param_token.lexeme);

                let ty = if self.match_token(TokenType::Colon) {
                    Some(self.parse_type()?)
                } else {
                    None
                };

                let default_value = if self.match_token(TokenType::Eq) {
                    Some(Box::new(self.expression(0)?))
                } else {
                    None
                };

                params.push(LambdaParam {
                    name,
                    ty,
                    default_value,
                    span: param_token.span,
                });

                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RParen, "expected ')' after lambda parameters")?;

        // Optional return type
        let return_type = if self.match_token(TokenType::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        self.consume(TokenType::FatArrow, "expected '=>' after lambda parameters")?;

        // Parse body - block or expression
        let body = if self.check(TokenType::LBrace) {
            FuncBody::Block(self.block()?)
        } else {
            FuncBody::Expr(Box::new(self.expression(0)?))
        };

        let end_span = match &body {
            FuncBody::Block(b) => b.span,
            FuncBody::Expr(e) => e.span,
        };

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(LambdaExpr {
                type_params: Vec::new(),
                params,
                return_type,
                body,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse a lambda expression when we've already consumed the first identifier
    /// has_colon: true if current token is Colon (first param has type)
    ///            false if current token is Comma (multiple untyped params)
    pub(super) fn lambda_expr_after_first_ident(
        &mut self,
        start_span: Span,
        first_ident: Token,
        has_colon: bool,
    ) -> Result<Expr, ParseError> {
        let mut params = Vec::new();

        // Parse the first parameter's type if present
        let first_name = self.interner.intern(&first_ident.lexeme);
        let first_ty = if has_colon {
            self.consume(TokenType::Colon, "expected ':'")
                .expect("colon should be present");
            Some(self.parse_type()?)
        } else {
            None
        };

        let first_default = if self.match_token(TokenType::Eq) {
            Some(Box::new(self.expression(0)?))
        } else {
            None
        };

        params.push(LambdaParam {
            name: first_name,
            ty: first_ty,
            default_value: first_default,
            span: first_ident.span,
        });

        // Parse remaining parameters if comma-separated
        while self.match_token(TokenType::Comma) {
            let param_token = self.current.clone();
            self.consume(TokenType::Identifier, "expected parameter name")?;
            let name = self.interner.intern(&param_token.lexeme);

            let ty = if self.match_token(TokenType::Colon) {
                Some(self.parse_type()?)
            } else {
                None
            };

            let default_value = if self.match_token(TokenType::Eq) {
                Some(Box::new(self.expression(0)?))
            } else {
                None
            };

            params.push(LambdaParam {
                name,
                ty,
                default_value,
                span: param_token.span,
            });
        }

        self.consume(TokenType::RParen, "expected ')' after lambda parameters")?;

        // Optional return type
        let return_type = if self.match_token(TokenType::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        self.consume(TokenType::FatArrow, "expected '=>' after lambda parameters")?;

        // Parse body - block or expression
        let body = if self.check(TokenType::LBrace) {
            FuncBody::Block(self.block()?)
        } else {
            FuncBody::Expr(Box::new(self.expression(0)?))
        };

        let end_span = match &body {
            FuncBody::Block(b) => b.span,
            FuncBody::Expr(e) => e.span,
        };

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(LambdaExpr {
                type_params: Vec::new(),
                params,
                return_type,
                body,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Continue parsing an expression after we've already parsed the prefix/left side.
    /// This is used when we've parsed an identifier and need to continue with
    /// postfix ops (calls, indexing, field access) then binary operators.
    pub(super) fn continue_expression(
        &mut self,
        left: Expr,
        min_prec: u8,
    ) -> Result<Expr, ParseError> {
        // First handle call/index/field-access (postfix), then delegate to
        // the shared Pratt binary-operator loop in expression_from().
        let expr = self.continue_call(left)?;
        self.expression_from(expr, min_prec)
    }

    /// Continue parsing calls, indexes, field access, and method calls after
    /// we have the base expression.  This is the simplified postfix loop used
    /// when we already consumed the leading identifier inside a parenthesised
    /// expression and cannot re-enter `call()` (which starts from `primary()`).
    fn continue_call(&mut self, mut expr: Expr) -> Result<Expr, ParseError> {
        loop {
            // Allow method chains to span multiple lines
            if self.check(TokenType::Newline) {
                self.skip_newlines();
                if !self.check(TokenType::Dot) && !self.check(TokenType::QuestionDot) {
                    break;
                }
            }

            if self.match_token(TokenType::LParen) {
                expr = self.finish_call(expr)?;
            } else if self.match_token(TokenType::LBracket) {
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

                if self.check(TokenType::LParen) {
                    // Method call: expr.method(args)
                    self.advance(); // consume '('
                    self.skip_newlines();
                    let args = self.parse_call_args()?;
                    let end_span = self.current.span;
                    self.consume(TokenType::RParen, "expected ')' after arguments")?;

                    let span = expr.span.merge(end_span);
                    expr = Expr {
                        id: self.next_id(),
                        kind: ExprKind::MethodCall(Box::new(MethodCallExpr {
                            object: expr,
                            method: field,
                            type_args: Vec::new(),
                            args,
                            method_span: field_span,
                        })),
                        span,
                    };
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
            } else {
                break;
            }
        }
        Ok(expr)
    }
}
