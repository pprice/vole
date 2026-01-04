// src/frontend/parse_lambda.rs
//
// Lambda parsing functionality for the Vole parser.
// This module contains methods for parsing lambda expressions and related disambiguation.

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::{Span, Token, TokenType};
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Convert an expression to an assignment target
    #[allow(dead_code)] // Will be used in subsequent refactor tasks
    pub(super) fn expr_to_assign_target(&self, expr: Expr) -> Result<AssignTarget, ParseError> {
        match expr.kind {
            ExprKind::Identifier(sym) => Ok(AssignTarget::Variable(sym)),
            ExprKind::FieldAccess(fa) => Ok(AssignTarget::Field {
                object: Box::new(fa.object),
                field: fa.field,
                field_span: fa.field_span,
            }),
            ExprKind::Index(idx) => Ok(AssignTarget::Index {
                object: Box::new(idx.object),
                index: Box::new(idx.index),
            }),
            _ => Err(ParseError::new(
                ParserError::UnexpectedToken {
                    token: "invalid assignment target".to_string(),
                    span: expr.span.into(),
                },
                expr.span,
            )),
        }
    }

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

                params.push(LambdaParam {
                    name,
                    ty,
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
            LambdaBody::Block(self.block()?)
        } else {
            LambdaBody::Expr(Box::new(self.expression(0)?))
        };

        let end_span = match &body {
            LambdaBody::Block(b) => b.span,
            LambdaBody::Expr(e) => e.span,
        };

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(LambdaExpr {
                params,
                return_type,
                body,
                span: start_span.merge(end_span),
                captures: std::cell::RefCell::new(Vec::new()),
                has_side_effects: std::cell::Cell::new(false),
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

        params.push(LambdaParam {
            name: first_name,
            ty: first_ty,
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

            params.push(LambdaParam {
                name,
                ty,
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
            LambdaBody::Block(self.block()?)
        } else {
            LambdaBody::Expr(Box::new(self.expression(0)?))
        };

        let end_span = match &body {
            LambdaBody::Block(b) => b.span,
            LambdaBody::Expr(e) => e.span,
        };

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(LambdaExpr {
                params,
                return_type,
                body,
                span: start_span.merge(end_span),
                captures: std::cell::RefCell::new(Vec::new()),
                has_side_effects: std::cell::Cell::new(false),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Continue parsing an expression after we've already parsed the prefix/left side
    /// This is used when we've parsed an identifier and need to continue with binary ops, calls, etc.
    pub(super) fn continue_expression(
        &mut self,
        left: Expr,
        min_prec: u8,
    ) -> Result<Expr, ParseError> {
        // First handle call/index (postfix)
        let mut expr = self.continue_call(left)?;

        // Then handle binary operators
        while self.current.ty.precedence() > min_prec {
            let op_token = self.current.clone();
            let op = match op_token.ty {
                TokenType::Plus => BinaryOp::Add,
                TokenType::Minus => BinaryOp::Sub,
                TokenType::Star => BinaryOp::Mul,
                TokenType::Slash => BinaryOp::Div,
                TokenType::Percent => BinaryOp::Mod,
                TokenType::EqEq => BinaryOp::Eq,
                TokenType::BangEq => BinaryOp::Ne,
                TokenType::Lt => BinaryOp::Lt,
                TokenType::Gt => BinaryOp::Gt,
                TokenType::LtEq => BinaryOp::Le,
                TokenType::GtEq => BinaryOp::Ge,
                TokenType::AmpAmp => BinaryOp::And,
                TokenType::PipePipe => BinaryOp::Or,
                TokenType::Ampersand => BinaryOp::BitAnd,
                TokenType::Pipe => BinaryOp::BitOr,
                TokenType::Caret => BinaryOp::BitXor,
                TokenType::LessLess => BinaryOp::Shl,
                TokenType::GreaterGreater => BinaryOp::Shr,
                TokenType::Eq => {
                    // Assignment
                    self.advance();
                    let value = self.expression(0)?;
                    let span = expr.span.merge(value.span);

                    let target = match expr.kind {
                        ExprKind::Identifier(sym) => AssignTarget::Variable(sym),
                        ExprKind::FieldAccess(fa) => AssignTarget::Field {
                            object: Box::new(fa.object),
                            field: fa.field,
                            field_span: fa.field_span,
                        },
                        ExprKind::Index(idx) => AssignTarget::Index {
                            object: Box::new(idx.object),
                            index: Box::new(idx.index),
                        },
                        _ => {
                            return Err(ParseError::new(
                                ParserError::UnexpectedToken {
                                    token: "invalid assignment target".to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            ));
                        }
                    };

                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::Assign(Box::new(AssignExpr { target, value })),
                        span,
                    });
                }
                TokenType::QuestionQuestion => {
                    // Null coalescing
                    self.advance();
                    let default = self.expression(1)?;
                    let span = expr.span.merge(default.span);
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::NullCoalesce(Box::new(NullCoalesceExpr {
                            value: expr,
                            default,
                        })),
                        span,
                    });
                }
                TokenType::KwIs => {
                    // Type test
                    self.advance();
                    let type_span_start = self.current.span;
                    let type_expr = self.parse_type()?;
                    let type_span = type_span_start.merge(self.previous.span);
                    let span = expr.span.merge(type_span);
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::Is(Box::new(IsExpr {
                            value: expr,
                            type_expr,
                            type_span,
                        })),
                        span,
                    });
                }
                _ => break,
            };

            let prec = op_token.ty.precedence();
            self.advance();
            let right = self.expression(prec)?;
            let span = expr.span.merge(right.span);

            expr = Expr {
                id: self.next_id(),
                kind: ExprKind::Binary(Box::new(BinaryExpr {
                    left: expr,
                    op,
                    right,
                })),
                span,
            };
        }

        // Check for range operators
        if self.check(TokenType::DotDot) || self.check(TokenType::DotDotEqual) {
            let inclusive = self.check(TokenType::DotDotEqual);
            self.advance();
            let right = self.expression(0)?;
            let span = expr.span.merge(right.span);
            return Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::Range(Box::new(RangeExpr {
                    start: expr,
                    end: right,
                    inclusive,
                })),
                span,
            });
        }

        Ok(expr)
    }

    /// Continue parsing calls, indexes, field access, and method calls after we have the base expression
    fn continue_call(&mut self, mut expr: Expr) -> Result<Expr, ParseError> {
        loop {
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
                    let mut args = Vec::new();
                    if !self.check(TokenType::RParen) {
                        loop {
                            args.push(self.expression(0)?);
                            if !self.match_token(TokenType::Comma) {
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
