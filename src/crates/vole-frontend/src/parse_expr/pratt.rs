use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse an expression with Pratt parsing
    pub(crate) fn expression(&mut self, min_prec: u8) -> Result<Expr, ParseError> {
        let left = self.unary()?;
        self.expression_from(left, min_prec)
    }

    /// Pratt parsing loop: given an already-parsed `left` operand, parse
    /// binary operators, assignment, compound assignment, null-coalescing,
    /// type tests (`is`), and range operators at precedences above `min_prec`.
    pub(crate) fn expression_from(
        &mut self,
        mut left: Expr,
        min_prec: u8,
    ) -> Result<Expr, ParseError> {
        while self.current.ty.precedence() > min_prec {
            let op_ty = self.current.ty;
            let op = match op_ty {
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
                    // Assignment - special handling
                    self.advance();
                    let value = self.expression(0)?;
                    let span = left.span.merge(value.span);

                    let target = match left.kind {
                        ExprKind::Identifier(sym) => {
                            if self.interner.resolve(sym) == "_" {
                                AssignTarget::Discard
                            } else {
                                AssignTarget::Variable(sym)
                            }
                        }
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
                                    span: left.span.into(),
                                },
                                left.span,
                            ));
                        }
                    };

                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::Assign(Box::new(AssignExpr { target, value })),
                        span,
                    });
                }
                TokenType::PlusEq
                | TokenType::MinusEq
                | TokenType::StarEq
                | TokenType::SlashEq
                | TokenType::PercentEq => {
                    // Compound assignment: x += 1, arr[i] -= 2
                    let op = match self.current.ty {
                        TokenType::PlusEq => CompoundOp::Add,
                        TokenType::MinusEq => CompoundOp::Sub,
                        TokenType::StarEq => CompoundOp::Mul,
                        TokenType::SlashEq => CompoundOp::Div,
                        TokenType::PercentEq => CompoundOp::Mod,
                        _ => unreachable!(),
                    };
                    self.advance();

                    // Convert left expression to AssignTarget
                    let target = match left.kind {
                        ExprKind::Identifier(sym) => AssignTarget::Variable(sym),
                        ExprKind::Index(idx) => AssignTarget::Index {
                            object: Box::new(idx.object),
                            index: Box::new(idx.index),
                        },
                        ExprKind::FieldAccess(fa) => AssignTarget::Field {
                            object: Box::new(fa.object),
                            field: fa.field,
                            field_span: fa.field_span,
                        },
                        _ => {
                            return Err(ParseError::new(
                                ParserError::UnexpectedToken {
                                    token: "invalid compound assignment target".to_string(),
                                    span: left.span.into(),
                                },
                                left.span,
                            ));
                        }
                    };

                    let value = self.expression(0)?;
                    let span = left.span.merge(value.span);
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::CompoundAssign(Box::new(CompoundAssignExpr {
                            target,
                            op,
                            value,
                        })),
                        span,
                    });
                }
                TokenType::QuestionQuestion => {
                    // Null coalescing: x ?? default (right-associative)
                    self.advance();
                    let default = self.expression(1)?; // precedence 1 for right-associativity
                    let span = left.span.merge(default.span);
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::NullCoalesce(Box::new(NullCoalesceExpr {
                            value: left,
                            default,
                        })),
                        span,
                    });
                }
                TokenType::KwIs => {
                    // Type test: x is Type
                    self.advance();
                    let type_span_start = self.current.span;
                    let type_expr = self.parse_type()?;
                    let type_span = type_span_start.merge(self.previous.span);
                    let span = left.span.merge(type_span);
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::Is(Box::new(IsExpr {
                            value: left,
                            type_expr,
                            type_span,
                        })),
                        span,
                    });
                }
                _ => break,
            };

            let prec = op_ty.precedence();
            self.advance();
            let right = self.expression(prec)?;
            let span = left.span.merge(right.span);

            left = Expr {
                id: self.next_id(),
                kind: ExprKind::Binary(Box::new(BinaryExpr { left, op, right })),
                span,
            };
        }

        // Check for range operators (lowest precedence)
        if self.check(TokenType::DotDot) || self.check(TokenType::DotDotEqual) {
            let inclusive = self.check(TokenType::DotDotEqual);
            self.advance();
            let right = self.expression(0)?;
            let span = left.span.merge(right.span);
            return Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::Range(Box::new(RangeExpr {
                    start: left,
                    end: right,
                    inclusive,
                })),
                span,
            });
        }

        Ok(left)
    }

    /// Parse a unary expression (-, !, ~)
    pub(super) fn unary(&mut self) -> Result<Expr, ParseError> {
        if self.match_token(TokenType::Minus) {
            let op_span = self.previous.span;
            let operand = self.unary()?;
            let span = op_span.merge(operand.span);
            return Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::Unary(Box::new(UnaryExpr {
                    op: UnaryOp::Neg,
                    operand,
                })),
                span,
            });
        }

        if self.match_token(TokenType::Bang) {
            let op_span = self.previous.span;
            let operand = self.unary()?;
            let span = op_span.merge(operand.span);
            return Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::Unary(Box::new(UnaryExpr {
                    op: UnaryOp::Not,
                    operand,
                })),
                span,
            });
        }

        if self.match_token(TokenType::Tilde) {
            let op_span = self.previous.span;
            let operand = self.unary()?;
            let span = op_span.merge(operand.span);
            return Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::Unary(Box::new(UnaryExpr {
                    op: UnaryOp::BitNot,
                    operand,
                })),
                span,
            });
        }

        self.call()
    }
}
