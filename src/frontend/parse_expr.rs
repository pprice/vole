// src/frontend/parse_expr.rs
//
// Expression parsing functionality for the Vole parser.
// This module contains methods for parsing expressions using Pratt parsing,
// including binary operators, unary operators, calls, field access, and primary expressions.

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::TokenType;
use crate::errors::ParserError;
use crate::frontend::{Lexer, Span};

impl<'src> Parser<'src> {
    /// Check if the current position looks like a struct literal.
    /// This uses lookahead to distinguish `Name { field: value }` from `Name { statement }`.
    /// Returns true if:
    /// - Content after `{` is `}` (empty struct literal: `Name { }`)
    /// - Content after `{` is `Identifier :` (field initialization)
    ///
    /// We create a temporary lexer to peek without consuming tokens.
    pub(super) fn looks_like_struct_literal(&self) -> bool {
        // We're at `{` which is in self.current
        // Create a temporary lexer starting from position after `{`
        let brace_end = self.current.span.end;
        let remaining_source = &self.lexer.source()[brace_end..];

        let mut peek_lexer = Lexer::new(remaining_source);

        // Get first token after `{`
        let mut first = peek_lexer.next_token();

        // Skip newlines
        while first.ty == TokenType::Newline {
            first = peek_lexer.next_token();
        }

        if first.ty == TokenType::RBrace {
            // Empty struct: `Name { }`
            return true;
        }

        if first.ty == TokenType::Identifier {
            // Check what follows the identifier
            let second = peek_lexer.next_token();
            if second.ty == TokenType::Colon {
                // It's `Name { identifier: ...` - struct literal
                return true;
            }
        }

        // Anything else: keyword, literal, operator, etc. - it's a block
        false
    }

    /// Parse an expression with Pratt parsing
    pub(super) fn expression(&mut self, min_prec: u8) -> Result<Expr, ParseError> {
        let mut left = self.unary()?;

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
                    // Assignment - special handling
                    self.advance();
                    let value = self.expression(0)?;
                    let span = left.span.merge(value.span);

                    let target = match left.kind {
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

            let prec = op_token.ty.precedence();
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
    fn unary(&mut self) -> Result<Expr, ParseError> {
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

    /// Parse a call expression (function call), index expressions, field access, and method calls
    fn call(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.primary()?;

        loop {
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
    pub(super) fn finish_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
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

        let span = callee.span.merge(end_span);
        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Call(Box::new(CallExpr { callee, args })),
            span,
        })
    }

    /// Parse a primary expression (literals, identifiers, grouping, interpolated strings)
    fn primary(&mut self) -> Result<Expr, ParseError> {
        let token = self.current.clone();

        match token.ty {
            TokenType::IntLiteral => {
                self.advance();
                let value: i64 = token.lexeme.parse().map_err(|_| {
                    ParseError::new(
                        ParserError::UnexpectedToken {
                            token: "invalid integer literal".to_string(),
                            span: token.span.into(),
                        },
                        token.span,
                    )
                })?;
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::IntLiteral(value),
                    span: token.span,
                })
            }
            TokenType::FloatLiteral => {
                self.advance();
                let value: f64 = token.lexeme.parse().map_err(|_| {
                    ParseError::new(
                        ParserError::UnexpectedToken {
                            token: "invalid float literal".to_string(),
                            span: token.span.into(),
                        },
                        token.span,
                    )
                })?;
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::FloatLiteral(value),
                    span: token.span,
                })
            }
            TokenType::KwTrue => {
                self.advance();
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::BoolLiteral(true),
                    span: token.span,
                })
            }
            TokenType::KwFalse => {
                self.advance();
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::BoolLiteral(false),
                    span: token.span,
                })
            }
            TokenType::KwNil => {
                self.advance();
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Nil,
                    span: token.span,
                })
            }
            TokenType::KwImport => {
                let start_span = token.span;
                self.advance(); // consume 'import'

                // Expect a string literal for the module path
                if !self.check(TokenType::StringLiteral) {
                    return Err(ParseError::new(
                        ParserError::ExpectedToken {
                            expected: "module path string".to_string(),
                            found: self.current.ty.as_str().to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }

                let path_token = self.current.clone();
                self.advance();

                // Remove surrounding quotes
                let path = self.process_string_content(&path_token.lexeme);
                let span = start_span.merge(path_token.span);

                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Import(path),
                    span,
                })
            }
            TokenType::StringLiteral => {
                self.advance();
                // Remove surrounding quotes and process escape sequences
                let content = self.process_string_content(&token.lexeme);
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::StringLiteral(content),
                    span: token.span,
                })
            }
            TokenType::StringInterpStart => self.parse_interpolated_string(),
            TokenType::Identifier => {
                self.advance();
                let sym = self.interner.intern(&token.lexeme);

                // Check for struct literal: Name { field: value }
                // We need lookahead to distinguish from a block: `size { let x = ... }`
                // A struct literal looks like `Name { identifier: value }` or `Name { }`
                // A block starts with statements, keywords, or expressions without `:` after ident
                if self.check(TokenType::LBrace) && self.looks_like_struct_literal() {
                    return self.struct_literal(sym, token.span);
                }

                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Identifier(sym),
                    span: token.span,
                })
            }
            TokenType::LParen => {
                let start_span = token.span;
                self.advance(); // consume '('

                // Case 1: () - empty parens, must be lambda
                if self.check(TokenType::RParen) {
                    // Zero-param lambda: () => body
                    return self.lambda_expr(start_span);
                }

                // Case 2: Check if first token after '(' is an identifier
                if self.check(TokenType::Identifier) {
                    // Save the identifier token and consume it
                    let ident_token = self.current.clone();
                    self.advance();

                    // Check what follows the identifier
                    match self.current.ty {
                        // (ident: ...) - type annotation means lambda
                        TokenType::Colon => {
                            // Definitely a lambda with typed parameter - parse all params
                            return self.lambda_expr_after_first_ident(
                                start_span,
                                ident_token,
                                true,
                            );
                        }
                        // (ident, ...) - comma means multi-param lambda
                        TokenType::Comma => {
                            // Definitely a lambda with multiple params
                            return self.lambda_expr_after_first_ident(
                                start_span,
                                ident_token,
                                false,
                            );
                        }
                        // (ident) - could be grouping or single-param lambda
                        TokenType::RParen => {
                            let ident_span = ident_token.span;
                            // Consume the ')'
                            self.advance();

                            // Now check for => or -> to determine if lambda
                            if self.check(TokenType::FatArrow) || self.check(TokenType::Arrow) {
                                // It's a lambda: (x) => body or (x) -> T => body
                                let name = self.interner.intern(&ident_token.lexeme);

                                // Optional return type
                                let return_type = if self.match_token(TokenType::Arrow) {
                                    Some(self.parse_type()?)
                                } else {
                                    None
                                };

                                self.consume(
                                    TokenType::FatArrow,
                                    "expected '=>' after lambda parameters",
                                )?;

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

                                return Ok(Expr {
                                    id: self.next_id(),
                                    kind: ExprKind::Lambda(Box::new(LambdaExpr {
                                        params: vec![LambdaParam {
                                            name,
                                            ty: None,
                                            span: ident_span,
                                        }],
                                        return_type,
                                        body,
                                        span: start_span.merge(end_span),
                                        captures: std::cell::RefCell::new(Vec::new()),
                                        has_side_effects: std::cell::Cell::new(false),
                                    })),
                                    span: start_span.merge(end_span),
                                });
                            } else {
                                // It's grouping: (identifier)
                                let name = self.interner.intern(&ident_token.lexeme);
                                let inner_expr = Expr {
                                    id: self.next_id(),
                                    kind: ExprKind::Identifier(name),
                                    span: ident_span,
                                };
                                let span = start_span.merge(ident_span);
                                return Ok(Expr {
                                    id: self.next_id(),
                                    kind: ExprKind::Grouping(Box::new(inner_expr)),
                                    span,
                                });
                            }
                        }
                        // Anything else after identifier means it's part of an expression
                        // We already consumed the identifier, need to handle this
                        _ => {
                            // Build the identifier expression and continue parsing
                            let name = self.interner.intern(&ident_token.lexeme);
                            let left = Expr {
                                id: self.next_id(),
                                kind: ExprKind::Identifier(name),
                                span: ident_token.span,
                            };
                            // Parse the rest of the expression with the identifier as left side
                            let expr = self.continue_expression(left, 0)?;
                            let end_span = self.current.span;
                            self.consume(TokenType::RParen, "expected ')' after expression")?;
                            let span = start_span.merge(end_span);
                            return Ok(Expr {
                                id: self.next_id(),
                                kind: ExprKind::Grouping(Box::new(expr)),
                                span,
                            });
                        }
                    }
                }

                // Case 3: Expression that doesn't start with identifier (e.g., (1 + 2))
                let expr = self.expression(0)?;
                let end_span = self.current.span;
                self.consume(TokenType::RParen, "expected ')' after expression")?;
                let span = start_span.merge(end_span);
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Grouping(Box::new(expr)),
                    span,
                })
            }
            TokenType::LBracket => {
                let start_span = self.current.span;
                self.advance(); // consume '['

                let mut elements = Vec::new();

                if !self.check(TokenType::RBracket) {
                    elements.push(self.expression(0)?);

                    while self.match_token(TokenType::Comma) {
                        if self.check(TokenType::RBracket) {
                            break; // trailing comma allowed
                        }
                        elements.push(self.expression(0)?);
                    }
                }

                let end_span = self.current.span;
                self.consume(TokenType::RBracket, "expected ']' after array elements")?;

                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::ArrayLiteral(elements),
                    span: start_span.merge(end_span),
                })
            }
            TokenType::KwMatch => self.match_expr(),
            TokenType::KwTry => self.try_expr(),
            // Type keywords in expression position: `let X = i32`
            TokenType::KwI8
            | TokenType::KwI16
            | TokenType::KwI32
            | TokenType::KwI64
            | TokenType::KwI128
            | TokenType::KwU8
            | TokenType::KwU16
            | TokenType::KwU32
            | TokenType::KwU64
            | TokenType::KwF32
            | TokenType::KwF64
            | TokenType::KwBool
            | TokenType::KwString => {
                let start_span = token.span;
                // Parse full type expression (handles unions and optionals)
                let type_expr = self.parse_type()?;
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::TypeLiteral(type_expr),
                    span: start_span.merge(self.previous.span),
                })
            }
            TokenType::Error => Err(ParseError::new(
                ParserError::UnexpectedToken {
                    token: token.lexeme.clone(),
                    span: token.span.into(),
                },
                token.span,
            )),
            _ => Err(ParseError::new(
                ParserError::ExpectedExpression {
                    found: token.ty.as_str().to_string(),
                    span: token.span.into(),
                },
                token.span,
            )),
        }
    }

    /// Parse a struct literal: Name { field: value, ... }
    fn struct_literal(&mut self, name: Symbol, start_span: Span) -> Result<Expr, ParseError> {
        self.consume(TokenType::LBrace, "expected '{'")?;
        self.skip_newlines();

        let mut fields = Vec::new();

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            let field_span = self.current.span;
            let field_name_token = self.current.clone();
            self.consume(TokenType::Identifier, "expected field name")?;
            let field_name = self.interner.intern(&field_name_token.lexeme);

            self.consume(TokenType::Colon, "expected ':' after field name")?;
            let value = self.expression(0)?;

            fields.push(StructFieldInit {
                name: field_name,
                value,
                span: field_span.merge(self.previous.span),
            });

            if self.check(TokenType::Comma) {
                self.advance();
                self.skip_newlines();
            } else {
                break;
            }
            self.skip_newlines();
        }

        let end_span = self.current.span;
        self.consume(TokenType::RBrace, "expected '}'")?;

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::StructLiteral(Box::new(StructLiteralExpr { name, fields })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse a match expression
    fn match_expr(&mut self) -> Result<Expr, ParseError> {
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
    fn pattern(&mut self) -> Result<Pattern, ParseError> {
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
    fn get_pattern_span(&self, pattern: &Pattern) -> Span {
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

    /// Parse a try expression (propagation operator)
    fn try_expr(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'try'

        // Parse the inner expression - try binds tightly (like unary)
        let inner = self.unary()?;
        let span = start_span.merge(inner.span);

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Try(Box::new(inner)),
            span,
        })
    }

    /// Convert a token to a TypeExpr if it's a primitive type or nil keyword
    fn token_to_type_expr(&self, token: &super::token::Token) -> Option<TypeExpr> {
        match token.ty {
            TokenType::KwI8 => Some(TypeExpr::Primitive(PrimitiveType::I8)),
            TokenType::KwI16 => Some(TypeExpr::Primitive(PrimitiveType::I16)),
            TokenType::KwI32 => Some(TypeExpr::Primitive(PrimitiveType::I32)),
            TokenType::KwI64 => Some(TypeExpr::Primitive(PrimitiveType::I64)),
            TokenType::KwI128 => Some(TypeExpr::Primitive(PrimitiveType::I128)),
            TokenType::KwU8 => Some(TypeExpr::Primitive(PrimitiveType::U8)),
            TokenType::KwU16 => Some(TypeExpr::Primitive(PrimitiveType::U16)),
            TokenType::KwU32 => Some(TypeExpr::Primitive(PrimitiveType::U32)),
            TokenType::KwU64 => Some(TypeExpr::Primitive(PrimitiveType::U64)),
            TokenType::KwF32 => Some(TypeExpr::Primitive(PrimitiveType::F32)),
            TokenType::KwF64 => Some(TypeExpr::Primitive(PrimitiveType::F64)),
            TokenType::KwBool => Some(TypeExpr::Primitive(PrimitiveType::Bool)),
            TokenType::KwString => Some(TypeExpr::Primitive(PrimitiveType::String)),
            TokenType::KwNil => Some(TypeExpr::Nil),
            _ => None,
        }
    }
}
