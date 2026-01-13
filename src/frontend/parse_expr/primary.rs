use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;
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

    /// Parse a primary expression (literals, identifiers, grouping, interpolated strings)
    pub(super) fn primary(&mut self) -> Result<Expr, ParseError> {
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
            TokenType::KwDone => {
                let start_span = token.span;
                self.advance(); // consume 'Done'
                self.consume(TokenType::LBrace, "expected '{' after Done")?;
                let end_span = self.current.span;
                self.consume(TokenType::RBrace, "expected '}' after Done")?;
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Done,
                    span: start_span.merge(end_span),
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
            TokenType::RawStringLiteral => {
                self.advance();
                // Remove @" prefix and " suffix, no escape processing
                let lexeme = &token.lexeme;
                let content = lexeme[2..lexeme.len() - 1].to_string();
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

                // Check for type args: Name<T, U> followed by { for struct literal
                let type_args = if self.check(TokenType::Lt) {
                    self.try_parse_struct_type_args()?
                } else {
                    Vec::new()
                };

                // Check for struct literal: Name { field: value } or Name<T> { field: value }
                // We need lookahead to distinguish from a block: `size { let x = ... }`
                // A struct literal looks like `Name { identifier: value }` or `Name { }`
                // A block starts with statements, keywords, or expressions without `:` after ident
                if self.check(TokenType::LBrace) && self.looks_like_struct_literal() {
                    return self.struct_literal(sym, type_args, token.span);
                }

                // If we parsed type args but no struct literal follows, that's an error
                if !type_args.is_empty() {
                    return Err(ParseError::new(
                        ParserError::ExpectedToken {
                            expected: "'{' after type arguments for struct literal".to_string(),
                            found: self.current.ty.as_str().to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
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
                                        type_params: Vec::new(),
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

                // Empty array: []
                if self.check(TokenType::RBracket) {
                    let end_span = self.current.span;
                    self.advance(); // consume ']'
                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::ArrayLiteral(Vec::new()),
                        span: start_span.merge(end_span),
                    });
                }

                // Parse first element
                let first = self.expression(0)?;

                // Check what follows the first element
                if self.check(TokenType::Semicolon) {
                    // [expr; N] - repeat literal
                    self.advance(); // consume ';'
                    let count = self.parse_repeat_count()?;
                    let end_span = self.current.span;
                    self.consume(TokenType::RBracket, "expected ']' after repeat count")?;

                    return Ok(Expr {
                        id: self.next_id(),
                        kind: ExprKind::RepeatLiteral {
                            element: Box::new(first),
                            count,
                        },
                        span: start_span.merge(end_span),
                    });
                }

                // [expr, ...] - array/tuple literal
                let mut elements = vec![first];

                while self.match_token(TokenType::Comma) {
                    if self.check(TokenType::RBracket) {
                        break; // trailing comma allowed
                    }
                    elements.push(self.expression(0)?);
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
            TokenType::KwIf => self.if_expr(),
            TokenType::KwTry => self.try_expr(),
            TokenType::KwYield => self.yield_expr(),
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

    /// Parse the count in a repeat literal [expr; N]
    fn parse_repeat_count(&mut self) -> Result<usize, ParseError> {
        let token = self.current.clone();
        if token.ty != TokenType::IntLiteral {
            return Err(ParseError::new(
                ParserError::ExpectedExpression {
                    found: token.ty.as_str().to_string(),
                    span: token.span.into(),
                },
                token.span,
            ));
        }
        self.advance();
        token.lexeme.parse::<usize>().map_err(|_| {
            ParseError::new(
                ParserError::UnexpectedToken {
                    token: "invalid repeat count (must be non-negative integer)".to_string(),
                    span: token.span.into(),
                },
                token.span,
            )
        })
    }

    /// Parse a struct literal: Name { field: value, ... } or Name<T> { field: value, ... }
    fn struct_literal(
        &mut self,
        name: Symbol,
        type_args: Vec<TypeExpr>,
        start_span: Span,
    ) -> Result<Expr, ParseError> {
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
            kind: ExprKind::StructLiteral(Box::new(StructLiteralExpr {
                name,
                type_args,
                fields,
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse an if expression: if cond { then } [else { else }]
    pub(super) fn if_expr(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'if'

        // Parse condition
        let condition = self.expression(0)?;

        // Parse then branch as block expression
        self.consume(TokenType::LBrace, "expected '{' after if condition")?;
        let then_branch = self.block_expr(start_span)?;

        // Parse optional else branch
        self.skip_newlines();
        let else_branch = if self.match_token(TokenType::KwElse) {
            if self.check(TokenType::KwIf) {
                // else if - parse as another if expression
                Some(self.if_expr()?)
            } else {
                // else { block }
                self.consume(TokenType::LBrace, "expected '{' after else")?;
                Some(self.block_expr(start_span)?)
            }
        } else {
            None
        };

        let end_span = else_branch
            .as_ref()
            .map(|e| e.span)
            .unwrap_or(then_branch.span);

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::If(Box::new(IfExpr {
                condition,
                then_branch,
                else_branch,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse a block expression: { stmts; trailing_expr }
    /// Called after consuming the opening '{'
    fn block_expr(&mut self, start_span: Span) -> Result<Expr, ParseError> {
        self.skip_newlines();

        let mut stmts = Vec::new();
        let mut trailing_expr = None;

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            self.skip_newlines();
            if self.check(TokenType::RBrace) {
                break;
            }

            // Check for statement keywords (must be parsed as statements)
            if self.check(TokenType::KwLet)
                || self.check(TokenType::KwWhile)
                || self.check(TokenType::KwFor)
                || self.check(TokenType::KwBreak)
                || self.check(TokenType::KwContinue)
                || self.check(TokenType::KwReturn)
                || self.check(TokenType::KwRaise)
            {
                stmts.push(self.statement()?);
                self.skip_newlines();
                continue;
            }

            // Try to parse as expression
            let expr = self.expression(0)?;

            // Check what follows
            self.skip_newlines();
            if self.check(TokenType::RBrace) {
                // This is the trailing expression
                trailing_expr = Some(expr);
                break;
            } else {
                // This is an expression statement
                let span = expr.span;
                stmts.push(Stmt::Expr(ExprStmt { expr, span }));
            }
        }

        let end_span = self.current.span;
        self.consume(TokenType::RBrace, "expected '}' after block")?;

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Block(Box::new(BlockExpr {
                stmts,
                trailing_expr,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }
}
