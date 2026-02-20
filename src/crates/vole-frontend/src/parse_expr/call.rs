use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse a single call argument.
    ///
    /// If the current token is an `Identifier` immediately followed by `:`,
    /// parse it as `CallArg::Named { name, value }`.  Otherwise parse the
    /// expression as `CallArg::Positional`.
    pub(crate) fn parse_call_arg(&mut self) -> Result<CallArg, ParseError> {
        // Look ahead: if current is Identifier and next is Colon, it's a named arg.
        if self.check(TokenType::Identifier) && self.peek_token().ty == TokenType::Colon {
            let name_span = self.current.span;
            let name = self.interner.intern(&self.current.lexeme);
            self.advance(); // consume identifier
            self.advance(); // consume ':'
            let value = self.expression(0)?;
            let span = name_span.merge(value.span);
            Ok(CallArg::Named { name, value, span })
        } else {
            Ok(CallArg::Positional(self.expression(0)?))
        }
    }

    /// Scan ahead (without consuming) to check whether `=>` appears at nesting
    /// depth 0 inside the current call arg list, AND every comma-separated piece
    /// before `=>` looks like an unparenthesized lambda parameter (`ident` or
    /// `ident : TypeExpr`).
    ///
    /// This discriminates `f(x => body)` (unparenthesized lambda) from
    /// `f((x) => body)` or `f(c, (x) => body)` (regular call args that the
    /// normal `parse_call_arg` / `expression(0)` path already handles).
    ///
    /// Each "piece" between commas (at depth 0) must begin with an `Identifier`.
    /// If any piece starts with something else (e.g. `(`, a literal), returns false.
    ///
    /// Caller must already have consumed `(` and skipped leading newlines.
    fn has_top_level_fat_arrow(&self) -> bool {
        // The current token starts the first piece; it must be an identifier.
        if self.current.ty != TokenType::Identifier {
            return false;
        }

        let mut scan_lexer = self.lexer.clone();
        let mut token = self.current.clone();
        let mut depth: u32 = 0;

        loop {
            match token.ty {
                TokenType::LParen | TokenType::LBracket | TokenType::LBrace => depth += 1,
                TokenType::RBracket | TokenType::RBrace => {
                    depth = depth.saturating_sub(1);
                }
                TokenType::RParen => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                // A comma at depth 0 separates param pieces.
                // The next non-newline token must be an Identifier or `=>`
                // (trailing comma before `=>` is unusual but harmless to reject).
                TokenType::Comma if depth == 0 => {
                    // Peek at the next real token
                    let mut next = scan_lexer.next_token();
                    while next.ty == TokenType::Newline {
                        next = scan_lexer.next_token();
                    }
                    // Next piece must start with an identifier (or be `=>` for
                    // an unexpected but benign trailing comma, which we accept
                    // by letting the main loop see `=>` on the next iteration).
                    if next.ty != TokenType::Identifier && next.ty != TokenType::FatArrow {
                        return false;
                    }
                    token = next;
                    continue;
                }
                TokenType::FatArrow if depth == 0 => return true,
                TokenType::Eof => return false,
                _ => {}
            }
            token = scan_lexer.next_token();
        }
    }

    /// Parse the entire call arg list as a single unparenthesized lambda.
    ///
    /// Called when `has_top_level_fat_arrow` returned true.  We collect all
    /// comma-separated pieces before `=>` as `LambdaParam`s, then parse the
    /// body after `=>`, and return a single `CallArg::Positional(Lambda{...})`.
    ///
    /// If any piece is not a valid lambda param (`ident` or `ident : TypeExpr`),
    /// an error is returned.
    fn parse_unparenthesized_lambda(&mut self) -> Result<CallArg, ParseError> {
        let start_span = self.current.span;
        let mut params: Vec<LambdaParam> = Vec::new();

        // Collect params until we hit `=>`
        loop {
            if self.check(TokenType::FatArrow) {
                break;
            }
            // Expect an identifier (param name)
            if !self.check(TokenType::Identifier) {
                return Err(ParseError::new(
                    ParserError::UnexpectedToken {
                        token: format!(
                            "use parentheses around lambda params when mixing with other arguments \
                             (found '{}')",
                            self.current.ty.as_str()
                        ),
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ));
            }
            let param_span = self.current.span;
            let param_name_str = self.current.lexeme.to_string();
            self.advance(); // consume identifier

            let ty = if self.match_token(TokenType::Colon) {
                Some(self.parse_type()?)
            } else {
                None
            };

            let name = self.interner.intern(&param_name_str);
            params.push(LambdaParam {
                name,
                ty,
                default_value: None,
                span: param_span,
            });

            // After a param, expect `,` (more params) or `=>` (done)
            if self.check(TokenType::FatArrow) {
                break;
            }
            if !self.match_token(TokenType::Comma) {
                return Err(ParseError::new(
                    ParserError::ExpectedToken {
                        expected: "',', or '=>' in unparenthesized lambda params".to_string(),
                        found: self.current.ty.as_str().to_string(),
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ));
            }
        }

        // Consume `=>`
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

        let lambda_span = start_span.merge(end_span);
        let lambda = Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(LambdaExpr {
                type_params: Vec::new(),
                params,
                return_type: None,
                body,
                span: lambda_span,
            })),
            span: lambda_span,
        };

        Ok(CallArg::Positional(lambda))
    }
}

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
                expr = self.parse_dot_postfix(expr)?;
            } else if self.match_token(TokenType::QuestionDot) {
                // Optional chaining: expr?.field
                let field_span = self.current.span;
                self.consume(TokenType::Identifier, "expected field name after '?.'")?;
                let field = self.interner.intern(&self.previous.lexeme);

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

    /// Parse a dot-postfix expression: field access, method call, or module-qualified struct literal.
    /// Called after the '.' token has been consumed.
    fn parse_dot_postfix(&mut self, expr: Expr) -> Result<Expr, ParseError> {
        let field_span = self.current.span;
        self.consume(TokenType::Identifier, "expected field name after '.'")?;
        let field = self.interner.intern(&self.previous.lexeme);

        // Check for type args: expr.method<T, U>(...) or direct call: expr.method(...)
        // or module.Type<T> { ... } for qualified generic struct literals
        let type_args = if self.check(TokenType::Lt) {
            // Try to parse type args with lookahead
            self.try_parse_call_type_args()?
        } else {
            Vec::new()
        };

        if self.check(TokenType::LParen) {
            // Method call: expr.method(args) or expr.method<T>(args)
            self.advance(); // consume '('
            self.skip_newlines();
            let args = self.parse_call_args()?;
            let end_span = self.current.span;
            self.consume(TokenType::RParen, "expected ')' after arguments")?;

            let span = expr.span.merge(end_span);
            Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::MethodCall(Box::new(MethodCallExpr {
                    object: expr,
                    method: field,
                    type_args,
                    args,
                    method_span: field_span,
                })),
                span,
            })
        } else if self.check(TokenType::LBrace) && self.looks_like_struct_literal() {
            // Check for module-qualified struct literal: mod.Type { field: value }
            // Try to extract a path of identifiers from the left-hand expression
            if let Some(mut path) = Self::expr_to_identifier_path(&expr) {
                path.push(field);
                let start_span = expr.span;
                // Parse the struct literal and continue the loop to handle
                // chained operations like `mod.Type { f: 1 }.field`
                self.struct_literal(path, type_args, start_span)
            } else if !type_args.is_empty() {
                // Had type args but LHS wasn't an identifier path - syntax error
                Err(ParseError::new(
                    ParserError::ExpectedToken {
                        expected: "'(' after type arguments".to_string(),
                        found: self.current.ty.as_str().to_string(),
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ))
            } else {
                // Not an identifier path - fall through to field access
                let span = expr.span.merge(field_span);
                Ok(Expr {
                    id: self.next_id(),
                    kind: ExprKind::FieldAccess(Box::new(FieldAccessExpr {
                        object: expr,
                        field,
                        field_span,
                    })),
                    span,
                })
            }
        } else if !type_args.is_empty() {
            // Had type args but no parens or struct literal - syntax error
            Err(ParseError::new(
                ParserError::ExpectedToken {
                    expected: "'(' or '{' after type arguments".to_string(),
                    found: self.current.ty.as_str().to_string(),
                    span: self.current.span.into(),
                },
                self.current.span,
            ))
        } else {
            // Field access: expr.field
            let span = expr.span.merge(field_span);
            Ok(Expr {
                id: self.next_id(),
                kind: ExprKind::FieldAccess(Box::new(FieldAccessExpr {
                    object: expr,
                    field,
                    field_span,
                })),
                span,
            })
        }
    }

    /// Finish parsing a function call (after the opening paren)
    pub(crate) fn finish_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        self.skip_newlines();
        let args = self.parse_call_args()?;
        let end_span = self.current.span;
        self.consume(TokenType::RParen, "expected ')' after arguments")?;

        let span = callee.span.merge(end_span);
        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Call(Box::new(CallExpr { callee, args })),
            span,
        })
    }

    /// Parse the argument list inside a call or method-call expression.
    ///
    /// Caller must have consumed `(` and skipped leading newlines before calling.
    /// Stops just before `)`.
    ///
    /// If `=>` appears at nesting depth 0 in the arg list, the entire arg list
    /// before `=>` is treated as unparenthesized lambda params and the result
    /// is a single `CallArg::Positional(Lambda)`.
    pub(crate) fn parse_call_args(&mut self) -> Result<Vec<CallArg>, ParseError> {
        if self.check(TokenType::RParen) {
            return Ok(Vec::new());
        }

        // Scan ahead: if `=>` appears at top level, treat the whole arg list
        // as an unparenthesized lambda.
        if self.has_top_level_fat_arrow() {
            let lambda_arg = self.parse_unparenthesized_lambda()?;
            self.skip_newlines();
            return Ok(vec![lambda_arg]);
        }

        let mut args = Vec::new();
        loop {
            args.push(self.parse_call_arg()?);
            self.skip_newlines();
            if !self.match_token(TokenType::Comma) {
                break;
            }
            self.skip_newlines();
            // Allow trailing comma
            if self.check(TokenType::RParen) {
                break;
            }
        }
        Ok(args)
    }

    /// Try to extract a path of identifiers from an expression.
    /// For example, `mod.sub` -> Some([mod, sub]), `x` -> Some([x]), `foo()` -> None
    /// This is used to check if a field access base could be a module path for qualified struct literals.
    fn expr_to_identifier_path(expr: &Expr) -> Option<Vec<Symbol>> {
        match &expr.kind {
            ExprKind::Identifier(sym) => Some(vec![*sym]),
            ExprKind::FieldAccess(fa) => {
                let mut path = Self::expr_to_identifier_path(&fa.object)?;
                path.push(fa.field);
                Some(path)
            }
            _ => None,
        }
    }
}
