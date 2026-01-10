// src/frontend/parse_stmt.rs
//
// Statement parsing methods extracted from parser.rs.

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::{Span, TokenType};
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Parse a block: `{ statements }`
    pub(super) fn block(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;
        self.consume(TokenType::LBrace, "expected '{'")?;
        self.skip_newlines();

        let mut stmts = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            stmts.push(self.statement()?);
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}'")?;
        let span = start_span.merge(self.previous.span);

        Ok(Block { stmts, span })
    }

    /// Parse a statement
    fn statement(&mut self) -> Result<Stmt, ParseError> {
        match self.current.ty {
            TokenType::KwLet => self.let_stmt(),
            TokenType::KwWhile => self.while_stmt(),
            TokenType::KwFor => self.for_stmt(),
            TokenType::KwIf => self.if_stmt(),
            TokenType::KwBreak => {
                let span = self.current.span;
                self.advance();
                Ok(Stmt::Break(span))
            }
            TokenType::KwContinue => self.continue_stmt(),
            TokenType::KwReturn => self.return_stmt(),
            TokenType::KwRaise => self.raise_stmt(),
            _ => self.expr_stmt(),
        }
    }

    /// Parse a let statement (as a Stmt)
    fn let_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'let'

        let mutable = self.match_token(TokenType::KwMut);

        // Check for tuple destructuring: let [a, b] = expr
        if self.check(TokenType::LBracket) {
            let pattern = self.parse_tuple_pattern()?;

            self.consume(TokenType::Eq, "expected '=' in let statement")?;
            let init = self.expression(0)?;
            let span = start_span.merge(init.span);

            return Ok(Stmt::LetTuple(LetTupleStmt {
                pattern,
                mutable,
                init,
                span,
            }));
        }

        // Regular let statement
        let stmt = self.let_statement_inner(mutable, start_span)?;
        Ok(Stmt::Let(stmt))
    }

    /// Parse the rest of a let statement (after 'let' and optional 'mut')
    fn let_statement_inner(
        &mut self,
        mutable: bool,
        start_span: Span,
    ) -> Result<LetStmt, ParseError> {
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected variable name")?;
        let name = self.interner.intern(&name_token.lexeme);

        let ty = if self.match_token(TokenType::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };

        self.consume(TokenType::Eq, "expected '=' in let statement")?;
        let init = self.expression(0)?;
        let span = start_span.merge(init.span);

        Ok(LetStmt {
            name,
            ty,
            mutable,
            init,
            span,
        })
    }

    /// Parse a let statement (returns LetStmt directly)
    pub(super) fn let_statement(&mut self) -> Result<LetStmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'let'
        let mutable = self.match_token(TokenType::KwMut);
        self.let_statement_inner(mutable, start_span)
    }

    /// Parse a tuple destructuring pattern: [a, b, c]
    fn parse_tuple_pattern(&mut self) -> Result<Pattern, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume '['

        let mut elements = Vec::new();
        let mut end_span = start_span;

        loop {
            if self.check(TokenType::RBracket) {
                break;
            }

            // Parse element pattern (identifier or wildcard)
            let token = self.current.clone();
            let elem_pattern = if token.ty == TokenType::Identifier && token.lexeme == "_" {
                // Wildcard pattern
                self.advance();
                end_span = token.span;
                Pattern::Wildcard(token.span)
            } else if token.ty == TokenType::Identifier {
                // Identifier pattern
                self.advance();
                let name = self.interner.intern(&token.lexeme);
                end_span = token.span;
                Pattern::Identifier {
                    name,
                    span: token.span,
                }
            } else {
                return Err(ParseError::new(
                    ParserError::ExpectedToken {
                        expected: "identifier".to_string(),
                        found: token.ty.as_str().to_string(),
                        span: token.span.into(),
                    },
                    token.span,
                ));
            };
            elements.push(elem_pattern);

            if !self.match_token(TokenType::Comma) {
                break;
            }
        }

        self.consume(TokenType::RBracket, "expected ']' after tuple pattern")?;

        Ok(Pattern::Tuple {
            elements,
            span: start_span.merge(end_span),
        })
    }

    /// Parse a while statement
    fn while_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'while'

        let condition = self.expression(0)?;
        let body = self.block()?;
        let span = start_span.merge(body.span);

        Ok(Stmt::While(WhileStmt {
            condition,
            body,
            span,
        }))
    }

    /// Parse a for statement
    fn for_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'for'

        let var_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected loop variable")?;
        let var_name = self.interner.intern(&var_token.lexeme);

        self.consume(TokenType::KwIn, "expected 'in'")?;

        let iterable = self.expression(0)?;

        let body = self.block()?;
        let span = start_span.merge(body.span);

        Ok(Stmt::For(ForStmt {
            var_name,
            iterable,
            body,
            span,
        }))
    }

    /// Parse a continue statement
    fn continue_stmt(&mut self) -> Result<Stmt, ParseError> {
        let span = self.current.span;
        self.advance();
        Ok(Stmt::Continue(span))
    }

    /// Parse an if statement
    fn if_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'if'

        let condition = self.expression(0)?;
        let then_branch = self.block()?;

        let else_branch = if self.match_token(TokenType::KwElse) {
            Some(self.block()?)
        } else {
            None
        };

        let end_span = else_branch
            .as_ref()
            .map(|b| b.span)
            .unwrap_or(then_branch.span);
        let span = start_span.merge(end_span);

        Ok(Stmt::If(IfStmt {
            condition,
            then_branch,
            else_branch,
            span,
        }))
    }

    /// Parse a return statement
    fn return_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'return'

        let value = if self.check(TokenType::Newline)
            || self.check(TokenType::RBrace)
            || self.check(TokenType::Eof)
        {
            None
        } else {
            Some(self.expression(0)?)
        };

        let span = value
            .as_ref()
            .map(|e| start_span.merge(e.span))
            .unwrap_or(start_span);

        Ok(Stmt::Return(ReturnStmt { value, span }))
    }

    /// Parse a raise statement: `raise ErrorName { field: value, ... }`
    fn raise_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'raise'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected error name after raise")?;
        let error_name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::LBrace, "expected '{' after error name")?;
        self.skip_newlines();

        let mut fields = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Parse field: name: expr  OR  name (shorthand for name: name)
            let field_span = self.current.span;
            let field_name_token = self.current.clone();
            self.consume(TokenType::Identifier, "expected field name")?;
            let field_name = self.interner.intern(&field_name_token.lexeme);

            let value = if self.match_token(TokenType::Colon) {
                self.expression(0)?
            } else {
                // Shorthand: field means field: field
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::Identifier(field_name),
                    span: field_span,
                }
            };

            // Allow optional comma
            if self.check(TokenType::Comma) {
                self.advance();
            }

            fields.push(StructFieldInit {
                name: field_name,
                value,
                span: field_span.merge(self.previous.span),
            });
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close raise")?;
        let span = start_span.merge(self.previous.span);

        Ok(Stmt::Raise(RaiseStmt {
            error_name,
            fields,
            span,
        }))
    }

    /// Parse an expression statement
    fn expr_stmt(&mut self) -> Result<Stmt, ParseError> {
        let expr = self.expression(0)?;
        let span = expr.span;
        Ok(Stmt::Expr(ExprStmt { expr, span }))
    }
}
