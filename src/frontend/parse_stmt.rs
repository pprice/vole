// src/frontend/parse_stmt.rs
//
// Statement parsing methods extracted from parser.rs.

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::TokenType;

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
            _ => self.expr_stmt(),
        }
    }

    /// Parse a let statement (as a Stmt)
    fn let_stmt(&mut self) -> Result<Stmt, ParseError> {
        let stmt = self.let_statement()?;
        Ok(Stmt::Let(stmt))
    }

    /// Parse a let statement (returns LetStmt directly)
    pub(super) fn let_statement(&mut self) -> Result<LetStmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'let'

        let mutable = self.match_token(TokenType::KwMut);

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

    /// Parse an expression statement
    fn expr_stmt(&mut self) -> Result<Stmt, ParseError> {
        let expr = self.expression(0)?;
        let span = expr.span;
        Ok(Stmt::Expr(ExprStmt { expr, span }))
    }
}
