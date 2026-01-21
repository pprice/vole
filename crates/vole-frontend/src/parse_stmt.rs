// src/frontend/parse_stmt.rs
//
// Statement parsing methods extracted from parser.rs.

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::{Span, TokenType};
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    /// Check if the current position starts an unambiguous type expression.
    /// This is used for type alias detection in `let Name = TypeExpr`.
    ///
    /// Unambiguous patterns:
    /// - Primitive type followed by `|` (e.g., `i32 | i64`)
    /// - Identifier followed by `|` where next is also a type-like token
    /// - Primitive type followed by `?` (e.g., `i32?`)
    fn is_unambiguous_type_pattern(&self) -> bool {
        // Pattern: { ... } - structural type (blocks have statements, not field: type)
        if self.check(TokenType::LBrace) {
            // Peek ahead to see if this looks like a structural type
            // { identifier : ... } is a structural type
            // { statement... } is a block
            let mut lexer_copy = self.lexer.clone();
            let next = lexer_copy.next_token();
            if next.ty == TokenType::Identifier || next.ty == TokenType::KwFunc {
                let after = lexer_copy.next_token();
                // { name: ... } or { func ... } - structural type
                if after.ty == TokenType::Colon || next.ty == TokenType::KwFunc {
                    return true;
                }
            }
            // Empty structural type { }
            if next.ty == TokenType::RBrace {
                return true;
            }
            return false;
        }

        // Check if current token is a type-like token
        let is_type_token = self.is_primitive_type_token() || self.check(TokenType::Identifier);

        if !is_type_token {
            return false;
        }

        // Peek at the next token
        let next = self.peek_token();

        // Pattern: TypeToken | ... - definitely a union type
        if next.ty == TokenType::Pipe {
            return true;
        }

        // Pattern: PrimitiveType? - definitely an optional type
        // (Identifier? could be ternary, so we only do this for primitives)
        if self.is_primitive_type_token() && next.ty == TokenType::Question {
            return true;
        }

        false
    }

    /// Check if the current token is a primitive type keyword
    fn is_primitive_type_token(&self) -> bool {
        matches!(
            self.current.ty,
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
                | TokenType::KwString
                | TokenType::KwNil
        )
    }

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
    pub fn statement(&mut self) -> Result<Stmt, ParseError> {
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
            TokenType::KwFunc => self.nested_func_stmt(),
            _ => self.expr_stmt(),
        }
    }

    /// Parse a nested function declaration as a let-bound lambda
    /// `func foo(x: i64) -> i64 { ... }` becomes `let foo = (x: i64) -> i64 => { ... }`
    fn nested_func_stmt(&mut self) -> Result<Stmt, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'func'

        // Parse function name
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected function name")?;
        let name = self.interner.intern(&name_token.lexeme);

        // Parse parameters (convert Param to LambdaParam)
        self.consume(TokenType::LParen, "expected '(' after function name")?;
        let mut params = Vec::new();
        if !self.check(TokenType::RParen) {
            loop {
                let param = self.parse_param()?;
                // Convert Param (required type) to LambdaParam (optional type)
                params.push(LambdaParam {
                    name: param.name,
                    ty: Some(param.ty),
                    span: param.span,
                });
                if !self.match_token(TokenType::Comma) {
                    break;
                }
                if self.check(TokenType::RParen) {
                    break;
                }
            }
        }
        self.consume(TokenType::RParen, "expected ')' after parameters")?;

        // Parse optional return type
        let return_type = if self.match_token(TokenType::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        // Parse body - block or expression
        let body = if self.match_token(TokenType::FatArrow) {
            let expr = self.expression(0)?;
            FuncBody::Expr(Box::new(expr))
        } else {
            let block = self.block()?;
            FuncBody::Block(block)
        };

        let end_span = match &body {
            FuncBody::Expr(e) => e.span,
            FuncBody::Block(b) => b.span,
        };
        let lambda_span = start_span.merge(end_span);

        // Create lambda expression
        let lambda = LambdaExpr {
            type_params: Vec::new(),
            params,
            return_type,
            body,
            captures: std::cell::RefCell::new(Vec::new()),
            has_side_effects: std::cell::Cell::new(false),
            span: lambda_span,
        };

        let lambda_expr = Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(lambda)),
            span: lambda_span,
        };

        // Create let statement
        let span = start_span.merge(end_span);
        Ok(Stmt::Let(LetStmt {
            name,
            ty: None,
            mutable: false,
            init: LetInit::Expr(lambda_expr),
            span,
        }))
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

        // Check for record destructuring: let { x, y } = expr
        if self.check(TokenType::LBrace) {
            let pattern = self.parse_record_pattern()?;

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

        // Check if RHS is a type expression:
        // 1. Explicit `: type` annotation forces type parsing
        // 2. Unambiguous type patterns (union, structural, etc.)
        let is_type_alias = ty.as_ref().is_some_and(
            |t| matches!(t, TypeExpr::Named(s) if self.interner.resolve(*s) == "type"),
        ) || self.is_unambiguous_type_pattern();

        let (init, end_span) = if is_type_alias {
            let type_expr = self.parse_type()?;
            let end = self.previous.span;
            (LetInit::TypeAlias(type_expr), end)
        } else {
            let expr = self.expression(0)?;
            let end = expr.span;
            (LetInit::Expr(expr), end)
        };

        let span = start_span.merge(end_span);

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

    /// Parse a destructuring pattern (for let statements): supports identifiers, wildcards, tuples, and records
    fn parse_destructure_pattern(&mut self) -> Result<Pattern, ParseError> {
        let token = self.current.clone();

        match token.ty {
            TokenType::LBracket => self.parse_tuple_pattern(),
            TokenType::LBrace => self.parse_record_pattern(),
            TokenType::Identifier if token.lexeme == "_" => {
                self.advance();
                Ok(Pattern::Wildcard(token.span))
            }
            TokenType::Identifier => {
                self.advance();
                let name = self.interner.intern(&token.lexeme);
                Ok(Pattern::Identifier {
                    name,
                    span: token.span,
                })
            }
            _ => Err(ParseError::new(
                ParserError::ExpectedToken {
                    expected: "pattern".to_string(),
                    found: token.ty.as_str().to_string(),
                    span: token.span.into(),
                },
                token.span,
            )),
        }
    }

    /// Parse a tuple destructuring pattern: [a, b, c] or [[a, b], c]
    fn parse_tuple_pattern(&mut self) -> Result<Pattern, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume '['

        let mut elements = Vec::new();

        loop {
            if self.check(TokenType::RBracket) {
                break;
            }

            // Parse element pattern recursively
            let elem_pattern = self.parse_destructure_pattern()?;
            elements.push(elem_pattern);

            if !self.match_token(TokenType::Comma) {
                break;
            }
        }

        self.consume(TokenType::RBracket, "expected ']' after tuple pattern")?;

        Ok(Pattern::Tuple {
            elements,
            span: start_span.merge(self.previous.span),
        })
    }

    /// Parse a record destructuring pattern: { x, y } or { x: a, y: b }
    fn parse_record_pattern(&mut self) -> Result<Pattern, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume '{'
        self.skip_newlines();

        let mut fields = Vec::new();

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Parse field: name or name: binding
            let field_token = self.current.clone();
            self.consume(TokenType::Identifier, "expected field name")?;
            let field_name = self.interner.intern(&field_token.lexeme);
            let mut field_end_span = field_token.span;

            let binding = if self.match_token(TokenType::Colon) {
                // Renamed binding: { x: alias }
                let binding_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected binding name after ':'")?;
                field_end_span = binding_token.span;
                self.interner.intern(&binding_token.lexeme)
            } else {
                // Same name binding: { x }
                field_name
            };

            fields.push(RecordFieldPattern {
                field_name,
                binding,
                span: field_token.span.merge(field_end_span),
            });

            if !self.match_token(TokenType::Comma) {
                break;
            }
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' after record pattern")?;

        Ok(Pattern::Record {
            type_name: None,
            fields,
            span: start_span.merge(self.previous.span),
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
            // Support `else if` by parsing another if statement and wrapping in a block
            if self.check(TokenType::KwIf) {
                let if_stmt = self.if_stmt()?;
                let span = if_stmt.span();
                Some(Block {
                    stmts: vec![if_stmt],
                    span,
                })
            } else {
                Some(self.block()?)
            }
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
