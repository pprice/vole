// src/frontend/parser.rs

use crate::errors::{LexerError, ParserError};
use crate::frontend::{Interner, Lexer, Span, Token, TokenType, ast::*};

pub struct Parser<'src> {
    lexer: Lexer<'src>,
    current: Token,
    previous: Token,
    interner: Interner,
}

/// A parse error wrapping a miette-enabled ParserError
#[derive(Debug)]
pub struct ParseError {
    pub error: ParserError,
    pub span: Span,
}

impl ParseError {
    /// Create a new parse error
    pub fn new(error: ParserError, span: Span) -> Self {
        Self { error, span }
    }
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        Self {
            lexer,
            current,
            previous: Token::new(TokenType::Eof, "", Span::default()),
            interner: Interner::new(),
        }
    }

    /// Create a parser with a custom file name for diagnostics
    pub fn with_file(source: &'src str, file: &str) -> Self {
        let mut lexer = Lexer::new_with_file(source, file);
        let current = lexer.next_token();
        Self {
            lexer,
            current,
            previous: Token::new(TokenType::Eof, "", Span::default()),
            interner: Interner::new(),
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.expression(0)
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut declarations = Vec::new();
        self.skip_newlines();

        while !self.check(TokenType::Eof) {
            declarations.push(self.declaration()?);
            self.skip_newlines();
        }

        Ok(Program { declarations })
    }

    fn skip_newlines(&mut self) {
        while self.current.ty == TokenType::Newline {
            self.current = self.lexer.next_token();
        }
    }

    fn declaration(&mut self) -> Result<Decl, ParseError> {
        match self.current.ty {
            TokenType::KwFunc => self.function_decl(),
            TokenType::KwTests => self.tests_decl(),
            TokenType::KwLet => self.let_decl(),
            _ => Err(ParseError::new(
                ParserError::UnexpectedToken {
                    token: self.current.ty.as_str().to_string(),
                    span: self.current.span.into(),
                },
                self.current.span,
            )),
        }
    }

    fn function_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'func'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected function name")?;
        let name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::LParen, "expected '(' after function name")?;

        let mut params = Vec::new();
        if !self.check(TokenType::RParen) {
            loop {
                let param = self.parse_param()?;
                params.push(param);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RParen, "expected ')' after parameters")?;

        let return_type = if self.match_token(TokenType::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let body = self.block()?;
        let span = start_span.merge(body.span);

        Ok(Decl::Function(FuncDecl {
            name,
            params,
            return_type,
            body,
            span,
        }))
    }

    fn tests_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'tests'

        // Parse optional label
        let label = if self.check(TokenType::StringLiteral) {
            let label_token = self.current.clone();
            self.advance();
            Some(self.process_string_content(&label_token.lexeme))
        } else {
            None
        };

        self.consume(TokenType::LBrace, "expected '{' after 'tests'")?;
        self.skip_newlines();

        let mut tests = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            tests.push(self.test_case()?);
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close tests block")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Tests(TestsDecl { label, tests, span }))
    }

    fn let_decl(&mut self) -> Result<Decl, ParseError> {
        let stmt = self.let_statement()?;
        Ok(Decl::Let(stmt))
    }

    fn test_case(&mut self) -> Result<TestCase, ParseError> {
        let start_span = self.current.span;
        self.consume(TokenType::KwTest, "expected 'test'")?;

        // Get test name (string literal)
        let name = if self.current.ty == TokenType::StringLiteral {
            let name = self.current.lexeme.clone();
            // Remove quotes from lexeme
            let name = name.trim_matches('"').to_string();
            self.advance();
            name
        } else {
            return Err(ParseError::new(
                ParserError::ExpectedToken {
                    expected: "string".to_string(),
                    found: self.current.ty.as_str().to_string(),
                    span: self.current.span.into(),
                },
                self.current.span,
            ));
        };

        let body = self.block()?;
        let span = start_span.merge(body.span);

        Ok(TestCase { name, body, span })
    }

    fn parse_param(&mut self) -> Result<Param, ParseError> {
        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected parameter name")?;
        let name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::Colon, "expected ':' after parameter name")?;
        let ty = self.parse_type()?;

        Ok(Param {
            name,
            ty,
            span: name_token.span,
        })
    }

    fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        let token = self.current.clone();
        match token.ty {
            TokenType::KwI32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I32))
            }
            TokenType::KwI64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I64))
            }
            TokenType::KwF64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::F64))
            }
            TokenType::KwBool => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::Bool))
            }
            TokenType::KwString => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::String))
            }
            TokenType::Identifier => {
                self.advance();
                let sym = self.interner.intern(&token.lexeme);
                Ok(TypeExpr::Named(sym))
            }
            _ => Err(ParseError::new(
                ParserError::ExpectedType {
                    span: token.span.into(),
                },
                token.span,
            )),
        }
    }

    fn block(&mut self) -> Result<Block, ParseError> {
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

    fn statement(&mut self) -> Result<Stmt, ParseError> {
        match self.current.ty {
            TokenType::KwLet => self.let_stmt(),
            TokenType::KwWhile => self.while_stmt(),
            TokenType::KwIf => self.if_stmt(),
            TokenType::KwBreak => {
                let span = self.current.span;
                self.advance();
                Ok(Stmt::Break(span))
            }
            TokenType::KwReturn => self.return_stmt(),
            _ => self.expr_stmt(),
        }
    }

    fn let_stmt(&mut self) -> Result<Stmt, ParseError> {
        let stmt = self.let_statement()?;
        Ok(Stmt::Let(stmt))
    }

    fn let_statement(&mut self) -> Result<LetStmt, ParseError> {
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

    fn expr_stmt(&mut self) -> Result<Stmt, ParseError> {
        let expr = self.expression(0)?;
        let span = expr.span;
        Ok(Stmt::Expr(ExprStmt { expr, span }))
    }

    /// Get a reference to the interner
    pub fn interner(&self) -> &Interner {
        &self.interner
    }

    /// Get a mutable reference to the interner
    pub fn interner_mut(&mut self) -> &mut Interner {
        &mut self.interner
    }

    /// Consume the parser and return the interner
    pub fn into_interner(self) -> Interner {
        self.interner
    }

    /// Take lexer errors (for diagnostic rendering)
    pub fn take_lexer_errors(&mut self) -> Vec<LexerError> {
        self.lexer.take_errors()
    }

    /// Advance to the next token
    fn advance(&mut self) {
        self.previous = std::mem::replace(&mut self.current, self.lexer.next_token());
    }

    /// Check if the current token matches the given type
    fn check(&self, ty: TokenType) -> bool {
        self.current.ty == ty
    }

    /// Consume the current token if it matches, otherwise return false
    fn match_token(&mut self, ty: TokenType) -> bool {
        if self.check(ty) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Require a token of the given type, or return an error
    fn consume(&mut self, ty: TokenType, msg: &str) -> Result<(), ParseError> {
        if self.check(ty) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::new(
                ParserError::ExpectedToken {
                    expected: msg.to_string(),
                    found: self.current.ty.as_str().to_string(),
                    span: self.current.span.into(),
                },
                self.current.span,
            ))
        }
    }

    /// Parse an expression with Pratt parsing
    fn expression(&mut self, min_prec: u8) -> Result<Expr, ParseError> {
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
                TokenType::Eq => {
                    // Assignment - special handling
                    if let ExprKind::Identifier(sym) = left.kind {
                        self.advance();
                        let value = self.expression(0)?;
                        let span = left.span.merge(value.span);
                        return Ok(Expr {
                            kind: ExprKind::Assign(Box::new(AssignExpr { target: sym, value })),
                            span,
                        });
                    } else {
                        return Err(ParseError::new(
                            ParserError::UnexpectedToken {
                                token: "invalid assignment target".to_string(),
                                span: left.span.into(),
                            },
                            left.span,
                        ));
                    }
                }
                _ => break,
            };

            let prec = op_token.ty.precedence();
            self.advance();
            let right = self.expression(prec)?;
            let span = left.span.merge(right.span);

            left = Expr {
                kind: ExprKind::Binary(Box::new(BinaryExpr { left, op, right })),
                span,
            };
        }

        Ok(left)
    }

    /// Parse a unary expression (- or !)
    fn unary(&mut self) -> Result<Expr, ParseError> {
        if self.match_token(TokenType::Minus) {
            let op_span = self.previous.span;
            let operand = self.unary()?;
            let span = op_span.merge(operand.span);
            return Ok(Expr {
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
                kind: ExprKind::Unary(Box::new(UnaryExpr {
                    op: UnaryOp::Not,
                    operand,
                })),
                span,
            });
        }

        self.call()
    }

    /// Parse a call expression (function call)
    fn call(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.primary()?;

        loop {
            if self.match_token(TokenType::LParen) {
                expr = self.finish_call(expr)?;
            } else {
                break;
            }
        }

        Ok(expr)
    }

    /// Finish parsing a function call (after the opening paren)
    fn finish_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
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
                    kind: ExprKind::FloatLiteral(value),
                    span: token.span,
                })
            }
            TokenType::KwTrue => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::BoolLiteral(true),
                    span: token.span,
                })
            }
            TokenType::KwFalse => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::BoolLiteral(false),
                    span: token.span,
                })
            }
            TokenType::StringLiteral => {
                self.advance();
                // Remove surrounding quotes and process escape sequences
                let content = self.process_string_content(&token.lexeme);
                Ok(Expr {
                    kind: ExprKind::StringLiteral(content),
                    span: token.span,
                })
            }
            TokenType::StringInterpStart => self.parse_interpolated_string(),
            TokenType::Identifier => {
                self.advance();
                let sym = self.interner.intern(&token.lexeme);
                Ok(Expr {
                    kind: ExprKind::Identifier(sym),
                    span: token.span,
                })
            }
            TokenType::LParen => {
                self.advance();
                let expr = self.expression(0)?;
                let end_span = self.current.span;
                self.consume(TokenType::RParen, "expected ')' after expression")?;
                let span = token.span.merge(end_span);
                Ok(Expr {
                    kind: ExprKind::Grouping(Box::new(expr)),
                    span,
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

    /// Parse an interpolated string
    fn parse_interpolated_string(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        let mut parts = Vec::new();

        // Process the start token: "text{
        let start_content = self.process_interp_start(&self.current.lexeme.clone());
        if !start_content.is_empty() {
            parts.push(StringPart::Literal(start_content));
        }
        self.advance();

        loop {
            // Parse the expression inside {}
            let expr = self.expression(0)?;
            parts.push(StringPart::Expr(Box::new(expr)));

            match self.current.ty {
                TokenType::StringInterpMiddle => {
                    // }text{ - there's more
                    let middle_content = self.process_interp_middle(&self.current.lexeme.clone());
                    if !middle_content.is_empty() {
                        parts.push(StringPart::Literal(middle_content));
                    }
                    self.advance();
                }
                TokenType::StringInterpEnd => {
                    // }text" - we're done
                    let end_content = self.process_interp_end(&self.current.lexeme.clone());
                    if !end_content.is_empty() {
                        parts.push(StringPart::Literal(end_content));
                    }
                    let end_span = self.current.span;
                    self.advance();
                    let span = start_span.merge(end_span);
                    return Ok(Expr {
                        kind: ExprKind::InterpolatedString(parts),
                        span,
                    });
                }
                _ => {
                    return Err(ParseError::new(
                        ParserError::UnexpectedToken {
                            token: "unterminated string interpolation".to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
            }
        }
    }

    /// Process a string literal content (remove quotes, handle escapes)
    fn process_string_content(&self, lexeme: &str) -> String {
        // Remove surrounding quotes
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process the start of an interpolated string: "text{ -> text
    fn process_interp_start(&self, lexeme: &str) -> String {
        // Remove leading " and trailing {
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process the middle of an interpolated string: }text{ -> text
    fn process_interp_middle(&self, lexeme: &str) -> String {
        // Remove leading } and trailing {
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process the end of an interpolated string: }text" -> text
    fn process_interp_end(&self, lexeme: &str) -> String {
        // Remove leading } and trailing "
        let inner = &lexeme[1..lexeme.len() - 1];
        self.process_escapes(inner)
    }

    /// Process escape sequences in a string
    fn process_escapes(&self, s: &str) -> String {
        let mut result = String::new();
        let mut chars = s.chars().peekable();

        while let Some(c) = chars.next() {
            if c == '\\' {
                match chars.next() {
                    Some('n') => result.push('\n'),
                    Some('t') => result.push('\t'),
                    Some('r') => result.push('\r'),
                    Some('\\') => result.push('\\'),
                    Some('"') => result.push('"'),
                    Some('{') => result.push('{'),
                    Some('}') => result.push('}'),
                    Some(other) => {
                        result.push('\\');
                        result.push(other);
                    }
                    None => result.push('\\'),
                }
            } else {
                result.push(c);
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_int_literal() {
        let mut parser = Parser::new("42");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::IntLiteral(n) => assert_eq!(n, 42),
            _ => panic!("expected int literal"),
        }
    }

    #[test]
    fn parse_float_literal() {
        let mut parser = Parser::new("3.14");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::FloatLiteral(n) => assert!((n - 3.14).abs() < 0.001),
            _ => panic!("expected float literal"),
        }
    }

    #[test]
    fn parse_binary_add() {
        let mut parser = Parser::new("1 + 2");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Add);
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn parse_precedence() {
        // 1 + 2 * 3 should be 1 + (2 * 3)
        let mut parser = Parser::new("1 + 2 * 3");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Add);
                match bin.right.kind {
                    ExprKind::Binary(inner) => {
                        assert_eq!(inner.op, BinaryOp::Mul);
                    }
                    _ => panic!("expected binary on right"),
                }
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn parse_function_call() {
        let mut parser = Parser::new("println(x)");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Call(call) => {
                assert_eq!(call.args.len(), 1);
            }
            _ => panic!("expected call"),
        }
    }

    #[test]
    fn parse_bool_literals() {
        let mut parser = Parser::new("true");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::BoolLiteral(b) => assert!(b),
            _ => panic!("expected bool literal"),
        }

        let mut parser = Parser::new("false");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::BoolLiteral(b) => assert!(!b),
            _ => panic!("expected bool literal"),
        }
    }

    #[test]
    fn parse_string_literal() {
        let mut parser = Parser::new("\"hello world\"");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::StringLiteral(s) => assert_eq!(s, "hello world"),
            _ => panic!("expected string literal"),
        }
    }

    #[test]
    fn parse_grouping() {
        let mut parser = Parser::new("(1 + 2) * 3");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Mul);
                match bin.left.kind {
                    ExprKind::Grouping(inner) => match inner.kind {
                        ExprKind::Binary(inner_bin) => {
                            assert_eq!(inner_bin.op, BinaryOp::Add);
                        }
                        _ => panic!("expected binary inside grouping"),
                    },
                    _ => panic!("expected grouping on left"),
                }
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn parse_unary_neg() {
        let mut parser = Parser::new("-42");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Unary(unary) => {
                assert_eq!(unary.op, UnaryOp::Neg);
                match unary.operand.kind {
                    ExprKind::IntLiteral(n) => assert_eq!(n, 42),
                    _ => panic!("expected int literal"),
                }
            }
            _ => panic!("expected unary"),
        }
    }

    #[test]
    fn parse_assignment() {
        let mut parser = Parser::new("x = 42");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Assign(assign) => match assign.value.kind {
                ExprKind::IntLiteral(n) => assert_eq!(n, 42),
                _ => panic!("expected int literal"),
            },
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn parse_interpolated_string() {
        let mut parser = Parser::new("\"hello {name}!\"");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::InterpolatedString(parts) => {
                assert_eq!(parts.len(), 3);
                match &parts[0] {
                    StringPart::Literal(s) => assert_eq!(s, "hello "),
                    _ => panic!("expected literal part"),
                }
                match &parts[1] {
                    StringPart::Expr(_) => {}
                    _ => panic!("expected expr part"),
                }
                match &parts[2] {
                    StringPart::Literal(s) => assert_eq!(s, "!"),
                    _ => panic!("expected literal part"),
                }
            }
            _ => panic!("expected interpolated string"),
        }
    }

    #[test]
    fn parse_comparison_operators() {
        let test_cases = [
            ("1 == 2", BinaryOp::Eq),
            ("1 != 2", BinaryOp::Ne),
            ("1 < 2", BinaryOp::Lt),
            ("1 > 2", BinaryOp::Gt),
            ("1 <= 2", BinaryOp::Le),
            ("1 >= 2", BinaryOp::Ge),
        ];

        for (input, expected_op) in test_cases {
            let mut parser = Parser::new(input);
            let expr = parser.parse_expression().unwrap();
            match expr.kind {
                ExprKind::Binary(bin) => {
                    assert_eq!(bin.op, expected_op, "failed for input: {}", input);
                }
                _ => panic!("expected binary for input: {}", input),
            }
        }
    }

    #[test]
    fn parse_function_call_multiple_args() {
        let mut parser = Parser::new("add(1, 2, 3)");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Call(call) => {
                assert_eq!(call.args.len(), 3);
            }
            _ => panic!("expected call"),
        }
    }

    #[test]
    fn parse_function_call_no_args() {
        let mut parser = Parser::new("foo()");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::Call(call) => {
                assert_eq!(call.args.len(), 0);
            }
            _ => panic!("expected call"),
        }
    }

    #[test]
    fn parse_function() {
        let source = r#"
func main() {
    let x = 42
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
    }

    #[test]
    fn parse_mandelbrot_structure() {
        let source = r#"
func main() {
    let size = 200
    let mut y = 0
    while y < size {
        let mut x = 0
        while x < size {
            if x == 0 {
                break
            }
            x = x + 1
        }
        y = y + 1
    }
    println("done")
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
    }

    #[test]
    fn parse_left_associativity() {
        // 1 - 2 - 3 should be (1 - 2) - 3, not 1 - (2 - 3)
        let mut parser = Parser::new("1 - 2 - 3");
        let expr = parser.parse_expression().unwrap();

        // Should be: (left: (1 - 2), op: Sub, right: 3)
        match &expr.kind {
            ExprKind::Binary(outer) => {
                assert_eq!(outer.op, BinaryOp::Sub);
                // Right should be just 3, not (2 - 3)
                match &outer.right.kind {
                    ExprKind::IntLiteral(3) => {} // correct
                    _ => panic!("expected right to be 3, got {:?}", outer.right.kind),
                }
                // Left should be (1 - 2)
                match &outer.left.kind {
                    ExprKind::Binary(inner) => {
                        assert_eq!(inner.op, BinaryOp::Sub);
                        match &inner.left.kind {
                            ExprKind::IntLiteral(1) => {}
                            _ => panic!("expected inner left to be 1"),
                        }
                        match &inner.right.kind {
                            ExprKind::IntLiteral(2) => {}
                            _ => panic!("expected inner right to be 2"),
                        }
                    }
                    _ => panic!("expected left to be binary"),
                }
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn parse_tests_block() {
        let source = r#"
tests {
    test "first test" {
        let x = 1
    }
    test "second test" {
        let y = 2
    }
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        match &program.declarations[0] {
            Decl::Tests(tests_decl) => {
                assert_eq!(tests_decl.tests.len(), 2);
                assert_eq!(tests_decl.tests[0].name, "first test");
                assert_eq!(tests_decl.tests[1].name, "second test");
            }
            _ => panic!("expected Tests declaration"),
        }
    }

    // Tests for miette error integration
    #[test]
    fn parse_error_contains_parser_error() {
        let mut parser = Parser::new("@");
        let result = parser.parse_expression();
        assert!(result.is_err());
        let err = result.unwrap_err();
        // ParseError should contain a ParserError
        assert!(matches!(err.error, ParserError::UnexpectedToken { .. }));
    }

    #[test]
    fn expected_expression_has_correct_error_type() {
        let mut parser = Parser::new("func");
        let result = parser.parse_expression();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err.error, ParserError::ExpectedExpression { .. }));
    }

    #[test]
    fn expected_token_has_correct_error_type() {
        let source = "func main( {}";
        let mut parser = Parser::new(source);
        let result = parser.parse_program();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err.error, ParserError::ExpectedToken { .. }));
    }

    #[test]
    fn expected_type_has_correct_error_type() {
        let source = "func main(x: +) {}";
        let mut parser = Parser::new(source);
        let result = parser.parse_program();
        assert!(result.is_err());
        let err = result.unwrap_err();
        // Should get ExpectedType for + where type is expected
        assert!(matches!(err.error, ParserError::ExpectedType { .. }));
    }

    #[test]
    fn parse_error_has_span() {
        let mut parser = Parser::new("@");
        let result = parser.parse_expression();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.span.line > 0);
    }

    #[test]
    fn parse_unary_not() {
        let mut parser = Parser::new("!true");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Unary(un) => {
                assert_eq!(un.op, UnaryOp::Not);
            }
            _ => panic!("expected unary expression"),
        }
    }

    #[test]
    fn parse_double_not() {
        let mut parser = Parser::new("!!false");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Unary(un) => {
                assert_eq!(un.op, UnaryOp::Not);
                match &un.operand.kind {
                    ExprKind::Unary(inner) => {
                        assert_eq!(inner.op, UnaryOp::Not);
                    }
                    _ => panic!("expected nested unary"),
                }
            }
            _ => panic!("expected unary expression"),
        }
    }

    #[test]
    fn parse_logical_and() {
        let mut parser = Parser::new("true && false");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::And);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_logical_or() {
        let mut parser = Parser::new("true || false");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Or);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_logical_precedence() {
        // a || b && c should be a || (b && c) because && binds tighter
        let mut parser = Parser::new("a || b && c");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Or);
                match &bin.right.kind {
                    ExprKind::Binary(inner) => {
                        assert_eq!(inner.op, BinaryOp::And);
                    }
                    _ => panic!("expected && on right"),
                }
            }
            _ => panic!("expected binary expression"),
        }
    }
}
