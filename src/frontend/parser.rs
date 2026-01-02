// src/frontend/parser.rs

use crate::frontend::{
    ast::*, Interner, Lexer, Span, Token, TokenType,
};

pub struct Parser<'src> {
    lexer: Lexer<'src>,
    current: Token,
    previous: Token,
    interner: Interner,
    had_error: bool,
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
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
            had_error: false,
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.expression(0)
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
            Err(ParseError {
                message: format!("{}, found '{}'", msg, self.current.ty.as_str()),
                span: self.current.span,
            })
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
                        return Err(ParseError {
                            message: "invalid assignment target".to_string(),
                            span: left.span,
                        });
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
        if self.check(TokenType::Minus) {
            let op_span = self.current.span;
            self.advance();
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
                let value: i64 = token.lexeme.parse().map_err(|_| ParseError {
                    message: "invalid integer literal".to_string(),
                    span: token.span,
                })?;
                Ok(Expr {
                    kind: ExprKind::IntLiteral(value),
                    span: token.span,
                })
            }
            TokenType::FloatLiteral => {
                self.advance();
                let value: f64 = token.lexeme.parse().map_err(|_| ParseError {
                    message: "invalid float literal".to_string(),
                    span: token.span,
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
            TokenType::StringInterpStart => {
                self.parse_interpolated_string()
            }
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
            TokenType::Error => {
                Err(ParseError {
                    message: token.lexeme.clone(),
                    span: token.span,
                })
            }
            _ => {
                Err(ParseError {
                    message: format!("expected expression, found '{}'", token.ty.as_str()),
                    span: token.span,
                })
            }
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
                    return Err(ParseError {
                        message: "unterminated string interpolation".to_string(),
                        span: self.current.span,
                    });
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
                    ExprKind::Grouping(inner) => {
                        match inner.kind {
                            ExprKind::Binary(inner_bin) => {
                                assert_eq!(inner_bin.op, BinaryOp::Add);
                            }
                            _ => panic!("expected binary inside grouping"),
                        }
                    }
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
            ExprKind::Assign(assign) => {
                match assign.value.kind {
                    ExprKind::IntLiteral(n) => assert_eq!(n, 42),
                    _ => panic!("expected int literal"),
                }
            }
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
}
