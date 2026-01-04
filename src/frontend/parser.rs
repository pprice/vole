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
            TokenType::KwClass => self.class_decl(),
            TokenType::KwRecord => self.record_decl(),
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

    fn class_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'class'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected class name")?;
        let name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::LBrace, "expected '{' after class name")?;
        self.skip_newlines();

        let (fields, methods) = self.parse_class_body()?;

        self.consume(TokenType::RBrace, "expected '}' to close class")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Class(ClassDecl {
            name,
            fields,
            methods,
            span,
        }))
    }

    fn record_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'record'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected record name")?;
        let name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::LBrace, "expected '{' after record name")?;
        self.skip_newlines();

        let (fields, methods) = self.parse_class_body()?;

        self.consume(TokenType::RBrace, "expected '}' to close record")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Record(RecordDecl {
            name,
            fields,
            methods,
            span,
        }))
    }

    fn parse_class_body(&mut self) -> Result<(Vec<FieldDef>, Vec<FuncDecl>), ParseError> {
        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            if self.check(TokenType::KwFunc) {
                // Parse method
                if let Decl::Function(func) = self.function_decl()? {
                    methods.push(func);
                }
            } else if self.check(TokenType::Identifier) {
                // Parse field: name: Type,
                let field_span = self.current.span;
                let name_token = self.current.clone();
                self.advance();
                let name = self.interner.intern(&name_token.lexeme);

                self.consume(TokenType::Colon, "expected ':' after field name")?;
                let ty = self.parse_type()?;

                // Expect comma (required, trailing allowed)
                if self.check(TokenType::Comma) {
                    self.advance();
                }

                fields.push(FieldDef {
                    name,
                    ty,
                    span: field_span.merge(self.previous.span),
                });
            } else {
                return Err(ParseError::new(
                    ParserError::UnexpectedToken {
                        token: self.current.ty.as_str().to_string(),
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ));
            }
            self.skip_newlines();
        }

        Ok((fields, methods))
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
        // Parse the base type first
        let mut base = self.parse_base_type()?;

        // Check for optional suffix: T?
        while self.match_token(TokenType::Question) {
            base = TypeExpr::Optional(Box::new(base));
        }

        // Check for union: A | B | C
        if self.check(TokenType::Pipe) {
            let mut variants = vec![base];
            while self.match_token(TokenType::Pipe) {
                let mut variant = self.parse_base_type()?;
                // Handle optional on each variant
                while self.match_token(TokenType::Question) {
                    variant = TypeExpr::Optional(Box::new(variant));
                }
                variants.push(variant);
            }
            return Ok(TypeExpr::Union(variants));
        }

        Ok(base)
    }

    fn parse_base_type(&mut self) -> Result<TypeExpr, ParseError> {
        let token = self.current.clone();
        match token.ty {
            TokenType::LParen => {
                // Function type: (T, T) -> R
                self.advance(); // consume '('

                let mut param_types = Vec::new();
                if !self.check(TokenType::RParen) {
                    param_types.push(self.parse_type()?);
                    while self.match_token(TokenType::Comma) {
                        param_types.push(self.parse_type()?);
                    }
                }
                self.consume(
                    TokenType::RParen,
                    "expected ')' after function parameter types",
                )?;
                self.consume(TokenType::Arrow, "expected '->' after function parameters")?;
                let return_type = self.parse_type()?;

                Ok(TypeExpr::Function {
                    params: param_types,
                    return_type: Box::new(return_type),
                })
            }
            TokenType::LBracket => {
                self.advance(); // consume '['
                let elem_type = self.parse_type()?;
                self.consume(TokenType::RBracket, "expected ']' after array element type")?;
                Ok(TypeExpr::Array(Box::new(elem_type)))
            }
            TokenType::KwNil => {
                self.advance();
                Ok(TypeExpr::Nil)
            }
            TokenType::KwI8 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I8))
            }
            TokenType::KwI16 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I16))
            }
            TokenType::KwI32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I32))
            }
            TokenType::KwI64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I64))
            }
            TokenType::KwI128 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::I128))
            }
            TokenType::KwU8 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U8))
            }
            TokenType::KwU16 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U16))
            }
            TokenType::KwU32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U32))
            }
            TokenType::KwU64 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::U64))
            }
            TokenType::KwF32 => {
                self.advance();
                Ok(TypeExpr::Primitive(PrimitiveType::F32))
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

    fn continue_stmt(&mut self) -> Result<Stmt, ParseError> {
        let span = self.current.span;
        self.advance();
        Ok(Stmt::Continue(span))
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

    /// Check if the current position looks like a struct literal.
    /// This uses lookahead to distinguish `Name { field: value }` from `Name { statement }`.
    /// Returns true if:
    /// - Content after `{` is `}` (empty struct literal: `Name { }`)
    /// - Content after `{` is `Identifier :` (field initialization)
    ///
    /// We create a temporary lexer to peek without consuming tokens.
    fn looks_like_struct_literal(&self) -> bool {
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
                TokenType::Ampersand => BinaryOp::BitAnd,
                TokenType::Pipe => BinaryOp::BitOr,
                TokenType::Caret => BinaryOp::BitXor,
                TokenType::LessLess => BinaryOp::Shl,
                TokenType::GreaterGreater => BinaryOp::Shr,
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

        if self.match_token(TokenType::Tilde) {
            let op_span = self.previous.span;
            let operand = self.unary()?;
            let span = op_span.merge(operand.span);
            return Ok(Expr {
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
            TokenType::KwNil => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Nil,
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

                // Check for struct literal: Name { field: value }
                // We need lookahead to distinguish from a block: `size { let x = ... }`
                // A struct literal looks like `Name { identifier: value }` or `Name { }`
                // A block starts with statements, keywords, or expressions without `:` after ident
                if self.check(TokenType::LBrace) && self.looks_like_struct_literal() {
                    return self.struct_literal(sym, token.span);
                }

                Ok(Expr {
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
                                    kind: ExprKind::Identifier(name),
                                    span: ident_span,
                                };
                                let span = start_span.merge(ident_span);
                                return Ok(Expr {
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
                                kind: ExprKind::Identifier(name),
                                span: ident_token.span,
                            };
                            // Parse the rest of the expression with the identifier as left side
                            let expr = self.continue_expression(left, 0)?;
                            let end_span = self.current.span;
                            self.consume(TokenType::RParen, "expected ')' after expression")?;
                            let span = start_span.merge(end_span);
                            return Ok(Expr {
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
                    kind: ExprKind::ArrayLiteral(elements),
                    span: start_span.merge(end_span),
                })
            }
            TokenType::KwMatch => self.match_expr(),
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
            kind: ExprKind::Match(Box::new(MatchExpr {
                scrutinee,
                arms,
                span: start_span.merge(end_span),
            })),
            span: start_span.merge(end_span),
        })
    }

    /// Parse a lambda expression: (params) => body
    fn lambda_expr(&mut self, start_span: Span) -> Result<Expr, ParseError> {
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
    fn lambda_expr_after_first_ident(
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
    fn continue_expression(&mut self, left: Expr, min_prec: u8) -> Result<Expr, ParseError> {
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
                    if let ExprKind::Identifier(sym) = expr.kind {
                        self.advance();
                        let value = self.expression(0)?;
                        let span = expr.span.merge(value.span);
                        return Ok(Expr {
                            kind: ExprKind::Assign(Box::new(AssignExpr { target: sym, value })),
                            span,
                        });
                    } else {
                        return Err(ParseError::new(
                            ParserError::UnexpectedToken {
                                token: "invalid assignment target".to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        ));
                    }
                }
                TokenType::QuestionQuestion => {
                    // Null coalescing
                    self.advance();
                    let default = self.expression(1)?;
                    let span = expr.span.merge(default.span);
                    return Ok(Expr {
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

        match token.ty {
            // Wildcard: _
            TokenType::Identifier if token.lexeme == "_" => {
                self.advance();
                Ok(Pattern::Wildcard(token.span))
            }
            // Identifier (binding pattern)
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

    #[test]
    fn parse_bitwise_and() {
        let mut parser = Parser::new("a & b");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::BitAnd);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_bitwise_or() {
        let mut parser = Parser::new("a | b");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::BitOr);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_bitwise_xor() {
        let mut parser = Parser::new("a ^ b");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::BitXor);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_shift_left() {
        let mut parser = Parser::new("a << b");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Shl);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_shift_right() {
        let mut parser = Parser::new("a >> b");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Shr);
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_bitwise_not() {
        let mut parser = Parser::new("~a");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Unary(un) => {
                assert_eq!(un.op, UnaryOp::BitNot);
            }
            _ => panic!("expected unary expression"),
        }
    }

    #[test]
    fn parse_bitwise_precedence() {
        // a | b ^ c & d should be a | (b ^ (c & d))
        // because & > ^ > |
        let mut parser = Parser::new("a | b ^ c & d");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::BitOr);
                match &bin.right.kind {
                    ExprKind::Binary(xor_bin) => {
                        assert_eq!(xor_bin.op, BinaryOp::BitXor);
                        match &xor_bin.right.kind {
                            ExprKind::Binary(and_bin) => {
                                assert_eq!(and_bin.op, BinaryOp::BitAnd);
                            }
                            _ => panic!("expected & on right of ^"),
                        }
                    }
                    _ => panic!("expected ^ on right of |"),
                }
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_shift_vs_additive_precedence() {
        // a + b << c should be (a + b) << c
        // because + > << in precedence
        let mut parser = Parser::new("a + b << c");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::Shl);
                match &bin.left.kind {
                    ExprKind::Binary(add_bin) => {
                        assert_eq!(add_bin.op, BinaryOp::Add);
                    }
                    _ => panic!("expected + on left of <<"),
                }
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_bitwise_vs_logical_precedence() {
        // a && b | c should be a && (b | c)
        // because | > && in precedence
        let mut parser = Parser::new("a && b | c");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Binary(bin) => {
                assert_eq!(bin.op, BinaryOp::And);
                match &bin.right.kind {
                    ExprKind::Binary(or_bin) => {
                        assert_eq!(or_bin.op, BinaryOp::BitOr);
                    }
                    _ => panic!("expected | on right of &&"),
                }
            }
            _ => panic!("expected binary expression"),
        }
    }

    #[test]
    fn parse_nil_literal() {
        let mut parser = Parser::new("nil");
        let expr = parser.parse_expression().unwrap();
        assert!(matches!(expr.kind, ExprKind::Nil));
    }

    #[test]
    fn parse_optional_type() {
        let mut parser = Parser::new("func foo(x: i32?) {}");
        let program = parser.parse_program().unwrap();
        if let Decl::Function(f) = &program.declarations[0] {
            assert!(matches!(&f.params[0].ty, TypeExpr::Optional(_)));
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn parse_union_type() {
        let mut parser = Parser::new("func foo(x: i32 | string | nil) {}");
        let program = parser.parse_program().unwrap();
        if let Decl::Function(f) = &program.declarations[0] {
            assert!(matches!(&f.params[0].ty, TypeExpr::Union(v) if v.len() == 3));
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn parse_null_coalesce() {
        let mut parser = Parser::new("x ?? 0");
        let expr = parser.parse_expression().unwrap();
        assert!(matches!(expr.kind, ExprKind::NullCoalesce(_)));
    }

    #[test]
    fn parse_is_expression() {
        let mut parser = Parser::new("x is i32");
        let expr = parser.parse_expression().unwrap();
        assert!(matches!(expr.kind, ExprKind::Is(_)));
    }

    #[test]
    fn parse_nil_type() {
        let mut parser = Parser::new("func foo(x: nil) {}");
        let program = parser.parse_program().unwrap();
        if let Decl::Function(f) = &program.declarations[0] {
            assert!(matches!(&f.params[0].ty, TypeExpr::Nil));
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn parse_chained_optional() {
        // i32? ? should be (i32?)? (space needed because lexer tokenizes ?? as QuestionQuestion)
        let mut parser = Parser::new("func foo(x: i32? ?) {}");
        let program = parser.parse_program().unwrap();
        if let Decl::Function(f) = &program.declarations[0] {
            if let TypeExpr::Optional(inner) = &f.params[0].ty {
                assert!(matches!(inner.as_ref(), TypeExpr::Optional(_)));
            } else {
                panic!("Expected Optional type");
            }
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn parse_null_coalesce_right_associative() {
        // a ?? b ?? c should be a ?? (b ?? c)
        let mut parser = Parser::new("a ?? b ?? c");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::NullCoalesce(nc) => {
                // Left should be 'a', right should be 'b ?? c'
                assert!(matches!(nc.value.kind, ExprKind::Identifier(_)));
                assert!(matches!(nc.default.kind, ExprKind::NullCoalesce(_)));
            }
            _ => panic!("expected NullCoalesce"),
        }
    }

    #[test]
    fn parse_is_with_optional_type() {
        let mut parser = Parser::new("x is i32?");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Is(is_expr) => {
                assert!(matches!(&is_expr.type_expr, TypeExpr::Optional(_)));
            }
            _ => panic!("expected Is expression"),
        }
    }

    #[test]
    fn parse_is_with_union_type() {
        let mut parser = Parser::new("x is i32 | string");
        let expr = parser.parse_expression().unwrap();
        match &expr.kind {
            ExprKind::Is(is_expr) => {
                assert!(matches!(&is_expr.type_expr, TypeExpr::Union(v) if v.len() == 2));
            }
            _ => panic!("expected Is expression"),
        }
    }

    #[test]
    fn parse_function_type() {
        let mut parser = Parser::new("let f: (i64, i64) -> i64 = x");
        let result = parser.parse_program();
        assert!(result.is_ok());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            assert!(let_stmt.ty.is_some());
            if let Some(TypeExpr::Function {
                params,
                return_type: _,
            }) = &let_stmt.ty
            {
                assert_eq!(params.len(), 2);
            } else {
                panic!("expected function type");
            }
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_lambda_no_params() {
        let mut parser = Parser::new("let f = () => 42");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            if let ExprKind::Lambda(lambda) = &let_stmt.init.kind {
                assert_eq!(lambda.params.len(), 0);
            } else {
                panic!("expected lambda expression");
            }
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_lambda_one_param() {
        let mut parser = Parser::new("let f = (x) => x");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            if let ExprKind::Lambda(lambda) = &let_stmt.init.kind {
                assert_eq!(lambda.params.len(), 1);
                assert!(lambda.params[0].ty.is_none());
            } else {
                panic!("expected lambda expression");
            }
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_lambda_typed_param() {
        let mut parser = Parser::new("let f = (x: i64) => x + 1");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            if let ExprKind::Lambda(lambda) = &let_stmt.init.kind {
                assert_eq!(lambda.params.len(), 1);
                assert!(lambda.params[0].ty.is_some());
            } else {
                panic!("expected lambda expression");
            }
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_lambda_multiple_params() {
        let mut parser = Parser::new("let f = (a: i64, b: i64) => a + b");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            if let ExprKind::Lambda(lambda) = &let_stmt.init.kind {
                assert_eq!(lambda.params.len(), 2);
            } else {
                panic!("expected lambda expression");
            }
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_lambda_block_body() {
        let mut parser = Parser::new("let f = (x: i64) => { return x + 1 }");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            if let ExprKind::Lambda(lambda) = &let_stmt.init.kind {
                assert!(matches!(lambda.body, LambdaBody::Block(_)));
            } else {
                panic!("expected lambda expression");
            }
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_grouping_not_lambda() {
        let mut parser = Parser::new("let x = (1 + 2)");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            assert!(
                matches!(&let_stmt.init.kind, ExprKind::Grouping(_)),
                "expected Grouping, got {:?}",
                let_stmt.init.kind
            );
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_grouping_ident() {
        let mut parser = Parser::new("let x = (y)");
        let result = parser.parse_program();
        assert!(result.is_ok(), "parse failed: {:?}", result.err());
        let program = result.unwrap();
        if let Decl::Let(let_stmt) = &program.declarations[0] {
            // (y) without => should be grouping
            assert!(
                matches!(&let_stmt.init.kind, ExprKind::Grouping(_)),
                "expected Grouping, got {:?}",
                let_stmt.init.kind
            );
        } else {
            panic!("expected let declaration");
        }
    }

    #[test]
    fn parse_class_declaration() {
        let source = r#"
class Point {
    x: i32,
    y: i32,

    func sum() -> i32 {
        return 42
    }
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        match &program.declarations[0] {
            Decl::Class(class) => {
                assert_eq!(class.fields.len(), 2);
                assert_eq!(class.methods.len(), 1);
            }
            _ => panic!("expected class declaration"),
        }
    }

    #[test]
    fn parse_record_declaration() {
        let source = r#"
record Point {
    x: i32,
    y: i32,
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        match &program.declarations[0] {
            Decl::Record(record) => {
                assert_eq!(record.fields.len(), 2);
                assert_eq!(record.methods.len(), 0);
            }
            _ => panic!("expected record declaration"),
        }
    }

    #[test]
    fn parse_struct_literal() {
        let mut parser = Parser::new("Point { x: 10, y: 20 }");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::StructLiteral(sl) => {
                assert_eq!(sl.fields.len(), 2);
            }
            _ => panic!("expected struct literal"),
        }
    }

    #[test]
    fn parse_field_access() {
        let mut parser = Parser::new("p.x");
        let expr = parser.parse_expression().unwrap();
        assert!(matches!(expr.kind, ExprKind::FieldAccess(_)));
    }

    #[test]
    fn parse_method_call() {
        let mut parser = Parser::new("p.sum()");
        let expr = parser.parse_expression().unwrap();
        assert!(matches!(expr.kind, ExprKind::MethodCall(_)));
    }

    #[test]
    fn parse_method_call_with_args() {
        let mut parser = Parser::new("p.distance(other)");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::MethodCall(mc) => {
                assert_eq!(mc.args.len(), 1);
            }
            _ => panic!("expected method call"),
        }
    }

    #[test]
    fn parse_chained_field_access() {
        let mut parser = Parser::new("a.b.c");
        let expr = parser.parse_expression().unwrap();
        // Should parse as ((a.b).c)
        match expr.kind {
            ExprKind::FieldAccess(fa) => {
                // The outermost is .c
                assert!(matches!(fa.object.kind, ExprKind::FieldAccess(_)));
            }
            _ => panic!("expected field access"),
        }
    }

    #[test]
    fn parse_struct_literal_empty() {
        let mut parser = Parser::new("Empty { }");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::StructLiteral(sl) => {
                assert_eq!(sl.fields.len(), 0);
            }
            _ => panic!("expected struct literal"),
        }
    }

    #[test]
    fn parse_struct_literal_trailing_comma() {
        let mut parser = Parser::new("Point { x: 10, y: 20, }");
        let expr = parser.parse_expression().unwrap();
        match expr.kind {
            ExprKind::StructLiteral(sl) => {
                assert_eq!(sl.fields.len(), 2);
            }
            _ => panic!("expected struct literal"),
        }
    }
}
