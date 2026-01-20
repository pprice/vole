// src/frontend/parse_decl.rs
//
// Declaration parsing: functions, tests, classes, records, interfaces, implement blocks

use super::ast::*;
use super::parser::{ParseError, Parser};
use super::token::TokenType;
use crate::errors::ParserError;

impl<'src> Parser<'src> {
    pub(super) fn declaration(&mut self) -> Result<Decl, ParseError> {
        match self.current.ty {
            TokenType::KwFunc => self.function_decl(),
            TokenType::KwTests => self.tests_decl(),
            TokenType::KwLet => self.let_decl(),
            TokenType::KwClass => self.class_decl(),
            TokenType::KwRecord => self.record_decl(),
            TokenType::KwInterface => self.interface_decl(),
            TokenType::KwImplement => self.implement_block(),
            TokenType::KwError => self.error_decl(),
            TokenType::KwExternal => {
                let block = self.parse_external_block()?;
                Ok(Decl::External(block))
            }
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

        // Parse optional type parameters: func foo<T, U>()
        let type_params = self.parse_type_params()?;

        self.consume(TokenType::LParen, "expected '(' after function name")?;

        let mut params = Vec::new();
        if !self.check(TokenType::RParen) {
            loop {
                let param = self.parse_param()?;
                params.push(param);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
                // Allow trailing comma
                if self.check(TokenType::RParen) {
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

        // Parse body: either `=> expr` or `{ block }`
        let (body, end_span) = if self.match_token(TokenType::FatArrow) {
            let expr = self.expression(0)?;
            let end = expr.span;
            (FuncBody::Expr(Box::new(expr)), end)
        } else {
            let block = self.block()?;
            let end = block.span;
            (FuncBody::Block(block), end)
        };
        let span = start_span.merge(end_span);

        Ok(Decl::Function(FuncDecl {
            name,
            type_params,
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

        // Parse optional type parameters: class Foo<T>
        let type_params = self.parse_type_params()?;

        // Parse optional implements clause
        let implements = self.parse_implements_clause()?;

        self.consume(TokenType::LBrace, "expected '{' after class name")?;
        self.skip_newlines();

        let (fields, external, methods, statics) = self.parse_class_body()?;

        self.consume(TokenType::RBrace, "expected '}' to close class")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Class(ClassDecl {
            name,
            type_params,
            implements,
            fields,
            external,
            methods,
            statics,
            span,
        }))
    }

    fn record_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'record'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected record name")?;
        let name = self.interner.intern(&name_token.lexeme);

        // Parse optional type parameters: record Box<T>
        let type_params = self.parse_type_params()?;

        // Parse optional implements clause
        let implements = self.parse_implements_clause()?;

        self.consume(TokenType::LBrace, "expected '{' after record name")?;
        self.skip_newlines();

        let (fields, external, methods, statics) = self.parse_class_body()?;

        self.consume(TokenType::RBrace, "expected '}' to close record")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Record(RecordDecl {
            name,
            type_params,
            implements,
            fields,
            external,
            methods,
            statics,
            span,
        }))
    }

    fn error_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'error'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected error name")?;
        let name = self.interner.intern(&name_token.lexeme);

        self.consume(TokenType::LBrace, "expected '{' after error name")?;
        self.skip_newlines();

        let mut fields = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Parse field: name: Type
            let field_span = self.current.span;
            let field_name_token = self.current.clone();
            self.consume(TokenType::Identifier, "expected field name")?;
            let field_name = self.interner.intern(&field_name_token.lexeme);

            self.consume(TokenType::Colon, "expected ':' after field name")?;
            let ty = self.parse_type()?;

            // Allow optional comma
            if self.check(TokenType::Comma) {
                self.advance();
            }

            fields.push(FieldDef {
                name: field_name,
                ty,
                span: field_span.merge(self.previous.span),
            });
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close error")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Error(ErrorDecl { name, fields, span }))
    }

    /// Parse: implements Interface1, Interface2<T>, ...
    fn parse_implements_clause(&mut self) -> Result<Vec<TypeExpr>, ParseError> {
        let mut implements = Vec::new();
        if self.match_token(TokenType::KwImplements) {
            loop {
                implements.push(self.parse_type()?);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }
        Ok(implements)
    }

    /// Parse interface declaration: interface Name [extends Parent] { methods }
    fn interface_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'interface'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected interface name")?;
        let name = self.interner.intern(&name_token.lexeme);

        // Parse optional type parameters: interface Iterator<T>
        let type_params = self.parse_type_params()?;

        // Parse optional extends clause
        let mut extends = Vec::new();
        if self.match_token(TokenType::KwExtends) {
            loop {
                let parent_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected parent interface name")?;
                extends.push(self.interner.intern(&parent_token.lexeme));
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::LBrace, "expected '{' after interface name")?;
        self.skip_newlines();

        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut external_blocks = Vec::new();
        let mut statics: Option<StaticsBlock> = None;

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Check for 'default' keyword prefix
            let is_default = self.match_token(TokenType::KwDefault);

            if self.check(TokenType::KwStatics) {
                if statics.is_some() {
                    return Err(ParseError::new(
                        ParserError::DuplicateStaticsBlock {
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
                statics = Some(self.parse_statics_block()?);
            } else if self.check(TokenType::KwExternal) {
                let mut block = self.parse_external_block()?;
                block.is_default = is_default;
                external_blocks.push(block);
            } else if self.check(TokenType::KwFunc) {
                methods.push(self.interface_method(is_default)?);
            } else if is_default {
                // 'default' keyword without 'func' or 'external'
                return Err(ParseError::new(
                    ParserError::ExpectedToken {
                        expected: "'func' or 'external' after 'default'".to_string(),
                        found: self.current.ty.as_str().to_string(),
                        span: self.current.span.into(),
                    },
                    self.current.span,
                ));
            } else if self.check(TokenType::Identifier) {
                // Field: name: type
                let field_span = self.current.span;
                let name_token = self.current.clone();
                self.advance();
                let field_name = self.interner.intern(&name_token.lexeme);

                self.consume(TokenType::Colon, "expected ':' after field name")?;
                let ty = self.parse_type()?;

                // Allow optional comma
                if self.check(TokenType::Comma) {
                    self.advance();
                }

                fields.push(FieldDef {
                    name: field_name,
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

        self.consume(TokenType::RBrace, "expected '}' to close interface")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Interface(InterfaceDecl {
            name,
            type_params,
            extends,
            fields,
            external_blocks,
            methods,
            statics,
            span,
        }))
    }

    /// Parse interface method: func name(params) -> Type or func name(params) -> Type { body }
    /// The is_default flag indicates whether the method was preceded by 'default' keyword.
    fn interface_method(&mut self, is_default: bool) -> Result<InterfaceMethod, ParseError> {
        let start_span = self.current.span;
        self.consume(TokenType::KwFunc, "expected 'func' in interface method")?;

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected method name")?;
        let name = self.interner.intern(&name_token.lexeme);

        // Parse optional type parameters: func name<T, U>(...)
        let type_params = self.parse_type_params()?;

        self.consume(TokenType::LParen, "expected '(' after method name")?;

        let mut params = Vec::new();
        if !self.check(TokenType::RParen) {
            loop {
                let param = self.parse_param()?;
                params.push(param);
                if !self.match_token(TokenType::Comma) {
                    break;
                }
                // Allow trailing comma
                if self.check(TokenType::RParen) {
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

        // Optional body (default implementation)
        let body = if self.check(TokenType::LBrace) {
            Some(self.block()?)
        } else {
            None
        };

        let span = start_span.merge(self.previous.span);

        Ok(InterfaceMethod {
            name,
            type_params,
            params,
            return_type,
            body,
            is_default,
            span,
        })
    }

    /// Parse implement block: implement [Trait for] Type { methods }
    fn implement_block(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'implement'

        // Parse: Trait for Type  OR  just Type
        // Trait can be a generic type like Iterator<i64>
        let first_type = self.parse_type()?;

        let (trait_type, target_type) = if self.match_token(TokenType::KwFor) {
            // implement Trait for Type (Trait may be generic like Iterator<i64>)
            let target = self.parse_type()?;
            (Some(first_type), target)
        } else {
            // implement Type { ... } (type extension)
            (None, first_type)
        };

        self.consume(TokenType::LBrace, "expected '{' in implement block")?;
        self.skip_newlines();

        let mut external = None;
        let mut methods = Vec::new();
        let mut statics = None;
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            if self.check(TokenType::KwStatics) {
                if statics.is_some() {
                    return Err(ParseError::new(
                        ParserError::DuplicateStaticsBlock {
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
                statics = Some(self.parse_statics_block()?);
            } else if self.check(TokenType::KwExternal) {
                if external.is_some() {
                    return Err(ParseError::new(
                        ParserError::DuplicateExternalBlock {
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
                external = Some(self.parse_external_block()?);
            } else if let Decl::Function(func) = self.function_decl()? {
                methods.push(func);
            }
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close implement block")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Implement(ImplementBlock {
            trait_type,
            target_type,
            external,
            methods,
            statics,
            span,
        }))
    }

    #[allow(clippy::type_complexity)]
    fn parse_class_body(
        &mut self,
    ) -> Result<
        (
            Vec<FieldDef>,
            Option<ExternalBlock>,
            Vec<FuncDecl>,
            Option<StaticsBlock>,
        ),
        ParseError,
    > {
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut external = None;
        let mut statics = None;

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            if self.check(TokenType::KwStatics) {
                if statics.is_some() {
                    return Err(ParseError::new(
                        ParserError::DuplicateStaticsBlock {
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
                statics = Some(self.parse_statics_block()?);
            } else if self.check(TokenType::KwExternal) {
                if external.is_some() {
                    return Err(ParseError::new(
                        ParserError::DuplicateExternalBlock {
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
                external = Some(self.parse_external_block()?);
            } else if self.check(TokenType::KwFunc) {
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

        Ok((fields, external, methods, statics))
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

    /// Parse statics block: statics { methods, external blocks }
    /// Contains static methods that are called on the type, not on instances.
    fn parse_statics_block(&mut self) -> Result<StaticsBlock, ParseError> {
        let start_span = self.current.span;
        self.consume(TokenType::KwStatics, "expected 'statics'")?;
        self.consume(TokenType::LBrace, "expected '{' after 'statics'")?;
        self.skip_newlines();

        let mut methods = Vec::new();
        let mut external_blocks = Vec::new();

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Check for 'default' keyword prefix
            let is_default = self.match_token(TokenType::KwDefault);

            if self.check(TokenType::KwExternal) {
                let mut ext_block = self.parse_external_block()?;
                ext_block.is_default = is_default;
                external_blocks.push(ext_block);
            } else if self.check(TokenType::KwFunc) {
                let method = self.interface_method(is_default)?;
                methods.push(method);
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

        self.consume(TokenType::RBrace, "expected '}' to close statics block")?;
        let span = start_span.merge(self.previous.span);

        Ok(StaticsBlock {
            methods,
            external_blocks,
            span,
        })
    }
}
