// src/frontend/parse_decl.rs
//
// Declaration parsing: functions, tests, classes, interfaces, implement blocks

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
            TokenType::KwStruct => self.struct_decl(),
            TokenType::KwInterface => self.interface_decl(false),
            TokenType::KwStatic => self.static_interface_decl(),
            TokenType::KwImplement => self.implement_block(),
            TokenType::KwError => self.error_decl(),
            TokenType::KwSentinel => self.sentinel_decl(),
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

        // In skip_tests mode, brace-match to find the closing } without parsing the body.
        // Since the lexer already tokenized everything (including strings as single tokens),
        // we just count LBrace/RBrace tokens.
        if self.skip_tests {
            let mut depth: u32 = 1;
            while depth > 0 && !self.check(TokenType::Eof) {
                if self.check(TokenType::LBrace) {
                    depth += 1;
                } else if self.check(TokenType::RBrace) {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                self.advance();
            }
            self.consume(TokenType::RBrace, "expected '}' to close tests block")?;
            let span = start_span.merge(self.previous.span);

            return Ok(Decl::Tests(TestsDecl {
                label,
                decls: Vec::new(),
                tests: Vec::new(),
                span,
            }));
        }

        self.skip_newlines();

        // Parse declarations and test cases in any order
        let mut decls = Vec::new();
        let mut tests = Vec::new();
        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            if self.check(TokenType::KwTest) {
                tests.push(self.test_case()?);
            } else {
                decls.push(self.declaration()?);
            }
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close tests block")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Tests(TestsDecl {
            label,
            decls,
            tests,
            span,
        }))
    }

    fn let_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'let'

        let mutable = self.match_token(TokenType::KwMut);

        // Check for tuple destructuring: let [a, b] = expr
        if self.check(TokenType::LBracket) {
            let pattern = self.parse_tuple_pattern()?;
            self.consume(TokenType::Eq, "expected '=' in let statement")?;
            let init = self.expression(0)?;
            let span = start_span.merge(init.span);

            return Ok(Decl::LetTuple(LetTupleStmt {
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

            return Ok(Decl::LetTuple(LetTupleStmt {
                pattern,
                mutable,
                init,
                span,
            }));
        }

        // Regular let declaration
        let stmt = self.let_statement_inner(mutable, start_span)?;
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

    fn struct_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'struct'

        let name_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected struct name")?;
        let name = self.interner.intern(&name_token.lexeme);

        // Parse optional type parameters: struct Foo<T>
        let type_params = self.parse_type_params()?;

        self.consume(TokenType::LBrace, "expected '{' after struct name")?;
        self.skip_newlines();

        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut statics: Option<StaticsBlock> = None;

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
            } else if self.check(TokenType::KwFunc) {
                // Parse method
                if let Decl::Function(func) = self.function_decl()? {
                    methods.push(func);
                }
            } else if self.check(TokenType::Identifier) {
                // Parse field: name: Type
                let field_span = self.current.span;
                let field_name_token = self.current.clone();
                self.advance();
                let field_name = self.interner.intern(&field_name_token.lexeme);

                self.consume(TokenType::Colon, "expected ':' after field name")?;
                let ty = self.parse_type()?;

                // Parse optional default value: field: Type = expr
                let default_value = if self.match_token(TokenType::Eq) {
                    Some(Box::new(self.expression(0)?))
                } else {
                    None
                };

                // Allow optional comma
                if self.check(TokenType::Comma) {
                    self.advance();
                }

                fields.push(FieldDef {
                    name: field_name,
                    ty,
                    default_value,
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

        self.consume(TokenType::RBrace, "expected '}' to close struct")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Struct(StructDecl {
            name,
            type_params,
            fields,
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

            // Parse optional default value: field: Type = expr
            let default_value = if self.match_token(TokenType::Eq) {
                Some(Box::new(self.expression(0)?))
            } else {
                None
            };

            // Allow optional comma
            if self.check(TokenType::Comma) {
                self.advance();
            }

            fields.push(FieldDef {
                name: field_name,
                ty,
                default_value,
                span: field_span.merge(self.previous.span),
            });
            self.skip_newlines();
        }

        self.consume(TokenType::RBrace, "expected '}' to close error")?;
        let span = start_span.merge(self.previous.span);

        Ok(Decl::Error(ErrorDecl { name, fields, span }))
    }

    fn sentinel_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'sentinel'

        // Accept identifiers and keyword tokens as sentinel names.
        // Keywords like Done and nil are valid sentinel names since
        // the whole point is to declare new sentinel types.
        let name_token = self.current.clone();
        if !self.current.lexeme.is_empty()
            && self.current.lexeme.chars().next().unwrap().is_alphabetic()
        {
            self.advance();
        } else {
            return Err(ParseError::new(
                ParserError::ExpectedIdentifier {
                    span: self.current.span.into(),
                },
                self.current.span,
            ));
        }
        let name = self.interner.intern(&name_token.lexeme);

        let span = start_span.merge(self.previous.span);

        // Error if someone tries to add a body
        if self.check(TokenType::LBrace) {
            return Err(ParseError::new(
                ParserError::SentinelCannotHaveBody {
                    span: self.current.span.into(),
                },
                self.current.span,
            ));
        }

        Ok(Decl::Sentinel(SentinelDecl { name, span }))
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

    /// Parse `static interface` declaration - sugar for interface with only statics
    /// `static interface X { func foo() }` is equivalent to `interface X { statics { func foo() } }`
    fn static_interface_decl(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'static'
        self.consume(
            TokenType::KwInterface,
            "expected 'interface' after 'static'",
        )?;
        self.interface_decl_inner(true, start_span)
    }

    /// Parse interface declaration: interface Name [extends Parent] { methods }
    /// If is_static is true, all methods and external blocks are wrapped in a statics block.
    fn interface_decl(&mut self, is_static: bool) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'interface'
        self.interface_decl_inner(is_static, start_span)
    }

    /// Inner implementation of interface parsing, shared by regular and static interfaces
    fn interface_decl_inner(
        &mut self,
        is_static: bool,
        start_span: crate::Span,
    ) -> Result<Decl, ParseError> {
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

        // For static interfaces, we collect methods/externals into these vectors
        // and wrap them in a StaticsBlock at the end
        let mut static_methods = Vec::new();
        let mut static_external_blocks = Vec::new();
        let body_start_span = self.current.span;

        while !self.check(TokenType::RBrace) && !self.check(TokenType::Eof) {
            // Check for 'default' keyword prefix
            let is_default = self.match_token(TokenType::KwDefault);

            if self.check(TokenType::KwStatics) {
                if is_static {
                    // Static interfaces cannot have explicit statics blocks
                    return Err(ParseError::new(
                        ParserError::UnexpectedToken {
                            token: "statics".to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
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
                if is_static {
                    static_external_blocks.push(block);
                } else {
                    external_blocks.push(block);
                }
            } else if self.check(TokenType::KwFunc) {
                let method = self.interface_method(is_default)?;
                if is_static {
                    static_methods.push(method);
                } else {
                    methods.push(method);
                }
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
                if is_static {
                    // Static interfaces cannot have fields
                    return Err(ParseError::new(
                        ParserError::UnexpectedToken {
                            token: self.current.ty.as_str().to_string(),
                            span: self.current.span.into(),
                        },
                        self.current.span,
                    ));
                }
                // Field: name: type
                let field_span = self.current.span;
                let name_token = self.current.clone();
                self.advance();
                let field_name = self.interner.intern(&name_token.lexeme);

                self.consume(TokenType::Colon, "expected ':' after field name")?;
                let ty = self.parse_type()?;

                // Parse optional default value: field: Type = expr
                let default_value = if self.match_token(TokenType::Eq) {
                    Some(Box::new(self.expression(0)?))
                } else {
                    None
                };

                // Allow optional comma
                if self.check(TokenType::Comma) {
                    self.advance();
                }

                fields.push(FieldDef {
                    name: field_name,
                    ty,
                    default_value,
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

        // For static interfaces, wrap collected methods/externals in a StaticsBlock
        if is_static && (!static_methods.is_empty() || !static_external_blocks.is_empty()) {
            let statics_span = body_start_span.merge(self.previous.span);
            statics = Some(StaticsBlock {
                methods: static_methods,
                external_blocks: static_external_blocks,
                span: statics_span,
            });
        }

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

        // Optional body (default implementation) - block or expression
        let body = if self.check(TokenType::LBrace) {
            Some(FuncBody::Block(self.block()?))
        } else if self.match_token(TokenType::FatArrow) {
            Some(FuncBody::Expr(Box::new(self.expression(0)?)))
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
    /// Trait can be a qualified path like mod.Interface or mod.Interface<T>
    fn implement_block(&mut self) -> Result<Decl, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'implement'

        // Parse: Trait for Type  OR  just Type
        // For the first type:
        //   - If identifier: could be Interface, Interface<T>, mod.Interface
        //   - If keyword (string, i64, etc.): must be a type extension
        // We can only use parse_interface_path() for identifiers since qualified
        // paths start with identifiers (module names).
        let first_type = if self.check(TokenType::Identifier) {
            // Could be interface path or simple type name
            self.parse_interface_path()?
        } else {
            // Must be a primitive type or other type expression (type extension)
            self.parse_type()?
        };

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

    /// Parse an interface path for implement blocks.
    /// Supports:
    ///   - Simple: Interface
    ///   - Generic: Interface<T>
    ///   - Qualified: mod.Interface
    ///   - Qualified generic: mod.Interface<T>
    fn parse_interface_path(&mut self) -> Result<TypeExpr, ParseError> {
        // Must start with identifier
        let first_token = self.current.clone();
        self.consume(TokenType::Identifier, "expected interface name")?;
        let first_sym = self.interner.intern(&first_token.lexeme);

        // Check for dotted path: mod.Interface
        if self.check(TokenType::Dot) {
            let mut segments = vec![first_sym];
            while self.match_token(TokenType::Dot) {
                let seg_token = self.current.clone();
                self.consume(TokenType::Identifier, "expected identifier after '.'")?;
                segments.push(self.interner.intern(&seg_token.lexeme));
            }

            // Check for generic arguments: mod.Interface<T>
            let args = if self.check(TokenType::Lt) {
                self.advance(); // consume '<'
                let mut type_args = Vec::new();
                if !self.check_gt_in_type_context() {
                    type_args.push(self.parse_type()?);
                    while self.match_token(TokenType::Comma) {
                        type_args.push(self.parse_type()?);
                    }
                }
                self.consume_gt_in_type_context()?;
                type_args
            } else {
                Vec::new()
            };

            return Ok(TypeExpr::QualifiedPath { segments, args });
        }

        // Check for generic arguments: Interface<T>
        if self.check(TokenType::Lt) {
            self.advance(); // consume '<'
            let mut args = Vec::new();
            if !self.check_gt_in_type_context() {
                args.push(self.parse_type()?);
                while self.match_token(TokenType::Comma) {
                    args.push(self.parse_type()?);
                }
            }
            self.consume_gt_in_type_context()?;
            return Ok(TypeExpr::Generic {
                name: first_sym,
                args,
            });
        }

        // Simple interface name
        Ok(TypeExpr::Named(first_sym))
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

                // Parse optional default value: field: Type = expr
                let default_value = if self.match_token(TokenType::Eq) {
                    Some(Box::new(self.expression(0)?))
                } else {
                    None
                };

                // Expect comma (required, trailing allowed)
                if self.check(TokenType::Comma) {
                    self.advance();
                }

                fields.push(FieldDef {
                    name,
                    ty,
                    default_value,
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

        // Parse body: either `=> expr` or `{ ... }`
        let body = if self.match_token(TokenType::FatArrow) {
            // Expression body
            let expr = self.parse_expression()?;
            let span = start_span.merge(expr.span);
            return Ok(TestCase {
                name,
                body: FuncBody::Expr(Box::new(expr)),
                span,
            });
        } else {
            // Block body
            let block = self.block()?;
            FuncBody::Block(block)
        };

        let span = start_span.merge(self.previous.span);

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
