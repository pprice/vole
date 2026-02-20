use super::*;

#[test]
fn parse_int_literal() {
    let mut parser = Parser::new("42", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::IntLiteral(n, _) => assert_eq!(n, 42),
        _ => panic!("expected int literal"),
    }
}

#[test]
fn parse_float_literal() {
    let mut parser = Parser::new("3.25", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::FloatLiteral(n, _) => assert!((n - 3.25).abs() < 0.001),
        _ => panic!("expected float literal"),
    }
}

#[test]
fn parse_float_literal_f128_suffix() {
    let mut parser = Parser::new("3.25_f128", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::FloatLiteral(n, Some(NumericSuffix::F128)) => assert!((n - 3.25).abs() < 0.001),
        _ => panic!("expected f128 float literal"),
    }
}

#[test]
fn parse_binary_add() {
    let mut parser = Parser::new("1 + 2", ModuleId::new(0));
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
    let mut parser = Parser::new("1 + 2 * 3", ModuleId::new(0));
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
    let mut parser = Parser::new("println(x)", ModuleId::new(0));
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
    let mut parser = Parser::new("true", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::BoolLiteral(b) => assert!(b),
        _ => panic!("expected bool literal"),
    }

    let mut parser = Parser::new("false", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::BoolLiteral(b) => assert!(!b),
        _ => panic!("expected bool literal"),
    }
}

#[test]
fn parse_string_literal() {
    let mut parser = Parser::new("\"hello world\"", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::StringLiteral(s) => assert_eq!(s, "hello world"),
        _ => panic!("expected string literal"),
    }
}

#[test]
fn parse_grouping() {
    let mut parser = Parser::new("(1 + 2) * 3", ModuleId::new(0));
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
    let mut parser = Parser::new("-42", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::Unary(unary) => {
            assert_eq!(unary.op, UnaryOp::Neg);
            match unary.operand.kind {
                ExprKind::IntLiteral(n, _) => assert_eq!(n, 42),
                _ => panic!("expected int literal"),
            }
        }
        _ => panic!("expected unary"),
    }
}

#[test]
fn parse_assignment() {
    let mut parser = Parser::new("x = 42", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::Assign(assign) => match assign.value.kind {
            ExprKind::IntLiteral(n, _) => assert_eq!(n, 42),
            _ => panic!("expected int literal"),
        },
        _ => panic!("expected assignment"),
    }
}

#[test]
fn parse_interpolated_string() {
    let mut parser = Parser::new("\"hello {name}!\"", ModuleId::new(0));
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
        let mut parser = Parser::new(input, ModuleId::new(0));
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
fn parse_binary_operator_with_newline_after_operator() {
    let mut parser = Parser::new("1 ==\n2", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::Binary(bin) => assert_eq!(bin.op, BinaryOp::Eq),
        _ => panic!("expected binary expression"),
    }
}

#[test]
fn parse_function_call_multiple_args() {
    let mut parser = Parser::new("add(1, 2, 3)", ModuleId::new(0));
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
    let mut parser = Parser::new("foo()", ModuleId::new(0));
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
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 1);
}

#[test]
fn parse_mandelbrot_structure() {
    let source = r#"
func main() {
    let size = 200
    var y = 0
    while y < size {
        var x = 0
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
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 1);
}

#[test]
fn parse_left_associativity() {
    // 1 - 2 - 3 should be (1 - 2) - 3, not 1 - (2 - 3)
    let mut parser = Parser::new("1 - 2 - 3", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();

    // Should be: (left: (1 - 2), op: Sub, right: 3)
    match &expr.kind {
        ExprKind::Binary(outer) => {
            assert_eq!(outer.op, BinaryOp::Sub);
            // Right should be just 3, not (2 - 3)
            match &outer.right.kind {
                ExprKind::IntLiteral(3, _) => {} // correct
                _ => panic!("expected right to be 3, got {:?}", outer.right.kind),
            }
            // Left should be (1 - 2)
            match &outer.left.kind {
                ExprKind::Binary(inner) => {
                    assert_eq!(inner.op, BinaryOp::Sub);
                    match &inner.left.kind {
                        ExprKind::IntLiteral(1, _) => {}
                        _ => panic!("expected inner left to be 1"),
                    }
                    match &inner.right.kind {
                        ExprKind::IntLiteral(2, _) => {}
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
    let mut parser = Parser::new(source, ModuleId::new(0));
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
    let mut parser = Parser::new("@", ModuleId::new(0));
    let result = parser.parse_expression();
    assert!(result.is_err());
    let err = result.unwrap_err();
    // ParseError should contain a ParserError
    assert!(matches!(err.error, ParserError::UnexpectedToken { .. }));
}

#[test]
fn expected_expression_has_correct_error_type() {
    let mut parser = Parser::new("func", ModuleId::new(0));
    let result = parser.parse_expression();
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err.error, ParserError::ExpectedExpression { .. }));
}

#[test]
fn expected_token_has_correct_error_type() {
    let source = "func main( {}";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err.error, ParserError::ExpectedToken { .. }));
}

#[test]
fn expected_type_has_correct_error_type() {
    let source = "func main(x: +) {}";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_err());
    let err = result.unwrap_err();
    // Should get ExpectedType for + where type is expected
    assert!(matches!(err.error, ParserError::ExpectedType { .. }));
}

#[test]
fn parse_error_has_span() {
    let mut parser = Parser::new("@", ModuleId::new(0));
    let result = parser.parse_expression();
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.span.line > 0);
}

#[test]
fn parse_unary_not() {
    let mut parser = Parser::new("!true", ModuleId::new(0));
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
    let mut parser = Parser::new("!!false", ModuleId::new(0));
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
    let mut parser = Parser::new("true && false", ModuleId::new(0));
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
    let mut parser = Parser::new("true || false", ModuleId::new(0));
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
    let mut parser = Parser::new("a || b && c", ModuleId::new(0));
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
    let mut parser = Parser::new("a & b", ModuleId::new(0));
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
    let mut parser = Parser::new("a | b", ModuleId::new(0));
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
    let mut parser = Parser::new("a ^ b", ModuleId::new(0));
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
    let mut parser = Parser::new("a << b", ModuleId::new(0));
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
    let mut parser = Parser::new("a >> b", ModuleId::new(0));
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
    let mut parser = Parser::new("~a", ModuleId::new(0));
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
    let mut parser = Parser::new("a | b ^ c & d", ModuleId::new(0));
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
    let mut parser = Parser::new("a + b << c", ModuleId::new(0));
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
    let mut parser = Parser::new("a && b | c", ModuleId::new(0));
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
    // nil is no longer a keyword; it parses as an identifier
    // (resolved to the prelude sentinel during semantic analysis)
    let mut parser = Parser::new("nil", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    assert!(matches!(expr.kind, ExprKind::Identifier(_)));
}

#[test]
fn parse_optional_type() {
    let mut parser = Parser::new("func foo(x: i32?) {}", ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    if let Decl::Function(f) = &program.declarations[0] {
        assert!(matches!(&f.params[0].ty.kind, TypeExprKind::Optional(_)));
    } else {
        panic!("Expected function declaration");
    }
}

#[test]
fn parse_union_type() {
    let mut parser = Parser::new("func foo(x: i32 | string | nil) {}", ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    if let Decl::Function(f) = &program.declarations[0] {
        assert!(matches!(&f.params[0].ty.kind, TypeExprKind::Union(v) if v.len() == 3));
    } else {
        panic!("Expected function declaration");
    }
}

#[test]
fn parse_null_coalesce() {
    let mut parser = Parser::new("x ?? 0", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    assert!(matches!(expr.kind, ExprKind::NullCoalesce(_)));
}

#[test]
fn parse_is_expression() {
    let mut parser = Parser::new("x is i32", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    assert!(matches!(expr.kind, ExprKind::Is(_)));
}

#[test]
fn parse_nil_type() {
    // nil is no longer a keyword; it parses as a Named type
    // (resolved to the prelude sentinel during semantic analysis)
    let mut parser = Parser::new("func foo(x: nil) {}", ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    if let Decl::Function(f) = &program.declarations[0] {
        assert!(matches!(&f.params[0].ty.kind, TypeExprKind::Named(_)));
    } else {
        panic!("Expected function declaration");
    }
}

#[test]
fn parse_chained_optional() {
    // i32? ? should be (i32?)? (space needed because lexer tokenizes ?? as QuestionQuestion)
    let mut parser = Parser::new("func foo(x: i32? ?) {}", ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Optional(inner) = &f.params[0].ty.kind {
            assert!(matches!(inner.kind, TypeExprKind::Optional(_)));
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
    let mut parser = Parser::new("a ?? b ?? c", ModuleId::new(0));
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
    let mut parser = Parser::new("x is i32?", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match &expr.kind {
        ExprKind::Is(is_expr) => {
            assert!(matches!(&is_expr.type_expr.kind, TypeExprKind::Optional(_)));
        }
        _ => panic!("expected Is expression"),
    }
}

#[test]
fn parse_is_with_union_type() {
    let mut parser = Parser::new("x is i32 | string", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match &expr.kind {
        ExprKind::Is(is_expr) => {
            assert!(matches!(&is_expr.type_expr.kind, TypeExprKind::Union(v) if v.len() == 2));
        }
        _ => panic!("expected Is expression"),
    }
}

#[test]
fn parse_function_type() {
    let mut parser = Parser::new("let f: (i64, i64) -> i64 = x", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        assert!(let_stmt.ty.is_some());
        if let Some(ty) = &let_stmt.ty
            && let TypeExprKind::Function {
                params,
                return_type: _,
            } = &ty.kind
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
    let mut parser = Parser::new("let f = () => 42", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Lambda(lambda) = &let_stmt.init.as_expr().unwrap().kind {
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
    let mut parser = Parser::new("let f = (x) => x", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Lambda(lambda) = &let_stmt.init.as_expr().unwrap().kind {
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
    let mut parser = Parser::new("let f = (x: i64) => x + 1", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Lambda(lambda) = &let_stmt.init.as_expr().unwrap().kind {
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
    let mut parser = Parser::new("let f = (a: i64, b: i64) => a + b", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Lambda(lambda) = &let_stmt.init.as_expr().unwrap().kind {
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
    let mut parser = Parser::new("let f = (x: i64) => { return x + 1 }", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Lambda(lambda) = &let_stmt.init.as_expr().unwrap().kind {
            assert!(matches!(lambda.body, FuncBody::Block(_)));
        } else {
            panic!("expected lambda expression");
        }
    } else {
        panic!("expected let declaration");
    }
}

#[test]
fn parse_grouping_not_lambda() {
    let mut parser = Parser::new("let x = (1 + 2)", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        assert!(
            matches!(
                &let_stmt.init.as_expr().unwrap().kind,
                ExprKind::Grouping(_)
            ),
            "expected Grouping, got {:?}",
            let_stmt.init.as_expr().unwrap().kind
        );
    } else {
        panic!("expected let declaration");
    }
}

#[test]
fn parse_grouping_ident() {
    let mut parser = Parser::new("let x = (y)", ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_ok(), "parse failed: {:?}", result.err());
    let program = result.unwrap();
    if let Decl::Let(let_stmt) = &program.declarations[0] {
        // (y) without => should be grouping
        assert!(
            matches!(
                &let_stmt.init.as_expr().unwrap().kind,
                ExprKind::Grouping(_)
            ),
            "expected Grouping, got {:?}",
            let_stmt.init.as_expr().unwrap().kind
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
    let mut parser = Parser::new(source, ModuleId::new(0));
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
fn parse_struct_literal() {
    let mut parser = Parser::new("Point { x: 10, y: 20 }", ModuleId::new(0));
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
    let mut parser = Parser::new("p.x", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    assert!(matches!(expr.kind, ExprKind::FieldAccess(_)));
}

#[test]
fn parse_method_call() {
    let mut parser = Parser::new("p.sum()", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    assert!(matches!(expr.kind, ExprKind::MethodCall(_)));
}

#[test]
fn parse_method_call_with_args() {
    let mut parser = Parser::new("p.distance(other)", ModuleId::new(0));
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
    let mut parser = Parser::new("a.b.c", ModuleId::new(0));
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
    let mut parser = Parser::new("Empty { }", ModuleId::new(0));
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
    let mut parser = Parser::new("Point { x: 10, y: 20, }", ModuleId::new(0));
    let expr = parser.parse_expression().unwrap();
    match expr.kind {
        ExprKind::StructLiteral(sl) => {
            assert_eq!(sl.fields.len(), 2);
        }
        _ => panic!("expected struct literal"),
    }
}

#[test]
fn parse_import_expr() {
    let mut parser = Parser::new(r#"let math = import "std:math""#, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 1);

    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Import(path) = &let_stmt.init.as_expr().unwrap().kind {
            assert_eq!(path, "std:math");
        } else {
            panic!("Expected Import expression");
        }
    } else {
        panic!("Expected Let declaration");
    }
}

#[test]
fn test_parse_generic_function() {
    let source = "func identity<T>(x: T) -> T { return x }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.type_params.len(), 1);
        assert!(f.type_params[0].constraint.is_none());
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_parse_constrained_type_param() {
    let source = "func show<T: Stringable>(x: T) -> string { return x.to_string() }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.type_params.len(), 1);
        assert!(f.type_params[0].constraint.is_some());
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_parse_generic_function_multiple_params() {
    let source = "func pair<A, B>(a: A, b: B) -> A { return a }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.type_params.len(), 2);
        assert!(f.type_params[0].constraint.is_none());
        assert!(f.type_params[1].constraint.is_none());
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_parse_generic_class() {
    let source = "class Container<T> { item: T }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Class(c) = &program.declarations[0] {
        assert_eq!(c.type_params.len(), 1);
    } else {
        panic!("expected class");
    }
}

#[test]
fn test_parse_generic_interface() {
    let source = r#"
interface Iterable<T> {
    func next() -> T?
}
"#;
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Interface(i) = &program.declarations[0] {
        assert_eq!(i.type_params.len(), 1);
    } else {
        panic!("expected interface");
    }
}

#[test]
fn test_parse_generic_type() {
    let source = "func foo(x: Box<i64>) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Generic { name: _, args } = &f.params[0].ty.kind {
            assert_eq!(args.len(), 1);
        } else {
            panic!("expected generic type");
        }
    }
}

#[test]
fn test_parse_nested_generic_type() {
    let source = "func foo(x: Map<string, i64>) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Generic { args, .. } = &f.params[0].ty.kind {
            assert_eq!(args.len(), 2);
        } else {
            panic!("expected generic type");
        }
    }
}

#[test]
fn test_parse_deeply_nested_generic_type() {
    // Tests >> token splitting: Box<i64>> must be parsed as Box<i64> >
    let source = "func foo(x: Map<string, Box<i64>>) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse nested generics with >>");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Generic { args, .. } = &f.params[0].ty.kind {
            assert_eq!(args.len(), 2, "Map should have 2 type args");
            // Second arg should be Box<i64>
            if let TypeExprKind::Generic {
                args: inner_args, ..
            } = &args[1].kind
            {
                assert_eq!(inner_args.len(), 1, "Box should have 1 type arg");
            } else {
                panic!("expected Box<i64> as second type argument");
            }
        } else {
            panic!("expected generic type");
        }
    }
}

#[test]
fn test_parse_triple_nested_generic() {
    // Tests >>> case: three levels of nesting
    let source = "func foo(x: Outer<Middle<Inner<i64>>>) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse triple nested generics");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Generic { args, .. } = &f.params[0].ty.kind {
            assert_eq!(args.len(), 1);
            if let TypeExprKind::Generic {
                args: middle_args, ..
            } = &args[0].kind
            {
                assert_eq!(middle_args.len(), 1);
                if let TypeExprKind::Generic {
                    args: inner_args, ..
                } = &middle_args[0].kind
                {
                    assert_eq!(inner_args.len(), 1);
                } else {
                    panic!("expected Inner<i64>");
                }
            } else {
                panic!("expected Middle<Inner<i64>>");
            }
        } else {
            panic!("expected generic type");
        }
    }
}

#[test]
fn test_parse_tuple_type() {
    // Tuple type: [i32, string]
    let source = "func foo(x: [i32, string]) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse tuple type");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Tuple(elements) = &f.params[0].ty.kind {
            assert_eq!(elements.len(), 2, "tuple should have 2 elements");
            assert!(matches!(
                elements[0].kind,
                TypeExprKind::Primitive(PrimitiveType::I32)
            ));
            assert!(matches!(
                elements[1].kind,
                TypeExprKind::Primitive(PrimitiveType::String)
            ));
        } else {
            panic!("expected tuple type, got {:?}", f.params[0].ty);
        }
    }
}

#[test]
fn test_parse_tuple_type_three_elements() {
    // Tuple type with 3 elements
    let source = "func foo(x: [i64, bool, f64]) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse 3-element tuple");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Tuple(elements) = &f.params[0].ty.kind {
            assert_eq!(elements.len(), 3);
        } else {
            panic!("expected tuple type");
        }
    }
}

#[test]
fn test_parse_f128_type() {
    let source = "func foo(x: f128) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse f128 type");

    if let Decl::Function(f) = &program.declarations[0] {
        assert!(matches!(
            f.params[0].ty.kind,
            TypeExprKind::Primitive(PrimitiveType::F128)
        ));
    } else {
        panic!("expected function declaration");
    }
}

#[test]
fn test_parse_fixed_array_type() {
    // Fixed array type: [i32; 10]
    let source = "func foo(x: [i32; 10]) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse fixed array type");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::FixedArray { element, size } = &f.params[0].ty.kind {
            assert_eq!(*size, 10);
            assert!(matches!(
                element.kind,
                TypeExprKind::Primitive(PrimitiveType::I32)
            ));
        } else {
            panic!("expected fixed array type, got {:?}", f.params[0].ty);
        }
    }
}

#[test]
fn test_parse_array_type_unchanged() {
    // Regular array type: [i32] - should still work
    let source = "func foo(x: [i32]) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse dynamic array type");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Array(element) = &f.params[0].ty.kind {
            assert!(matches!(
                element.kind,
                TypeExprKind::Primitive(PrimitiveType::I32)
            ));
        } else {
            panic!("expected array type, got {:?}", f.params[0].ty);
        }
    }
}

#[test]
fn test_parse_tuple_trailing_comma() {
    // Tuple with trailing comma
    let source = "func foo(x: [i32, string,]) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse tuple with trailing comma");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExprKind::Tuple(elements) = &f.params[0].ty.kind {
            assert_eq!(elements.len(), 2);
        } else {
            panic!("expected tuple type");
        }
    }
}

#[test]
fn test_parse_repeat_literal() {
    // Repeat literal: [0; 10]
    let source = "let arr = [0; 10]";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().expect("should parse repeat literal");

    if let Decl::Let(l) = &program.declarations[0] {
        if let ExprKind::RepeatLiteral { element, count } = &l.init.as_expr().unwrap().kind {
            assert_eq!(*count, 10);
            if let ExprKind::IntLiteral(n, _) = &element.kind {
                assert_eq!(*n, 0);
            } else {
                panic!("expected int literal as element");
            }
        } else {
            panic!("expected repeat literal");
        }
    }
}

#[test]
fn test_parse_repeat_literal_with_expression() {
    // Repeat literal with expression: [1 + 2; 5]
    let source = "let arr = [1 + 2; 5]";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse repeat literal with expression");

    if let Decl::Let(l) = &program.declarations[0] {
        if let ExprKind::RepeatLiteral { element, count } = &l.init.as_expr().unwrap().kind {
            assert_eq!(*count, 5);
            assert!(matches!(&element.kind, ExprKind::Binary(_)));
        } else {
            panic!("expected repeat literal");
        }
    }
}

#[test]
fn test_parse_array_vs_repeat_disambiguation() {
    // [x] is array literal, [x; 5] is repeat literal
    let source1 = "let a = [x]";
    let mut parser1 = Parser::new(source1, ModuleId::new(0));
    let program1 = parser1.parse_program().expect("should parse array literal");

    if let Decl::Let(l) = &program1.declarations[0] {
        assert!(matches!(
            &l.init.as_expr().unwrap().kind,
            ExprKind::ArrayLiteral(_)
        ));
    }

    let source2 = "let b = [x; 5]";
    let mut parser2 = Parser::new(source2, ModuleId::new(0));
    let program2 = parser2
        .parse_program()
        .expect("should parse repeat literal");

    if let Decl::Let(l) = &program2.declarations[0] {
        assert!(matches!(
            &l.init.as_expr().unwrap().kind,
            ExprKind::RepeatLiteral { .. }
        ));
    }
}

#[test]
fn test_parse_param_default_value() {
    // Parameter with default value: y: i64 = 10
    let source = "func foo(x: i64, y: i64 = 10) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse parameter with default value");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.params.len(), 2);
        // First param should have no default
        assert!(f.params[0].default_value.is_none());
        // Second param should have default value of 10
        if let Some(default) = &f.params[1].default_value {
            assert!(matches!(default.kind, ExprKind::IntLiteral(10, _)));
        } else {
            panic!("expected default value for second parameter");
        }
    } else {
        panic!("expected function declaration");
    }
}

#[test]
fn test_parse_param_default_value_expression() {
    // Parameter with expression as default value
    let source = "func foo(x: i64 = 1 + 2) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse parameter with expression default");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.params.len(), 1);
        if let Some(default) = &f.params[0].default_value {
            assert!(matches!(default.kind, ExprKind::Binary(_)));
        } else {
            panic!("expected default value expression");
        }
    } else {
        panic!("expected function declaration");
    }
}

#[test]
fn test_parse_param_no_default_value() {
    // Parameter without default value (sanity check)
    let source = "func foo(x: i64) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse parameter without default");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.params.len(), 1);
        assert!(f.params[0].default_value.is_none());
    } else {
        panic!("expected function declaration");
    }
}

#[test]
fn test_parse_multiple_params_with_defaults() {
    // Multiple parameters with default values
    let source = "func foo(a: i64, b: i64 = 1, c: i64 = 2) { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse multiple params with defaults");

    if let Decl::Function(f) = &program.declarations[0] {
        assert_eq!(f.params.len(), 3);
        assert!(f.params[0].default_value.is_none());
        assert!(f.params[1].default_value.is_some());
        assert!(f.params[2].default_value.is_some());
    } else {
        panic!("expected function declaration");
    }
}

#[test]
fn parse_sentinel_decl() {
    let source = "sentinel Done";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 1);
    match &program.declarations[0] {
        Decl::Sentinel(s) => {
            let name = parser.interner().resolve(s.name);
            assert_eq!(name, "Done");
        }
        _ => panic!("expected Sentinel declaration"),
    }
}

#[test]
fn parse_sentinel_decl_lowercase() {
    let source = "sentinel nil";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 1);
    match &program.declarations[0] {
        Decl::Sentinel(s) => {
            let name = parser.interner().resolve(s.name);
            assert_eq!(name, "nil");
        }
        _ => panic!("expected Sentinel declaration"),
    }
}

#[test]
fn parse_sentinel_cannot_have_body() {
    let source = "sentinel Foo { }";
    let mut parser = Parser::new(source, ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(
        err.error,
        ParserError::SentinelCannotHaveBody { .. }
    ));
}

#[test]
fn parse_sentinel_with_function() {
    let source = r#"
sentinel Done
func main() {}
"#;
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 2);
    assert!(matches!(&program.declarations[0], Decl::Sentinel(_)));
    assert!(matches!(&program.declarations[1], Decl::Function(_)));
}

#[test]
fn parse_external_where_default_mapping_arm() {
    let source = r#"
external("vole:compiler_intrinsic") {
    func conv<T>(value: T) -> T where {
        f64 => "f64_conv"
        default => "generic_conv"
    }
}
"#;
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser
        .parse_program()
        .expect("should parse where default arm");
    assert_eq!(program.declarations.len(), 1);

    let Decl::External(external) = &program.declarations[0] else {
        panic!("expected external declaration");
    };
    assert_eq!(external.functions.len(), 1);
    let func = &external.functions[0];
    let mappings = func.type_mappings.as_ref().expect("where mappings");
    assert_eq!(mappings.len(), 2);
    assert!(matches!(mappings[0].arm, TypeMappingArm::Exact(_)));
    assert!(matches!(mappings[1].arm, TypeMappingArm::Default));
}

#[test]
fn parse_external_where_rejects_duplicate_default_mapping_arms() {
    let source = r#"
external("vole:compiler_intrinsic") {
    func conv<T>(value: T) -> T where {
        default => "first"
        default => "second"
    }
}
"#;
    let mut parser = Parser::new(source, ModuleId::new(0));
    let result = parser.parse_program();
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(
        err.error,
        ParserError::DuplicateWhereDefaultArm { .. }
    ));
}
