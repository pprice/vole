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

#[test]
fn parse_import_expr() {
    let mut parser = Parser::new(r#"let math = import "std:math""#);
    let program = parser.parse_program().unwrap();
    assert_eq!(program.declarations.len(), 1);

    if let Decl::Let(let_stmt) = &program.declarations[0] {
        if let ExprKind::Import(path) = &let_stmt.init.kind {
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
    let mut parser = Parser::new(source);
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
    let mut parser = Parser::new(source);
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
    let mut parser = Parser::new(source);
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
fn test_parse_generic_record() {
    let source = "record Box<T> { value: T }";
    let mut parser = Parser::new(source);
    let program = parser.parse_program().expect("should parse");

    if let Decl::Record(r) = &program.declarations[0] {
        assert_eq!(r.type_params.len(), 1);
    } else {
        panic!("expected record");
    }
}

#[test]
fn test_parse_generic_class() {
    let source = "class Container<T> { item: T }";
    let mut parser = Parser::new(source);
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
    let mut parser = Parser::new(source);
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
    let mut parser = Parser::new(source);
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExpr::Generic { name: _, args } = &f.params[0].ty {
            assert_eq!(args.len(), 1);
        } else {
            panic!("expected generic type");
        }
    }
}

#[test]
fn test_parse_nested_generic_type() {
    let source = "func foo(x: Map<string, i64>) { }";
    let mut parser = Parser::new(source);
    let program = parser.parse_program().expect("should parse");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExpr::Generic { args, .. } = &f.params[0].ty {
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
    let mut parser = Parser::new(source);
    let program = parser
        .parse_program()
        .expect("should parse nested generics with >>");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExpr::Generic { args, .. } = &f.params[0].ty {
            assert_eq!(args.len(), 2, "Map should have 2 type args");
            // Second arg should be Box<i64>
            if let TypeExpr::Generic {
                args: inner_args, ..
            } = &args[1]
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
    let mut parser = Parser::new(source);
    let program = parser
        .parse_program()
        .expect("should parse triple nested generics");

    if let Decl::Function(f) = &program.declarations[0] {
        if let TypeExpr::Generic { args, .. } = &f.params[0].ty {
            assert_eq!(args.len(), 1);
            if let TypeExpr::Generic {
                args: middle_args, ..
            } = &args[0]
            {
                assert_eq!(middle_args.len(), 1);
                if let TypeExpr::Generic {
                    args: inner_args, ..
                } = &middle_args[0]
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
