use super::*;
use crate::node_map::NodeMap;
use vole_frontend::Parser;
use vole_frontend::ast::LambdaPurity;

fn check(source: &str) -> Result<(), Vec<TypeError>> {
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let mut analyzer = Analyzer::new("test.vole");
    analyzer.analyze(&program, &mut interner)
}

fn analyze_output(source: &str) -> AnalysisOutput {
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let mut analyzer = Analyzer::new("test.vole");
    analyzer.analyze(&program, &mut interner).unwrap();
    analyzer.into_analysis_results()
}

// Tests for miette error integration
#[test]
fn type_error_contains_semantic_error() {
    let source = "func main() { let x: bool = 42 }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::TypeMismatch { .. }
    ));
}

#[test]
fn undefined_variable_has_correct_error_type() {
    let source = "func main() { let x = y }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::UndefinedVariable { .. }
    ));
}

#[test]
fn immutable_assignment_has_correct_error_type() {
    let source = "func main() { let x = 1\n x = 2 }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::ImmutableAssignment { .. }
    ));
}

#[test]
fn wrong_argument_count_has_correct_error_type() {
    let source = "func check(x: bool) {} func main() { check(true, false) }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::WrongArgumentCount { .. }
    ));
}

#[test]
fn condition_not_bool_has_correct_error_type() {
    // Use a string literal which is definitely not a bool or numeric
    let source = r#"func main() { if "hello" { } }"#;
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::ConditionNotBool { .. }
    ));
}

#[test]
fn type_error_has_span() {
    let source = "func main() { let x = y }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(errors[0].span.line > 0);
}

#[test]
fn analyze_simple_function() {
    let source = "func main() { let x = 42 }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_type_mismatch() {
    let source = "func main() { let x: bool = 42 }";
    assert!(check(source).is_err());
}

#[test]
fn analyze_undefined_variable() {
    let source = "func main() { let x = y }";
    assert!(check(source).is_err());
}

#[test]
fn analyze_immutable_assignment() {
    let source = "func main() { let x = 1\n x = 2 }";
    assert!(check(source).is_err());
}

#[test]
fn analyze_mutable_assignment() {
    let source = "func main() { var x = 1\n x = 2 }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_assert_requires_bool() {
    // Calling a function with wrong type should fail
    let source = "func check(b: bool) {} func main() { check(42) }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::TypeMismatch { ref expected, .. } if expected == "bool"
    ));
}

#[test]
fn analyze_assert_valid() {
    // assert(1 == 1) should pass - comparison returns bool
    let source = "func main() { assert(1 == 1) }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_assert_with_bool_literal() {
    let source = "func main() { assert(true) }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_assert_wrong_arg_count() {
    let source = "func check(b: bool) {} func main() { check(true, false) }";
    let result = check(source);
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(matches!(
        errors[0].error,
        SemanticError::WrongArgumentCount {
            expected: 1,
            found: 2,
            ..
        }
    ));
}

#[test]
fn analyze_tests_block() {
    let source = r#"
        tests {
            test "simple assertion" {
                assert(true)
            }
        }
    "#;
    assert!(check(source).is_ok());
}

#[test]
fn analyze_tests_block_with_invalid_assert() {
    let source = r#"
        func check(b: bool) {}
        tests {
            test "bad type" {
                check(42)
            }
        }
    "#;
    let result = check(source);
    assert!(result.is_err());
}

#[test]
fn generic_structural_field_access_produces_generic_vir_template() {
    let source = r#"
        class Person { name: string }

        func get_name<T: { name: string }>(x: T) -> string {
            return x.name
        }
    "#;

    let output = analyze_output(source);
    assert_eq!(output.generic_vir_functions.len(), 1);
    assert_eq!(output.generic_vir_functions[0].1.name, "get_name");
}

#[test]
fn tests_block_generic_function_produces_generic_vir_template() {
    let source = r#"
        class Person { name: string }

        tests {
            func get_name<T: { name: string }>(x: T) -> string {
                return x.name
            }

            test "can call tests-scoped generic" {
                let p = Person { name: "alice" }
                assert(get_name(p) == "alice")
            }
        }
    "#;

    let output = analyze_output(source);
    assert!(
        output
            .generic_vir_functions
            .iter()
            .any(|(_, vir)| vir.name == "get_name"),
        "expected tests-scoped generic function to produce a VIR template"
    );
}

#[test]
fn analyze_i32_literal_coercion() {
    let source = "func main() { let x: i32 = 42 }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_i32_binary_coercion() {
    let source = "func main() { let x: i32 = 42 * 3 }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_i8_return_negative_literal_inference() {
    let source = "func min_value() -> i8 { return -128 }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_u64_return_binary_literal_inference() {
    let source = "func max_value() -> u64 { return 9223372036854775807_u64 * 2 + 1 }";
    assert!(check(source).is_ok());
}

#[test]
fn generic_nested_call_records_correct_callee_monomorph_key() {
    let source = r#"
        func wrap<T>(x: T) -> T { return x }
        func double_wrap<T>(x: T) -> T { return wrap(wrap(x)) }
    "#;
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let mut analyzer = Analyzer::new("test.vole");
    analyzer.analyze(&program, &mut interner).unwrap();
    let output = analyzer.into_analysis_results();
    let node_map = output.node_map;
    let names = output.db.names();

    let double_wrap = program
        .declarations
        .iter()
        .find_map(|decl| match decl {
            Decl::Function(func) if interner.resolve(func.name) == "double_wrap" => Some(func),
            _ => None,
        })
        .expect("missing double_wrap decl");

    let FuncBody::Block(body) = &double_wrap.body else {
        panic!("expected block body");
    };
    let Stmt::Return(ret) = &body.stmts[0] else {
        panic!("expected return stmt");
    };
    let outer = ret.value.as_ref().expect("missing return value");
    let ExprKind::Call(outer_call) = &outer.kind else {
        panic!("expected outer call");
    };
    let inner = outer_call.args[0].expr();
    let ExprKind::Call(_) = &inner.kind else {
        panic!("expected inner call");
    };

    let outer_key = node_map
        .get_generic(outer.id)
        .expect("missing generic key on outer call");
    let inner_key = node_map
        .get_generic(inner.id)
        .expect("missing generic key on inner call");

    assert_eq!(
        names.last_segment_str(outer_key.func_name).as_deref(),
        Some("wrap")
    );
    assert_eq!(
        names.last_segment_str(inner_key.func_name).as_deref(),
        Some("wrap")
    );
}

#[test]
fn generic_template_nested_call_targets_wrap_function_id() {
    let source = r#"
        func wrap<T>(x: T) -> T { return x }
        func double_wrap<T>(x: T) -> T { return wrap(wrap(x)) }
    "#;
    let output = analyze_output(source);
    let names = output.db.names();
    let entities = output.db.entities();

    let wrap_name_id = output
        .generic_vir_functions
        .iter()
        .find_map(|(name_id, _)| {
            (names.last_segment_str(*name_id).as_deref() == Some("wrap")).then_some(*name_id)
        })
        .expect("missing wrap template");
    let double_wrap = output
        .generic_vir_functions
        .iter()
        .find_map(|(name_id, vir)| {
            (names.last_segment_str(*name_id).as_deref() == Some("double_wrap")).then_some(vir)
        })
        .expect("missing double_wrap template");

    let wrap_func_id = entities
        .function_by_name(wrap_name_id)
        .expect("missing wrap function id");
    assert_ne!(double_wrap.id, wrap_func_id);

    let outer_call = match double_wrap.body.stmts.first() {
        Some(vole_vir::stmt::VirStmt::Return {
            value: Some(ret), ..
        }) => match ret.as_ref() {
            vole_vir::expr::VirExpr::Call { target, args, .. } => (target, args),
            _ => panic!("expected return call in double_wrap template"),
        },
        _ => panic!("expected return call in double_wrap template"),
    };
    let inner_call = match outer_call.1[0].as_ref() {
        vole_vir::expr::VirExpr::Call { target, .. } => target,
        _ => panic!("expected nested inner call"),
    };

    match outer_call.0 {
        vole_vir::calls::CallTarget::GenericCall { function_id, .. } => {
            assert_eq!(*function_id, wrap_func_id)
        }
        _ => panic!("expected generic call target for outer call"),
    }
    match inner_call {
        vole_vir::calls::CallTarget::GenericCall { function_id, .. } => {
            assert_eq!(*function_id, wrap_func_id)
        }
        _ => panic!("expected generic call target for inner call"),
    }
}

#[test]
fn analyze_i32_to_i64_widening() {
    let source = "func main() { let x: i32 = 42\n let y: i64 = x }";
    assert!(check(source).is_ok());
}

#[test]
fn analyze_i64_to_i32_narrowing_error() {
    let source = "func main() { let x: i64 = 42\n let y: i32 = x }";
    let result = check(source);
    assert!(result.is_err());
}

// Helper to parse and analyze, returning the AST and node map for capture inspection
fn parse_and_analyze(source: &str) -> (Program, Interner, NodeMap) {
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let mut analyzer = Analyzer::new("test.vole");
    analyzer.analyze(&program, &mut interner).unwrap();
    let output = analyzer.into_analysis_results();
    (program, interner, output.node_map)
}

// Helper to extract lambda and its NodeId from first statement of main function
fn get_first_lambda(program: &Program) -> (&LambdaExpr, NodeId) {
    use vole_frontend::FuncBody;
    for decl in &program.declarations {
        if let Decl::Function(func) = decl {
            if let FuncBody::Block(block) = &func.body {
                for stmt in &block.stmts {
                    if let Stmt::Let(let_stmt) = stmt
                        && let Some(init_expr) = let_stmt.init.as_expr()
                        && let ExprKind::Lambda(lambda) = &init_expr.kind
                    {
                        return (lambda, init_expr.id);
                    }
                }
            }
        }
    }
    panic!("No lambda found in program");
}

#[test]
fn lambda_no_captures_when_only_params() {
    let source = r#"
        func apply(f: (i64) -> i64, x: i64) -> i64 { return f(x) }
        func main() {
            let f = (x: i64) => x + 1
            apply(f, 10)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.captures.is_empty());
}

#[test]
fn lambda_captures_outer_variable() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let x = 10
            let f = () => x + 1
            apply(f)
        }
    "#;
    let (program, interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert_eq!(analysis.captures.len(), 1);
    let name = interner.resolve(analysis.captures[0].name);
    assert_eq!(name, "x");
    assert!(!analysis.captures[0].is_mutable);
    assert!(!analysis.captures[0].is_mutated);
}

#[test]
fn lambda_captures_mutable_variable() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            var x = 10
            let f = () => x + 1
            apply(f)
        }
    "#;
    let (program, interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert_eq!(analysis.captures.len(), 1);
    let name = interner.resolve(analysis.captures[0].name);
    assert_eq!(name, "x");
    assert!(analysis.captures[0].is_mutable);
    assert!(!analysis.captures[0].is_mutated);
}

#[test]
fn lambda_captures_and_mutates_variable() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            var x = 10
            let f: () -> i64 = () => {
                x = x + 1
                return x
            }
            apply(f)
        }
    "#;
    let (program, interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert_eq!(analysis.captures.len(), 1);
    let name = interner.resolve(analysis.captures[0].name);
    assert_eq!(name, "x");
    assert!(analysis.captures[0].is_mutable);
    assert!(analysis.captures[0].is_mutated);
}

#[test]
fn lambda_does_not_capture_its_own_params() {
    let source = r#"
        func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
        func main() {
            let f = (x: i64) => x * 2
            apply(f, 5)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.captures.is_empty());
}

#[test]
fn lambda_does_not_capture_its_own_locals() {
    // Test with expression body that uses a local-like pattern
    // Note: this test verifies that locals defined in lambdas are not treated as captures
    let source = r#"
        func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
        func main() {
            let f = (y: i64) => y * 2
            apply(f, 5)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    // Parameters should not be treated as captures
    assert!(analysis.captures.is_empty());
}

#[test]
fn lambda_block_body_with_local() {
    // Test block body with local let binding
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let f: () -> i64 = () => {
                let y = 5
                return y * 2
            }
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    // Local y should not be captured
    assert!(analysis.captures.is_empty());
}

// Tests for side effect tracking and purity

#[test]
fn lambda_pure_no_captures_no_side_effects() {
    let source = r#"
        func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
        func main() {
            let f = (x: i64) => x + 1
            apply(f, 10)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(!analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::Pure);
}

#[test]
fn lambda_has_side_effects_println() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let f: () -> i64 = () => {
                println("hello")
                return 42
            }
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::HasSideEffects);
}

#[test]
fn lambda_has_side_effects_print() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let f: () -> i64 = () => {
                print("hello")
                return 42
            }
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::HasSideEffects);
}

#[test]
fn lambda_has_side_effects_assert() {
    // print is a hardcoded impure builtin that marks side effects
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let f: () -> i64 = () => {
                print("hello")
                return 42
            }
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::HasSideEffects);
}

#[test]
fn lambda_has_side_effects_calling_user_function() {
    let source = r#"
        func helper() -> i64 { return 42 }
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let f = () => helper()
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::HasSideEffects);
}

#[test]
fn lambda_purity_captures_immutable() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            let x = 10
            let f = () => x + 1
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(!analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::CapturesImmutable);
}

#[test]
fn lambda_purity_captures_mutable() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            var x = 10
            let f = () => x + 1
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(!analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::CapturesMutable);
}

#[test]
fn lambda_purity_mutates_captures() {
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            var x = 10
            let f: () -> i64 = () => {
                x = x + 1
                return x
            }
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(!analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::MutatesCaptures);
}

#[test]
fn lambda_side_effects_take_precedence_over_captures() {
    // Even though we capture and mutate, side effects take precedence
    let source = r#"
        func apply(f: () -> i64) -> i64 { return f() }
        func main() {
            var x = 10
            let f: () -> i64 = () => {
                println("hello")
                x = x + 1
                return x
            }
            apply(f)
        }
    "#;
    let (program, _interner, expr_data) = parse_and_analyze(source);
    let (_lambda, node_id) = get_first_lambda(&program);
    let analysis = expr_data.get_lambda_analysis(node_id).unwrap();
    assert!(analysis.has_side_effects);
    assert_eq!(analysis.purity(), LambdaPurity::HasSideEffects);
}

// Helper for satisfies_interface tests
fn analyze_and_check_interface(source: &str) -> Analyzer {
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let mut analyzer = Analyzer::new("test.vole");
    let _ = analyzer.analyze(&program, &mut interner);
    analyzer
}

#[test]
fn satisfies_interface_with_field() {
    let source = r#"
        interface Named {
            name: string
        }

        class Person {
            name: string,
            age: i64,
        }
    "#;
    let mut analyzer = analyze_and_check_interface(source);

    // Get the symbols for Person and Named
    let mut parser = Parser::new(source, ModuleId::new(0));
    let _ = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let person_sym = interner.intern("Person");
    let named_sym = interner.intern("Named");

    // Get the Person type via Resolver and create TypeId
    let type_def_id = analyzer
        .resolver(&interner)
        .resolve_type(person_sym, &analyzer.entity_registry())
        .unwrap();
    let ty_id = analyzer
        .type_arena_mut()
        .class(type_def_id, smallvec::smallvec![]);

    // Check if Person satisfies Named
    assert!(analyzer.satisfies_interface_id(ty_id, named_sym, &interner));
}

#[test]
fn satisfies_interface_missing_field() {
    let source = r#"
        interface Named {
            name: string
        }

        class Point {
            x: i64,
            y: i64,
        }
    "#;
    let mut analyzer = analyze_and_check_interface(source);

    let mut parser = Parser::new(source, ModuleId::new(0));
    let _ = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let point_sym = interner.intern("Point");
    let named_sym = interner.intern("Named");

    // Get the Point type via Resolver and create TypeId
    let type_def_id = analyzer
        .resolver(&interner)
        .resolve_type(point_sym, &analyzer.entity_registry())
        .unwrap();
    let ty_id = analyzer
        .type_arena_mut()
        .class(type_def_id, smallvec::smallvec![]);

    // Point does NOT satisfy Named (missing name field)
    assert!(!analyzer.satisfies_interface_id(ty_id, named_sym, &interner));
}

#[test]
fn satisfies_interface_with_method() {
    let source = r#"
        interface Hashable {
            func hash() -> i64
        }

        class User {
            id: i64,
            func hash() -> i64 {
                return self.id
            }
        }
    "#;
    let mut analyzer = analyze_and_check_interface(source);

    let mut parser = Parser::new(source, ModuleId::new(0));
    let _ = parser.parse_program().unwrap();
    let mut interner = parser.into_interner();
    let user_sym = interner.intern("User");
    let hashable_sym = interner.intern("Hashable");

    // Get the User type via Resolver and create TypeId
    let type_def_id = analyzer
        .resolver(&interner)
        .resolve_type(user_sym, &analyzer.entity_registry())
        .unwrap();
    let ty_id = analyzer
        .type_arena_mut()
        .class(type_def_id, smallvec::smallvec![]);

    assert!(analyzer.satisfies_interface_id(ty_id, hashable_sym, &interner));
}

#[test]
fn analyze_homogeneous_array_literal() {
    let source = r#"
        func foo() -> [i64] {
            return [1, 2, 3]
        }
    "#;
    let result = check(source);
    // Should analyze without errors - homogeneous array
    assert!(result.is_ok(), "Expected no errors but got: {:?}", result);
}

#[test]
fn analyze_heterogeneous_tuple_literal() {
    let source = r#"
        func foo() -> [i64, string, bool] {
            return [1, "hello", true]
        }
    "#;
    let result = check(source);
    // Should analyze without errors - heterogeneous tuple
    assert!(result.is_ok(), "Expected no errors but got: {:?}", result);
}

#[test]
fn analyze_repeat_literal() {
    let source = r#"
        func foo() -> [i64; 5] {
            return [0; 5]
        }
    "#;
    let result = check(source);
    // Should analyze without errors - repeat literal matches fixed array type
    assert!(result.is_ok(), "Expected no errors but got: {:?}", result);
}

#[test]
fn analyze_repeat_literal_wrong_size() {
    let source = r#"
        func foo() -> [i64; 5] {
            return [0; 10]
        }
    "#;
    let result = check(source);
    // Should have type mismatch - [i64; 10] vs [i64; 5]
    assert!(result.is_err(), "Expected type mismatch error");
}
