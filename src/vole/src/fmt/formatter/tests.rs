use super::*;
use crate::fmt::CANONICAL;

/// Helper to format and return just the output string
fn fmt(source: &str) -> String {
    format(source, CANONICAL).unwrap().output
}

#[test]
fn test_format_parses_successfully() {
    // Verify that format can parse valid source
    let source = "let x = 1\n";
    let result = format(source, CANONICAL);
    assert!(result.is_ok());
}

#[test]
fn test_format_rejects_invalid_source() {
    let source = "let = invalid";
    let result = format(source, CANONICAL);
    assert!(result.is_err());
}

#[test]
fn test_format_adds_trailing_newline() {
    // Empty source should still get trailing newline
    let source = "";
    let result = format(source, CANONICAL).unwrap();
    assert!(result.output.ends_with('\n'));
}

// === Let statements ===

#[test]
fn test_let_immutable() {
    assert_eq!(fmt("let x = 1"), "let x = 1\n");
}

#[test]
fn test_let_mutable() {
    assert_eq!(fmt("let mut x = 1"), "let mut x = 1\n");
}

#[test]
fn test_let_with_type() {
    assert_eq!(fmt("let x: i32 = 1"), "let x: i32 = 1\n");
}

#[test]
fn test_let_string() {
    assert_eq!(fmt(r#"let s = "hello""#), "let s = \"hello\"\n");
}

// === Function declarations ===

#[test]
fn test_func_no_params() {
    assert_eq!(fmt("func f() {}"), "func f() {}\n");
}

#[test]
fn test_func_with_params() {
    assert_eq!(
        fmt("func add(a: i32, b: i32) -> i32 { return a + b }"),
        "func add(a: i32, b: i32) -> i32 {\n    return a + b\n}\n"
    );
}

#[test]
fn test_func_no_return_type() {
    assert_eq!(
        fmt("func greet(name: string) { println(name) }"),
        "func greet(name: string) {\n    println(name)\n}\n"
    );
}

// === Expressions ===

#[test]
fn test_binary_operators() {
    assert_eq!(fmt("let x = 1 + 2"), "let x = 1 + 2\n");
    assert_eq!(fmt("let x = 1 - 2"), "let x = 1 - 2\n");
    assert_eq!(fmt("let x = 1 * 2"), "let x = 1 * 2\n");
    assert_eq!(fmt("let x = 1 / 2"), "let x = 1 / 2\n");
    assert_eq!(fmt("let x = 1 % 2"), "let x = 1 % 2\n");
}

#[test]
fn test_comparison_operators() {
    assert_eq!(fmt("let x = 1 == 2"), "let x = 1 == 2\n");
    assert_eq!(fmt("let x = 1 != 2"), "let x = 1 != 2\n");
    assert_eq!(fmt("let x = 1 < 2"), "let x = 1 < 2\n");
    assert_eq!(fmt("let x = 1 > 2"), "let x = 1 > 2\n");
    assert_eq!(fmt("let x = 1 <= 2"), "let x = 1 <= 2\n");
    assert_eq!(fmt("let x = 1 >= 2"), "let x = 1 >= 2\n");
}

#[test]
fn test_logical_operators() {
    assert_eq!(fmt("let x = true && false"), "let x = true && false\n");
    assert_eq!(fmt("let x = true || false"), "let x = true || false\n");
}

#[test]
fn test_unary_operators() {
    assert_eq!(fmt("let x = -1"), "let x = -1\n");
    assert_eq!(fmt("let x = !true"), "let x = !true\n");
}

#[test]
fn test_call_expression() {
    assert_eq!(fmt("let x = foo()"), "let x = foo()\n");
    assert_eq!(fmt("let x = foo(1)"), "let x = foo(1)\n");
    assert_eq!(fmt("let x = foo(1, 2, 3)"), "let x = foo(1, 2, 3)\n");
}

#[test]
fn test_array_literal() {
    // Note: spec says spaces inside brackets, but empty is []
    assert_eq!(fmt("let x = []"), "let x = []\n");
    assert_eq!(fmt("let x = [1, 2, 3]"), "let x = [ 1, 2, 3 ]\n");
}

#[test]
fn test_index_expression() {
    assert_eq!(fmt("let x = arr[0]"), "let x = arr[0]\n");
}

#[test]
fn test_range_expression() {
    assert_eq!(fmt("let x = 0..10"), "let x = 0..10\n");
    assert_eq!(fmt("let x = 0..=10"), "let x = 0..=10\n");
}

#[test]
fn test_nil_literal() {
    assert_eq!(fmt("let x = nil"), "let x = nil\n");
}

#[test]
fn test_bool_literals() {
    assert_eq!(fmt("let x = true"), "let x = true\n");
    assert_eq!(fmt("let x = false"), "let x = false\n");
}

#[test]
fn test_float_literal() {
    assert_eq!(fmt("let x = 3.14"), "let x = 3.14\n");
}

// === Control flow ===

#[test]
fn test_if_statement() {
    assert_eq!(
        fmt("func f() { if true { x = 1 } }"),
        "func f() {\n    if true {\n        x = 1\n    }\n}\n"
    );
}

#[test]
fn test_if_else_statement() {
    assert_eq!(
        fmt("func f() { if true { x = 1 } else { x = 2 } }"),
        "func f() {\n    if true {\n        x = 1\n    } else {\n        x = 2\n    }\n}\n"
    );
}

#[test]
fn test_while_statement() {
    assert_eq!(
        fmt("func f() { while true { x = 1 } }"),
        "func f() {\n    while true {\n        x = 1\n    }\n}\n"
    );
}

#[test]
fn test_for_statement() {
    assert_eq!(
        fmt("func f() { for x in arr { println(x) } }"),
        "func f() {\n    for x in arr {\n        println(x)\n    }\n}\n"
    );
}

#[test]
fn test_break_continue() {
    assert_eq!(
        fmt("func f() { while true { break } }"),
        "func f() {\n    while true {\n        break\n    }\n}\n"
    );
    assert_eq!(
        fmt("func f() { while true { continue } }"),
        "func f() {\n    while true {\n        continue\n    }\n}\n"
    );
}

#[test]
fn test_return_statement() {
    assert_eq!(fmt("func f() { return }"), "func f() {\n    return\n}\n");
    assert_eq!(
        fmt("func f() { return 42 }"),
        "func f() {\n    return 42\n}\n"
    );
}

// === Lambda expressions ===

#[test]
fn test_lambda_simple() {
    assert_eq!(
        fmt("let f = (x: i32) => x * 2"),
        "let f = (x: i32) => x * 2\n"
    );
}

#[test]
fn test_lambda_no_params() {
    assert_eq!(fmt("let f = () => 42"), "let f = () => 42\n");
}

#[test]
fn test_lambda_with_return_type() {
    assert_eq!(
        fmt("let f = (x: i32) -> i32 => x"),
        "let f = (x: i32) -> i32 => x\n"
    );
}

#[test]
fn test_lambda_block_body() {
    assert_eq!(
        fmt("let f = (x: i32) => { return x }"),
        "let f = (x: i32) => {\n    return x\n}\n"
    );
}

// === Match expressions ===

#[test]
fn test_match_expression() {
    let source = r#"let x = match n { 1 => "one" _ => "other" }"#;
    let expected = r#"let x = match n {
    1 => "one"
    _ => "other"
}
"#;
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_match_with_guard() {
    let source = r#"let x = match n { _ if n > 10 => "big" _ => "small" }"#;
    let expected = r#"let x = match n {
    _ if n > 10 => "big"
    _ => "small"
}
"#;
    assert_eq!(fmt(source), expected);
}

// === Struct literals ===

#[test]
fn test_struct_literal() {
    // Note: spec says spaces inside braces
    assert_eq!(
        fmt("let p = Point { x: 1, y: 2 }"),
        "let p = Point { x: 1, y: 2 }\n"
    );
}

#[test]
fn test_struct_literal_empty() {
    assert_eq!(fmt("let p = Point {}"), "let p = Point {}\n");
}

// === Field access and method calls ===

#[test]
fn test_field_access() {
    assert_eq!(fmt("let x = p.x"), "let x = p.x\n");
}

#[test]
fn test_method_call() {
    assert_eq!(fmt("let x = p.sum()"), "let x = p.sum()\n");
    assert_eq!(fmt("let x = p.add(1, 2)"), "let x = p.add(1, 2)\n");
}

// === Assignment ===

#[test]
fn test_assignment() {
    assert_eq!(fmt("func f() { x = 1 }"), "func f() {\n    x = 1\n}\n");
}

#[test]
fn test_compound_assignment() {
    assert_eq!(fmt("func f() { x += 1 }"), "func f() {\n    x += 1\n}\n");
}

// === Type expressions ===

#[test]
fn test_array_type() {
    assert_eq!(fmt("let x: [i32] = []"), "let x: [i32] = []\n");
}

#[test]
fn test_optional_type() {
    assert_eq!(fmt("let x: i32? = nil"), "let x: i32? = nil\n");
}

#[test]
fn test_union_type() {
    assert_eq!(fmt("let x: i32 | string = 1"), "let x: i32 | string = 1\n");
}

#[test]
fn test_function_type() {
    assert_eq!(
        fmt("let f: (i32) -> i32 = (x: i32) => x"),
        "let f: (i32) -> i32 = (x: i32) => x\n"
    );
}

// === Class declarations ===

#[test]
fn test_class_simple() {
    let source = "class Point { x: i32, y: i32, }";
    let expected = "class Point {\n    x: i32,\n    y: i32,\n}\n";
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_class_with_method() {
    let source = "class Point { x: i32, func sum() -> i32 { return self.x } }";
    let expected =
        "class Point {\n    x: i32,\n\n    func sum() -> i32 {\n        return self.x\n    }\n}\n";
    assert_eq!(fmt(source), expected);
}

// === Record declarations ===

#[test]
fn test_record_simple() {
    let source = "record Point { x: i32, y: i32, }";
    let expected = "record Point {\n    x: i32,\n    y: i32,\n}\n";
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_record_with_implements() {
    let source = "record User implements Hashable { id: i64, }";
    let expected = "record User implements Hashable {\n    id: i64,\n}\n";
    assert_eq!(fmt(source), expected);
}

// === Interface declarations ===

#[test]
fn test_interface_with_field() {
    let source = "interface Named { name: string, }";
    let expected = "interface Named {\n    name: string,\n}\n";
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_interface_with_method() {
    let source = "interface Hashable { func hash() -> i64 }";
    let expected = "interface Hashable {\n    func hash() -> i64\n}\n";
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_interface_extends() {
    let source = "interface Extended extends Base { func method() -> i64 }";
    let expected = "interface Extended extends Base {\n    func method() -> i64\n}\n";
    assert_eq!(fmt(source), expected);
}

// === Implement blocks ===

#[test]
fn test_implement_block() {
    let source =
        "implement Describable for Person { func describe() -> string { return self.name } }";
    let expected = "implement Describable for Person {\n    func describe() -> string {\n        return self.name\n    }\n}\n";
    assert_eq!(fmt(source), expected);
}

// === Tests blocks ===

#[test]
fn test_tests_block() {
    let source = r#"tests "example" { test "first" { assert(true) } }"#;
    let expected = r#"tests "example" {
    test "first" {
        assert(true)
    }
}
"#;
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_tests_block_without_label() {
    let source = r#"tests { test "first" { assert(true) } }"#;
    let expected = r#"tests {
    test "first" {
        assert(true)
    }
}
"#;
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_multiple_tests_have_blank_lines() {
    let source = r#"tests { test "a" { assert(true) } test "b" { assert(false) } }"#;
    let expected = r#"tests {
    test "a" {
        assert(true)
    }

    test "b" {
        assert(false)
    }
}
"#;
    assert_eq!(fmt(source), expected);
}

// === Multiple declarations ===

#[test]
fn test_multiple_declarations_have_blank_lines() {
    let source = "let x = 1\nlet y = 2";
    let expected = "let x = 1\n\nlet y = 2\n";
    assert_eq!(fmt(source), expected);
}

#[test]
fn test_func_and_tests() {
    let source = r#"func add(a: i32, b: i32) -> i32 { return a + b } tests { test "add" { assert(add(1, 2) == 3) } }"#;
    let expected = r#"func add(a: i32, b: i32) -> i32 {
    return a + b
}

tests {
    test "add" {
        assert(add(1, 2) == 3)
    }
}
"#;
    assert_eq!(fmt(source), expected);
}

// === String interpolation ===

#[test]
fn test_string_interpolation() {
    let source = r#"let s = "x is {x}""#;
    let expected = "let s = \"x is {x}\"\n";
    assert_eq!(fmt(source), expected);
}

// === Is expression ===

#[test]
fn test_is_expression() {
    assert_eq!(fmt("let b = x is i32"), "let b = x is i32\n");
}

// === Null coalescing ===

#[test]
fn test_null_coalesce() {
    assert_eq!(fmt("let x = a ?? b"), "let x = a ?? b\n");
}

// === Grouping ===

#[test]
fn test_grouping() {
    assert_eq!(fmt("let x = (1 + 2) * 3"), "let x = (1 + 2) * 3\n");
}

// === Idempotency tests ===

/// Format twice and ensure same result (idempotent)
fn assert_idempotent(source: &str) {
    let first = format(source, CANONICAL).unwrap();
    let second = format(&first.output, CANONICAL).unwrap();
    assert_eq!(
        first.output, second.output,
        "Formatting is not idempotent.\nFirst:\n{}\nSecond:\n{}",
        first.output, second.output
    );
    assert!(!second.changed, "Second format should report no changes");
}

#[test]
fn test_idempotent_let() {
    assert_idempotent("let x = 1\n");
    assert_idempotent("let mut x: i32 = 42\n");
}

#[test]
fn test_idempotent_function() {
    assert_idempotent("func add(a: i32, b: i32) -> i32 {\n    return a + b\n}\n");
}

#[test]
fn test_idempotent_class() {
    assert_idempotent("class Point {\n    x: i64,\n    y: i64,\n}\n");
}

#[test]
fn test_idempotent_record() {
    assert_idempotent("record User {\n    id: i64,\n    name: string,\n}\n");
}

#[test]
fn test_idempotent_interface() {
    assert_idempotent("interface Hashable {\n    func hash() -> i64\n}\n");
}

#[test]
fn test_idempotent_tests_block() {
    assert_idempotent("tests {\n    test \"example\" {\n        assert(true)\n    }\n}\n");
}

#[test]
fn test_idempotent_complex() {
    let source = r#"func process(name: string, count: i64) -> bool {
    let result = name.length > count
    if result {
        println("yes")
    } else {
        println("no")
    }
    return result
}
"#;
    assert_idempotent(source);
}

#[test]
fn test_idempotent_lambda() {
    assert_idempotent("let f = (x: i32) => x * 2\n");
}

#[test]
fn test_idempotent_match() {
    let source = r#"let x = match n {
    1 => "one"
    _ => "other"
}
"#;
    assert_idempotent(source);
}
