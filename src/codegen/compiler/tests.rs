use super::*;
use crate::commands::common::AnalyzedProgram;
use crate::frontend::Parser;
use crate::identity::NameTable;
use crate::sema::EntityRegistry;
use crate::sema::ExpressionData;
use crate::sema::ImplementRegistry;
use crate::sema::TypeTable;
use crate::sema::WellKnownTypes;
use crate::sema::generic::MonomorphCache;

fn compile_and_run(source: &str) -> i64 {
    let mut parser = Parser::new(source);
    let program = parser.parse_program().unwrap();
    let interner = parser.into_interner();

    let analyzed = AnalyzedProgram {
        program,
        interner,
        expression_data: ExpressionData::new(),
        implement_registry: ImplementRegistry::new(),
        module_programs: HashMap::new(),
        monomorph_cache: MonomorphCache::new(),
        name_table: NameTable::new(),
        type_table: TypeTable::new(),
        well_known: WellKnownTypes::new(),
        entity_registry: EntityRegistry::new(),
    };

    let mut jit = JitContext::new();
    {
        let mut compiler = Compiler::new(&mut jit, &analyzed);
        compiler.compile_program(&analyzed.program).unwrap();
    }
    let _ = jit.finalize();

    let fn_ptr = jit.get_function_ptr("main").unwrap();
    let main: extern "C" fn() -> i64 = unsafe { std::mem::transmute(fn_ptr) };
    main()
}

#[test]
fn compile_return_literal() {
    let result = compile_and_run("func main() -> i64 { return 42 }");
    assert_eq!(result, 42);
}

#[test]
fn compile_arithmetic() {
    let result = compile_and_run("func main() -> i64 { return 10 + 32 }");
    assert_eq!(result, 42);
}

#[test]
fn compile_let_and_return() {
    let result = compile_and_run("func main() -> i64 { let x = 40\n return x + 2 }");
    assert_eq!(result, 42);
}

#[test]
fn compile_multiple_ops() {
    let result = compile_and_run("func main() -> i64 { return 2 + 3 * 10 }");
    assert_eq!(result, 32); // 2 + 30
}

#[test]
fn compile_while_loop() {
    let source = r#"
func main() -> i64 {
    let mut x = 0
    while x < 10 {
        x = x + 1
    }
    return x
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 10);
}

#[test]
fn compile_if_else() {
    let source = r#"
func main() -> i64 {
    let x = 10
    if x > 5 {
        return 1
    } else {
        return 0
    }
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 1);
}

#[test]
fn compile_nested_while_with_break() {
    let source = r#"
func main() -> i64 {
    let mut sum = 0
    let mut i = 0
    while i < 100 {
        if i == 5 {
            break
        }
        sum = sum + i
        i = i + 1
    }
    return sum
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 10); // 0+1+2+3+4 = 10
}

#[test]
fn compile_user_function_call() {
    let source = r#"
func add(a: i64, b: i64) -> i64 {
    return a + b
}

func main() -> i64 {
    return add(10, 32)
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 42);
}

#[test]
fn compile_user_function_call_no_args() {
    let source = r#"
func get_answer() -> i64 {
    return 42
}

func main() -> i64 {
    return get_answer()
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 42);
}

#[test]
fn compile_recursive_function() {
    let source = r#"
func factorial(n: i64) -> i64 {
    if n <= 1 {
        return 1
    }
    return n * factorial(n - 1)
}

func main() -> i64 {
    return factorial(5)
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 120); // 5! = 120
}

#[test]
fn compile_println_i64() {
    // Test that println compiles and runs without crashing
    let source = r#"
func main() -> i64 {
    println(42)
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_println_bool() {
    let source = r#"
func main() -> i64 {
    println(true)
    println(false)
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_println_f64() {
    let source = r#"
func main() -> i64 {
    println(3.14)
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_println_string() {
    let source = r#"
func main() -> i64 {
    println("Hello, World!")
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_print_char() {
    let source = r#"
func main() -> i64 {
    print_char(65)
    print_char(10)
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_string_literal_in_let() {
    let source = r#"
func main() -> i64 {
    let s = "test"
    println(s)
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_interpolated_string() {
    let source = r#"
func main() -> i64 {
    let x = 42
    println("The answer is {x}")
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_interpolated_string_multiple() {
    let source = r#"
func main() -> i64 {
    let a = 1
    let b = 2
    println("{a} + {b} = {a + b}")
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_interpolated_string_with_bool() {
    let source = r#"
func main() -> i64 {
    let flag = true
    println("flag is {flag}")
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}

#[test]
fn compile_interpolated_string_with_float() {
    let source = r#"
func main() -> i64 {
    let pi = 3.14159
    println("pi = {pi}")
    return 0
}
"#;
    let result = compile_and_run(source);
    assert_eq!(result, 0);
}
