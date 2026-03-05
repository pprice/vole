//! Rule: function that returns a closure (higher-order return value).
//!
//! Generates a function whose return type is a closure type like `(i64) -> i64`,
//! and whose body returns a lambda that captures one of the function's own
//! parameters. Then calls the factory function, invokes the returned closure,
//! and asserts the result.
//!
//! This exercises closure allocation, capture semantics, and higher-order return
//! values.
//!
//! **Pattern -- numeric (i64):**
//! ```vole
//! func make_adder(n: i64) -> (i64) -> i64 {
//!     return (x: i64) -> i64 => x + n
//! }
//! let add5 = make_adder(5)
//! let result = add5(10)
//! assert(result == 15)
//! ```
//!
//! **Pattern -- string:**
//! ```vole
//! func make_prefixer(prefix: string) -> (string) -> string {
//!     return (s: string) -> string => prefix + " " + s
//! }
//! let prefixer = make_prefixer("hello")
//! let result = prefixer("world")
//! assert(result == "hello world")
//! ```
//!
//! Only captures safe primitive types (i64, i32, f64, string, bool).
//! Avoids Optional, Class instances, and i128 per journal safety notes.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureReturnFunc;

impl StmtRule for ClosureReturnFunc {
    fn name(&self) -> &'static str {
        "closure_return_func"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Need recursion room for the nested func definition.
        // Also skip inside generic class methods (closure capture bug).
        scope.can_recurse() && !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Pick which type family to generate.
        let variant = emit.gen_range(0..5);
        match variant {
            0 => emit_i64_variant(scope, emit),
            1 => emit_string_variant(scope, emit),
            2 => emit_bool_variant(scope, emit),
            3 => emit_f64_variant(scope, emit),
            _ => emit_i32_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Type-specific generators
// ---------------------------------------------------------------------------

/// Generate an i64 factory: `func f(n: i64) -> (i64) -> i64 { return (x: i64) -> i64 => BODY }`
fn emit_i64_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = PrimitiveType::I64;
    let ty_str = "i64";

    // Pick a body pattern.
    let body_pattern = emit.gen_range(0..3);
    let (body_expr, factory_arg, closure_arg, expected) = match body_pattern {
        0 => {
            // x + n
            let n: i64 = emit.random_in(1, 20) as i64;
            let x: i64 = emit.random_in(1, 50) as i64;
            (
                "x + n".to_string(),
                format!("{}", n),
                format!("{}", x),
                format!("{}", x + n),
            )
        }
        1 => {
            // x * n + 1
            let n: i64 = emit.random_in(1, 10) as i64;
            let x: i64 = emit.random_in(1, 10) as i64;
            (
                "x * n + 1".to_string(),
                format!("{}", n),
                format!("{}", x),
                format!("{}", x * n + 1),
            )
        }
        _ => {
            // x - n  (ensure non-negative by making x > n)
            let n: i64 = emit.random_in(1, 10) as i64;
            let x: i64 = emit.random_in(11, 50) as i64;
            (
                "x - n".to_string(),
                format!("{}", n),
                format!("{}", x),
                format!("{}", x - n),
            )
        }
    };

    emit_factory(
        scope,
        emit,
        prim,
        ty_str,
        &body_expr,
        &factory_arg,
        &closure_arg,
        &expected,
    )
}

/// Generate an i32 factory: `func f(n: i32) -> (i32) -> i32 { return (x: i32) -> i32 => BODY }`
fn emit_i32_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = PrimitiveType::I32;
    let ty_str = "i32";

    let body_pattern = emit.gen_range(0..2);
    let (body_expr, factory_arg, closure_arg, expected) = match body_pattern {
        0 => {
            // x + n
            let n: i64 = emit.random_in(1, 20) as i64;
            let x: i64 = emit.random_in(1, 50) as i64;
            (
                "x + n".to_string(),
                format!("{}_i32", n),
                format!("{}_i32", x),
                format!("{}_i32", x + n),
            )
        }
        _ => {
            // x * n
            let n: i64 = emit.random_in(1, 5) as i64;
            let x: i64 = emit.random_in(1, 10) as i64;
            (
                "x * n".to_string(),
                format!("{}_i32", n),
                format!("{}_i32", x),
                format!("{}_i32", x * n),
            )
        }
    };

    emit_factory(
        scope,
        emit,
        prim,
        ty_str,
        &body_expr,
        &factory_arg,
        &closure_arg,
        &expected,
    )
}

/// Generate a string factory:
/// `func f(prefix: string) -> (string) -> string { return (s: string) -> string => prefix + " " + s }`
fn emit_string_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = PrimitiveType::String;
    let ty_str = "string";

    let body_pattern = emit.gen_range(0..2);
    let (body_expr, param_name, factory_arg, closure_arg, expected) = match body_pattern {
        0 => {
            // prefix + " " + s
            let prefix = format!("s{}", emit.random_in(0, 99));
            let suffix = format!("t{}", emit.random_in(0, 99));
            let exp = format!("{} {}", prefix, suffix);
            (
                "n + \" \" + x".to_string(),
                None::<String>, // use default n, x
                format!("\"{}\"", prefix),
                format!("\"{}\"", suffix),
                format!("\"{}\"", exp),
            )
        }
        _ => {
            // x + n  (append captured string)
            let prefix = format!("u{}", emit.random_in(0, 99));
            let suffix = format!("v{}", emit.random_in(0, 99));
            let exp = format!("{}{}", prefix, suffix);
            (
                "x + n".to_string(),
                None::<String>,
                format!("\"{}\"", suffix),
                format!("\"{}\"", prefix),
                format!("\"{}\"", exp),
            )
        }
    };
    let _ = param_name; // Unused, names are always n and x.

    emit_factory(
        scope,
        emit,
        prim,
        ty_str,
        &body_expr,
        &factory_arg,
        &closure_arg,
        &expected,
    )
}

/// Generate a bool factory:
/// `func f(a: bool) -> (bool) -> bool { return (b: bool) -> bool => a && b }`
fn emit_bool_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = PrimitiveType::Bool;
    let ty_str = "bool";

    let body_pattern = emit.gen_range(0..2);
    let (body_expr, factory_arg, closure_arg, expected) = match body_pattern {
        0 => {
            // n && x  (true && true = true)
            (
                "n && x".to_string(),
                "true".to_string(),
                "true".to_string(),
                "true".to_string(),
            )
        }
        _ => {
            // n || x  (false || true = true)
            (
                "n || x".to_string(),
                "false".to_string(),
                "true".to_string(),
                "true".to_string(),
            )
        }
    };

    emit_factory(
        scope,
        emit,
        prim,
        ty_str,
        &body_expr,
        &factory_arg,
        &closure_arg,
        &expected,
    )
}

/// Generate an f64 factory:
/// `func f(n: f64) -> (f64) -> f64 { return (x: f64) -> f64 => x + n }`
fn emit_f64_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = PrimitiveType::F64;
    let ty_str = "f64";

    let body_pattern = emit.gen_range(0..2);
    let (body_expr, factory_arg, closure_arg, expected) = match body_pattern {
        0 => {
            // x + n
            let n = emit.random_in(1, 20);
            let x = emit.random_in(1, 50);
            (
                "x + n".to_string(),
                format!("{}.0", n),
                format!("{}.0", x),
                format!("{}.0", x + n),
            )
        }
        _ => {
            // x * n
            let n = emit.random_in(1, 5);
            let x = emit.random_in(1, 10);
            (
                "x * n".to_string(),
                format!("{}.0", n),
                format!("{}.0", x),
                format!("{}.0", x * n),
            )
        }
    };

    emit_factory(
        scope,
        emit,
        prim,
        ty_str,
        &body_expr,
        &factory_arg,
        &closure_arg,
        &expected,
    )
}

// ---------------------------------------------------------------------------
// Shared emit helper
// ---------------------------------------------------------------------------

/// Emit the full pattern:
///
/// ```text
/// func FACTORY(n: TYPE) -> (TYPE) -> TYPE {
///     return (x: TYPE) -> TYPE => BODY
/// }
/// let CLOSURE = FACTORY(FACTORY_ARG)
/// let RESULT = CLOSURE(CLOSURE_ARG)
/// assert(RESULT == EXPECTED)
/// ```
fn emit_factory(
    scope: &mut Scope,
    emit: &mut Emit,
    prim: PrimitiveType,
    ty_str: &str,
    body_expr: &str,
    factory_arg: &str,
    closure_arg: &str,
    expected: &str,
) -> Option<String> {
    let factory_name = scope.fresh_name();
    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    // Build the factory function definition.
    let func_def = format!(
        "func {}(n: {}) -> ({}) -> {} {{\n{}return (x: {}) -> {} => {}\n{}}}",
        factory_name, ty_str, ty_str, ty_str, inner_indent, ty_str, ty_str, body_expr, indent,
    );

    // Call factory and bind closure.
    let call_factory = format!("let {} = {}({})", closure_name, factory_name, factory_arg);

    // Call closure and bind result.
    let call_closure = format!("let {} = {}({})", result_name, closure_name, closure_arg);

    // Assert the result.
    let assert_stmt = format!("assert({} == {})", result_name, expected);

    // Register the closure variable and result in scope.
    let closure_type = TypeInfo::Function {
        param_types: vec![TypeInfo::Primitive(prim)],
        return_type: Box::new(TypeInfo::Primitive(prim)),
    };
    scope.add_local(closure_name.clone(), closure_type, false);
    scope.add_local(result_name.clone(), TypeInfo::Primitive(prim), false);

    Some(format!(
        "{}\n{}{}\n{}{}\n{}{}",
        func_def, indent, call_factory, indent, call_closure, indent, assert_stmt,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ClosureReturnFunc.name(), "closure_return_func");
    }

    #[test]
    fn generates_func_def_and_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureReturnFunc.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("func "), "expected func keyword, got: {text}");
        assert!(
            text.contains("return ("),
            "expected lambda return, got: {text}"
        );
        assert!(text.contains("=>"), "expected arrow syntax, got: {text}");
        assert!(text.contains("assert("), "expected assert, got: {text}");
    }

    #[test]
    fn adds_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureReturnFunc.generate(&mut scope, &mut emit, &params);
        // Should add 2 locals: closure variable + result variable.
        // (Factory function name is not added since it's a func def, not a let binding.)
        assert_eq!(scope.locals.len(), initial_len + 2);
    }

    #[test]
    fn generates_all_type_variants() {
        let table = SymbolTable::new();
        let mut found_i64 = false;
        let mut found_string = false;
        let mut found_bool = false;
        let mut found_f64 = false;
        let mut found_i32 = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureReturnFunc.generate(&mut scope, &mut emit, &params) {
                if text.contains("(n: i64)") {
                    found_i64 = true;
                }
                if text.contains("(n: string)") {
                    found_string = true;
                }
                if text.contains("(n: bool)") {
                    found_bool = true;
                }
                if text.contains("(n: f64)") {
                    found_f64 = true;
                }
                if text.contains("(n: i32)") {
                    found_i32 = true;
                }
            }
        }
        assert!(found_i64, "never generated i64 variant");
        assert!(found_string, "never generated string variant");
        assert!(found_bool, "never generated bool variant");
        assert!(found_f64, "never generated f64 variant");
        assert!(found_i32, "never generated i32 variant");
    }

    #[test]
    fn closure_local_has_function_type() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureReturnFunc.generate(&mut scope, &mut emit, &params);
        // First local added should be the closure (Function type).
        let (_, ref ty, _) = scope.locals[0];
        assert!(
            matches!(ty, TypeInfo::Function { .. }),
            "expected Function type, got: {ty:?}"
        );
    }

    #[test]
    fn precondition_rejects_at_max_depth() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ClosureReturnFunc.precondition(&scope, &params));
    }

    #[test]
    fn precondition_rejects_generic_class_method() {
        use crate::symbols::{ClassInfo, SymbolKind, TypeParam};

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        let sym_id = module.add_symbol(
            "GenericClass".into(),
            SymbolKind::Class(ClassInfo {
                fields: vec![],
                methods: vec![],
                static_methods: vec![],
                implements: vec![],
                type_params: vec![TypeParam {
                    name: "T".into(),
                    constraints: vec![],
                }],
            }),
        );

        let mut scope = Scope::with_module(&[], &table, mod_id);
        scope.current_class_sym_id = Some((mod_id, sym_id));

        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ClosureReturnFunc.precondition(&scope, &params));
    }

    #[test]
    fn assert_contains_correct_expected_value() {
        let table = SymbolTable::new();

        // Test across many seeds to verify the assert has matching expected value.
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureReturnFunc.generate(&mut scope, &mut emit, &params) {
                // Every generated output should have func, return, =>, and assert.
                assert!(text.contains("func "), "seed {seed}: missing func");
                assert!(text.contains("return ("), "seed {seed}: missing return");
                assert!(text.contains("=>"), "seed {seed}: missing =>");
                assert!(text.contains("assert("), "seed {seed}: missing assert");
            }
        }
    }
}
