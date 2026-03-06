//! Rule: generate generic functions with closure parameters.
//!
//! Stresses the intersection of generics with function types by generating
//! module-level generic functions that accept closures as parameters and
//! calling them with concrete closure arguments that force monomorphization.
//!
//! The generic functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 0 -- generic apply:**
//! ```vole
//! func apply_42918<T>(x: T, f: (T) -> T) -> T {
//!     return f(x)
//! }
//! let result_42918 = apply_42918(42, (x: i64) => x * 2)
//! assert(result_42918 == 84)
//! ```
//!
//! **Variant 1 -- generic reduce:**
//! ```vole
//! func reduce_42918<T>(items: [T], init: T, f: (T, T) -> T) -> T {
//!     var acc = init
//!     for item in items {
//!         acc = f(acc, item)
//!     }
//!     return acc
//! }
//! let result_42918 = reduce_42918([1, 2, 3, 4, 5], 0, (a: i64, b: i64) => a + b)
//! assert(result_42918 == 15)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericClosureParam;

impl StmtRule for GenericClosureParam {
    fn name(&self) -> &'static str {
        "generic_closure_param"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Generic functions must be at module level, not inside class methods
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_apply_variant(scope, emit),
            _ => emit_reduce_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: generic apply -- `(T, (T) -> T) -> T`
// ---------------------------------------------------------------------------

/// Generate a generic `apply_<N>` function at module level and call it with
/// an i64 closure.
///
/// ```vole
/// func apply_42918<T>(x: T, f: (T) -> T) -> T {
///     return f(x)
/// }
/// let result_42918 = apply_42918(42, (x: i64) => x * 2)
/// assert(result_42918 == 84)
/// ```
fn emit_apply_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("apply_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(x: T, f: (T) -> T) -> T {{\n    return f(x)\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Pick an input value and a closure operation
    let input_val = emit.gen_i64_range(1, 50);
    let (closure, expected) = pick_apply_closure(emit, input_val);

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    let code = format!(
        "let {rn} = {fn_name}({input}, {closure})\n{indent}assert({rn} == {expected})",
        rn = result_name,
        fn_name = fn_name,
        input = input_val,
        closure = closure,
        expected = expected,
        indent = indent,
    );

    Some(code)
}

/// Pick a closure and compute the expected result for the apply variant.
fn pick_apply_closure(emit: &mut Emit, input: i64) -> (String, i64) {
    let op = emit.gen_range(0..3);
    match op {
        0 => {
            // multiplication
            let factor = emit.gen_i64_range(2, 5);
            (format!("(x: i64) => x * {}", factor), input * factor)
        }
        1 => {
            // addition
            let addend = emit.gen_i64_range(1, 20);
            (format!("(x: i64) => x + {}", addend), input + addend)
        }
        _ => {
            // subtraction
            let subtrahend = emit.gen_i64_range(1, 10);
            (
                format!("(x: i64) => x - {}", subtrahend),
                input - subtrahend,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: generic reduce -- `([T], T, (T, T) -> T) -> T`
// ---------------------------------------------------------------------------

/// Generate a generic `reduce_<N>` function at module level and call it with
/// a small i64 array and an accumulator closure.
///
/// ```vole
/// func reduce_42918<T>(items: [T], init: T, f: (T, T) -> T) -> T {
///     var acc = init
///     for item in items {
///         acc = f(acc, item)
///     }
///     return acc
/// }
/// let result_42918 = reduce_42918([1, 2, 3, 4, 5], 0, (a: i64, b: i64) => a + b)
/// assert(result_42918 == 15)
/// ```
fn emit_reduce_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("reduce_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(items: [T], init: T, f: (T, T) -> T) -> T {{\n    var acc = init\n    for item in items {{\n        acc = f(acc, item)\n    }}\n    return acc\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Pick a reduce operation with known expected value
    let (array_literal, init_val, closure, expected) = pick_reduce_operation(emit);

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    let code = format!(
        "let {rn} = {fn_name}({array}, {init}, {closure})\n{indent}assert({rn} == {expected})",
        rn = result_name,
        fn_name = fn_name,
        array = array_literal,
        init = init_val,
        closure = closure,
        expected = expected,
        indent = indent,
    );

    Some(code)
}

/// Pick a reduce operation (array, init, closure, expected result).
fn pick_reduce_operation(emit: &mut Emit) -> (String, i64, String, i64) {
    let op = emit.gen_range(0..3);
    match op {
        0 => {
            // sum: [1, 2, 3, 4, 5], init=0, a + b => 15
            let len = emit.gen_range(3..6);
            let elems: Vec<i64> = (1..=len as i64).collect();
            let expected: i64 = elems.iter().sum();
            let array_str = format!(
                "[{}]",
                elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            (
                array_str,
                0,
                "(a: i64, b: i64) => a + b".to_string(),
                expected,
            )
        }
        1 => {
            // product: [1, 2, 3, 4], init=1, a * b => 24
            let len = emit.gen_range(3..5);
            let elems: Vec<i64> = (1..=len as i64).collect();
            let expected: i64 = elems.iter().product();
            let array_str = format!(
                "[{}]",
                elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            (
                array_str,
                1,
                "(a: i64, b: i64) => a * b".to_string(),
                expected,
            )
        }
        _ => {
            // sum of small values: [10, 20, 30], init=0 => 60
            let count = emit.gen_range(2..5);
            let step = emit.gen_i64_range(5, 15);
            let elems: Vec<i64> = (1..=count as i64).map(|i| i * step).collect();
            let expected: i64 = elems.iter().sum();
            let array_str = format!(
                "[{}]",
                elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            (
                array_str,
                0,
                "(a: i64, b: i64) => a + b".to_string(),
                expected,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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
        assert_eq!(GenericClosureParam.name(), "generic_closure_param");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!GenericClosureParam.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericClosureParam.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericClosureParam.precondition(&scope, &params));
    }

    #[test]
    fn generates_apply_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureParam.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for apply variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("f: (T) -> T"),
                        "expected closure param in decl: {decl}"
                    );
                    assert!(decl.contains("return f(x)"), "expected apply body: {decl}");
                    // Inline code should have assert
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Inline code should have typed closure
                    assert!(
                        text.contains("(x: i64) =>"),
                        "expected typed closure in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated apply variant in 100 seeds");
    }

    #[test]
    fn generates_reduce_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureParam.generate(&mut scope, &mut emit, &params) {
                if text.contains("reduce_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for reduce variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("items: [T]"),
                        "expected array param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("f: (T, T) -> T"),
                        "expected closure param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("var acc = init"),
                        "expected accumulator in decl: {decl}"
                    );
                    // Inline code should have assert
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Inline code should have typed closure params
                    assert!(
                        text.contains("(a: i64, b: i64) =>"),
                        "expected typed closure in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated reduce variant in 100 seeds");
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericClosureParam.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        // Verify at least one local was added
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
        // Result type should be i64
        let result_local = scope.locals.last().expect("should add result local");
        assert_eq!(
            result_local.1,
            TypeInfo::Primitive(PrimitiveType::I64),
            "result type must be i64"
        );
    }

    #[test]
    fn result_names_use_uid() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        if let Some(text) = GenericClosureParam.generate(&mut scope, &mut emit, &params) {
            // Result name should match `result_NNNNN` pattern
            assert!(
                text.contains("result_"),
                "expected result_ prefix in code: {text}"
            );
        }
    }
}
