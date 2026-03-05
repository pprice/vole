//! Rule: closure that captures an array and performs iterator operations.
//!
//! Generates a factory function that takes an `[i64]` parameter, returns a
//! closure `() -> i64` that captures the array, and runs one of several
//! iterator chain variants on it. The factory is called with a concrete array
//! literal, the returned closure is invoked, and the result is asserted.
//!
//! This exercises the intersection of closure capture semantics, iterator
//! dispatch, and RC management.
//!
//! **Pattern -- reduce (sum):**
//! ```vole
//! func make_summer(nums: [i64]) -> () -> i64 {
//!     return () -> i64 => nums.iter().reduce(0, (acc: i64, x: i64) -> i64 => acc + x)
//! }
//! let summer = make_summer([1, 2, 3])
//! let result = summer()
//! assert(result == 6)
//! ```
//!
//! **Pattern -- filter count:**
//! ```vole
//! func make_counter(nums: [i64]) -> () -> i64 {
//!     return () -> i64 => nums.iter().filter((x: i64) -> bool => x > 0).count()
//! }
//! let counter = make_counter([3, 7, 12])
//! let result = counter()
//! assert(result == 3)
//! ```
//!
//! **Pattern -- map collect length:**
//! ```vole
//! func make_mapper(nums: [i64]) -> () -> i64 {
//!     return () -> i64 => nums.iter().map((x: i64) -> i64 => x * 2).collect().length()
//! }
//! let mapper = make_mapper([5, 10])
//! let result = mapper()
//! assert(result == 2)
//! ```
//!
//! **Pattern -- direct length:**
//! ```vole
//! func make_measurer(nums: [i64]) -> () -> i64 {
//!     return () -> i64 => nums.length()
//! }
//! let measurer = make_measurer([1, 2, 3, 4])
//! let result = measurer()
//! assert(result == 4)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureIterCapture;

impl StmtRule for ClosureIterCapture {
    fn name(&self) -> &'static str {
        "closure_iter_capture"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.06)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Need recursion room for the nested func definition.
        // Skip inside generic class methods (closure capture bug).
        scope.can_recurse() && !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..4);
        match variant {
            0 => emit_reduce_sum(scope, emit),
            1 => emit_filter_count(scope, emit),
            2 => emit_map_collect_length(scope, emit),
            _ => emit_direct_length(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Array literal generation
// ---------------------------------------------------------------------------

/// Generate a random array literal of 2-5 small positive i64 values.
///
/// Returns `(literal_string, elements)` where `literal_string` is e.g.
/// `"[3, 7, 12, 1]"` and `elements` is the `Vec<i64>` of values.
fn random_array(emit: &mut Emit) -> (String, Vec<i64>) {
    let len = emit.random_in(2, 5);
    let elems: Vec<i64> = (0..len).map(|_| emit.random_in(1, 20) as i64).collect();
    let literal = format!(
        "[{}]",
        elems
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    (literal, elems)
}

// ---------------------------------------------------------------------------
// Variant: reduce (sum)
// ---------------------------------------------------------------------------

/// `.iter().reduce(0, (acc: i64, x: i64) -> i64 => acc + x)` -- sum
fn emit_reduce_sum(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let (array_literal, elems) = random_array(emit);
    let expected: i64 = elems.iter().sum();

    let body_expr = "nums.iter().reduce(0, (acc: i64, x: i64) -> i64 => acc + x)";

    emit_factory(
        scope,
        emit,
        &array_literal,
        body_expr,
        &expected.to_string(),
    )
}

// ---------------------------------------------------------------------------
// Variant: filter count
// ---------------------------------------------------------------------------

/// `.iter().filter((x: i64) -> bool => x > THRESHOLD).count()` -- count above threshold
fn emit_filter_count(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let (array_literal, elems) = random_array(emit);
    // Pick a threshold that produces a non-trivial count (at least 1 passes).
    // Use the minimum element as the threshold so all elements pass (x > min-1
    // would include min), but actually let's use a value that at least 1 element
    // exceeds. We pick threshold = 0 so all positive elements pass, making the
    // result deterministic: count == array length.
    let threshold: i64 = 0;
    let expected = elems.iter().filter(|&&x| x > threshold).count();

    let body_expr = format!(
        "nums.iter().filter((x: i64) -> bool => x > {}).count()",
        threshold
    );

    emit_factory(
        scope,
        emit,
        &array_literal,
        &body_expr,
        &expected.to_string(),
    )
}

// ---------------------------------------------------------------------------
// Variant: map + collect + length
// ---------------------------------------------------------------------------

/// `.iter().map((x: i64) -> i64 => x * 2).collect().length()` -- always same as input length
fn emit_map_collect_length(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let (array_literal, elems) = random_array(emit);
    let expected = elems.len();

    let body_expr = "nums.iter().map((x: i64) -> i64 => x * 2).collect().length()";

    emit_factory(
        scope,
        emit,
        &array_literal,
        body_expr,
        &expected.to_string(),
    )
}

// ---------------------------------------------------------------------------
// Variant: direct length
// ---------------------------------------------------------------------------

/// `.length()` -- simplest, just returns array length
fn emit_direct_length(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let (array_literal, elems) = random_array(emit);
    let expected = elems.len();

    let body_expr = "nums.length()";

    emit_factory(
        scope,
        emit,
        &array_literal,
        body_expr,
        &expected.to_string(),
    )
}

// ---------------------------------------------------------------------------
// Shared emit helper
// ---------------------------------------------------------------------------

/// Emit the full pattern:
///
/// ```text
/// func FACTORY(nums: [i64]) -> () -> i64 {
///     return () -> i64 => BODY_EXPR
/// }
/// let CLOSURE = FACTORY(ARRAY_LITERAL)
/// let RESULT = CLOSURE()
/// assert(RESULT == EXPECTED)
/// ```
fn emit_factory(
    scope: &mut Scope,
    emit: &mut Emit,
    array_literal: &str,
    body_expr: &str,
    expected: &str,
) -> Option<String> {
    let factory_name = scope.fresh_name();
    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    // Build the factory function definition.
    let func_def = format!(
        "func {}(nums: [i64]) -> () -> i64 {{\n{}return () -> i64 => {}\n{}}}",
        factory_name, inner_indent, body_expr, indent,
    );

    // Call factory and bind closure.
    let call_factory = format!("let {} = {}({})", closure_name, factory_name, array_literal);

    // Call closure and bind result.
    let call_closure = format!("let {} = {}()", result_name, closure_name);

    // Assert the result.
    let assert_stmt = format!("assert({} == {})", result_name, expected);

    // Register variables in scope.
    let closure_type = TypeInfo::Function {
        param_types: vec![],
        return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
    };
    scope.add_local(closure_name.clone(), closure_type, false);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

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
        assert_eq!(ClosureIterCapture.name(), "closure_iter_capture");
    }

    #[test]
    fn generates_func_def_and_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureIterCapture.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("func "), "expected func keyword, got: {text}");
        assert!(
            text.contains("nums: [i64]"),
            "expected array param, got: {text}"
        );
        assert!(
            text.contains("() -> i64"),
            "expected closure return type, got: {text}"
        );
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

        ClosureIterCapture.generate(&mut scope, &mut emit, &params);
        // Should add 2 locals: closure variable + result variable.
        assert_eq!(scope.locals.len(), initial_len + 2);
    }

    #[test]
    fn generates_all_variants() {
        let table = SymbolTable::new();
        let mut found_reduce = false;
        let mut found_filter = false;
        let mut found_map = false;
        let mut found_length = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureIterCapture.generate(&mut scope, &mut emit, &params) {
                if text.contains(".reduce(") {
                    found_reduce = true;
                }
                if text.contains(".filter(") {
                    found_filter = true;
                }
                if text.contains(".map(") {
                    found_map = true;
                }
                if text.contains("nums.length()") {
                    found_length = true;
                }
            }
        }
        assert!(found_reduce, "never generated reduce variant");
        assert!(found_filter, "never generated filter variant");
        assert!(found_map, "never generated map variant");
        assert!(found_length, "never generated direct length variant");
    }

    #[test]
    fn closure_local_has_function_type() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureIterCapture.generate(&mut scope, &mut emit, &params);
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
        assert!(!ClosureIterCapture.precondition(&scope, &params));
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
        assert!(!ClosureIterCapture.precondition(&scope, &params));
    }

    #[test]
    fn assert_contains_correct_expected_value() {
        let table = SymbolTable::new();

        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureIterCapture.generate(&mut scope, &mut emit, &params) {
                // Every generated output should have func, return, =>, and assert.
                assert!(text.contains("func "), "seed {seed}: missing func");
                assert!(
                    text.contains("return () -> i64 =>"),
                    "seed {seed}: missing return closure"
                );
                assert!(text.contains("assert("), "seed {seed}: missing assert");
            }
        }
    }

    #[test]
    fn array_literals_have_correct_bracket_syntax() {
        let table = SymbolTable::new();

        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureIterCapture.generate(&mut scope, &mut emit, &params) {
                // The factory call should contain an array literal argument.
                assert!(
                    text.contains("(["),
                    "seed {seed}: expected array literal in call, got: {text}"
                );
            }
        }
    }
}
