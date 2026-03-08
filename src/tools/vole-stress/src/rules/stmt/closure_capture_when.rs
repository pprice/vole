//! Rule: closures that capture outer variables and use `when` expressions.
//!
//! Exercises the interaction between closure captures and conditional codegen.
//!
//! **Variant 1 -- capture + when in iterator map:**
//! ```vole
//! let threshold = 5
//! let items = [1, 10, 3, 8]
//! let result = items.iter().map((x: i64) => when {
//!     x > threshold => "big"
//!     _ => "small"
//! }).collect()
//! ```
//!
//! **Variant 2 -- capture + string interpolation:**
//! ```vole
//! let prefix = "item"
//! let formatter = (n: i64) -> string => "{prefix}:{n}"
//! let result = formatter(42)
//! assert(result == "item:42")
//! ```
//!
//! **Variant 3 -- capture + conditional arithmetic:**
//! ```vole
//! let threshold = 5
//! let calc = (x: i64) -> i64 => when {
//!     x > threshold => x * 2
//!     _ => x + threshold
//! }
//! assert(calc(10) == 20)
//! assert(calc(3) == 8)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureCaptureWhen;

impl StmtRule for ClosureCaptureWhen {
    fn name(&self) -> &'static str {
        "closure_capture_when"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_capture_when_iter_map(scope, emit),
            1 => emit_capture_string_interpolation(scope, emit),
            _ => emit_capture_conditional_arithmetic(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1 -- capture + when in iterator map
// ---------------------------------------------------------------------------

fn emit_capture_when_iter_map(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    // Create the threshold variable (captured by closure)
    let threshold_name = scope.fresh_name();
    let threshold_val = emit.gen_i64_range(3, 8);

    // Create a small array literal
    let arr_name = scope.fresh_name();
    let arr_len = emit.random_in(3, 5);
    let arr_elems: Vec<i64> = (0..arr_len).map(|_| emit.gen_i64_range(1, 15)).collect();
    let arr_literal = format!(
        "[{}]",
        arr_elems
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );

    // Pick label pairs for the when arms
    let label_pairs = [("big", "small"), ("high", "low"), ("above", "below")];
    let (true_label, false_label) = label_pairs[emit.gen_range(0..label_pairs.len())];

    // Build the map + when expression
    let result_name = scope.fresh_name();

    let code = format!(
        "let {} = {}\n\
         {}let {} = {}\n\
         {}let {} = {}.iter().map((x: i64) => when {{\n\
         {}x > {} => \"{}\"\n\
         {}_ => \"{}\"\n\
         {}}}).collect()",
        threshold_name,
        threshold_val,
        indent,
        arr_name,
        arr_literal,
        indent,
        result_name,
        arr_name,
        inner_indent,
        threshold_name,
        true_label,
        inner_indent,
        false_label,
        indent,
    );

    // Register variables in scope
    scope.add_local(
        threshold_name,
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    scope.add_local(
        arr_name,
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );
    scope.add_local(
        result_name,
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2 -- capture + string interpolation
// ---------------------------------------------------------------------------

fn emit_capture_string_interpolation(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let indent = emit.indent_str();

    // Create the prefix variable (captured by closure)
    let prefix_name = scope.fresh_name();
    let prefix_choices = ["item", "key", "row", "tag", "rec"];
    let prefix_val = prefix_choices[emit.gen_range(0..prefix_choices.len())];

    // Create the closure
    let closure_name = scope.fresh_name();

    // Pick a test argument
    let test_arg = emit.gen_i64_range(1, 99);
    let expected = format!("{}:{}", prefix_val, test_arg);

    // Build the result binding + assertion
    let result_name = scope.fresh_name();

    let code = format!(
        "let {} = \"{}\"\n\
         {}let {} = (n: i64) -> string => \"{{{}}}:{{n}}\"\n\
         {}let {} = {}({})\n\
         {}assert({} == \"{}\")",
        prefix_name,
        prefix_val,
        indent,
        closure_name,
        prefix_name,
        indent,
        result_name,
        closure_name,
        test_arg,
        indent,
        result_name,
        expected,
    );

    // Register variables in scope
    scope.add_local(
        prefix_name,
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
        },
        false,
    );
    scope.add_local(
        result_name,
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 3 -- capture + conditional arithmetic
// ---------------------------------------------------------------------------

fn emit_capture_conditional_arithmetic(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    // Create the captured threshold variable
    let threshold_name = scope.fresh_name();
    let threshold_val = emit.gen_i64_range(3, 12);

    // Create the closure with a when expression
    let closure_name = scope.fresh_name();

    // Pick operations for the two branches
    let (true_op, true_compute): (&str, Box<dyn Fn(i64) -> i64>) = match emit.gen_range(0..3) {
        0 => ("x * 2", Box::new(|x: i64| x * 2)),
        1 => ("x * 3", Box::new(|x: i64| x * 3)),
        _ => ("x * 2 + 1", Box::new(|x: i64| x * 2 + 1)),
    };

    let threshold_for_false = threshold_val;
    let (false_op, false_compute): (String, Box<dyn Fn(i64) -> i64>) = match emit.gen_range(0..2) {
        0 => (
            format!("x + {}", threshold_name),
            Box::new(move |x: i64| x + threshold_for_false),
        ),
        _ => (
            format!("{} - x", threshold_name),
            Box::new(move |x: i64| threshold_for_false - x),
        ),
    };

    let code = format!(
        "let {} = {}\n\
         {}let {} = (x: i64) -> i64 => when {{\n\
         {}x > {} => {}\n\
         {}_ => {}\n\
         {}}}",
        threshold_name,
        threshold_val,
        indent,
        closure_name,
        inner_indent,
        threshold_name,
        true_op,
        inner_indent,
        false_op,
        indent,
    );

    // Pick test values: one above threshold, one at or below
    let high_test = threshold_val + emit.gen_i64_range(1, 10);
    let low_test = emit.gen_i64_range(0, threshold_val);

    let expected_high = true_compute(high_test);
    let expected_low = false_compute(low_test);

    let assert_high = format!(
        "assert({}({}) == {})",
        closure_name, high_test, expected_high
    );
    let assert_low = format!("assert({}({}) == {})", closure_name, low_test, expected_low);

    // Register variables in scope
    scope.add_local(
        threshold_name,
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
        },
        false,
    );

    Some(format!(
        "{}\n{}{}\n{}{}",
        code, indent, assert_high, indent, assert_low,
    ))
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ClosureCaptureWhen.name(), "closure_capture_when");
    }

    #[test]
    fn generates_iter_map_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureCaptureWhen
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains(".iter().map(") {
                assert!(
                    text.contains("when {"),
                    "expected when expression, got: {text}"
                );
                assert!(
                    text.contains(".collect()"),
                    "expected .collect(), got: {text}"
                );
                assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
                found = true;
                break;
            }
        }
        assert!(found, "never generated iter map variant in 100 seeds");
    }

    #[test]
    fn generates_string_interpolation_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureCaptureWhen
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains("-> string =>") && text.contains("assert(") {
                assert!(
                    text.contains("{n}"),
                    "expected interpolation with n, got: {text}"
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "never generated string interpolation variant in 100 seeds"
        );
    }

    #[test]
    fn generates_conditional_arithmetic_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureCaptureWhen
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains("-> i64 => when {") {
                assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
                let assert_count = text.matches("assert(").count();
                assert_eq!(
                    assert_count, 2,
                    "expected 2 assertions for arithmetic variant, got {assert_count}: {text}"
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "never generated conditional arithmetic variant in 100 seeds"
        );
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_iter = false;
        let mut found_interp = false;
        let mut found_arith = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureCaptureWhen
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains(".iter().map(") {
                found_iter = true;
            } else if text.contains("-> string =>") && !text.contains("when {") {
                found_interp = true;
            } else if text.contains("-> i64 => when {") {
                found_arith = true;
            }

            if found_iter && found_interp && found_arith {
                break;
            }
        }

        assert!(found_iter, "never generated iter map variant in 200 seeds");
        assert!(
            found_interp,
            "never generated string interpolation variant in 200 seeds"
        );
        assert!(
            found_arith,
            "never generated conditional arithmetic variant in 200 seeds"
        );
    }

    #[test]
    fn adds_locals_to_scope() {
        let table = SymbolTable::new();
        for seed in 0..30 {
            let mut scope = Scope::new(&[], &table);
            let initial_len = scope.locals.len();
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            ClosureCaptureWhen.generate(&mut scope, &mut emit, &test_params());
            // All variants add at least 2 locals.
            assert!(
                scope.locals.len() >= initial_len + 2,
                "seed {seed}: expected at least 2 new locals, got {} (started with {})",
                scope.locals.len(),
                initial_len,
            );
        }
    }

    #[test]
    fn iter_map_captures_threshold_variable() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureCaptureWhen
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains(".iter().map(") {
                // The when condition should reference the captured threshold
                // variable (a local name), not a literal number.
                assert!(
                    text.contains("x > local"),
                    "expected captured variable reference in when condition, got: {text}"
                );
                found = true;
                break;
            }
        }
        assert!(found, "never generated iter map variant in 100 seeds");
    }
}
