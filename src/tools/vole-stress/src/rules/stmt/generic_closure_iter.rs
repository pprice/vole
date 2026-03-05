//! Rule: nested function that takes an array and a closure, iterates applying the closure.
//!
//! Combines closure parameters + iteration + nested function definitions.
//! Three variants:
//!
//! **apply_all**: concatenates `f(item)` results via for-loop.
//! ```vole
//! func apply_all_0(arr: [i64], f: (i64) -> string) -> string {
//!     var result = ""
//!     for item in arr {
//!         result = result + f(item)
//!     }
//!     return result
//! }
//! let local0 = apply_all_0([1, 2, 3], (x: i64) => "{x}")
//! ```
//!
//! **sum_via**: sums via `.iter().map().reduce()`.
//! ```vole
//! func sum_via_0(arr: [string], to_num: (string) -> i64) -> i64 {
//!     return arr.iter().map((x: string) => to_num(x)).reduce(0, (acc, x) => acc + x)
//! }
//! let local0 = sum_via_0(["hi", "there"], (s: string) => s.length())
//! ```
//!
//! **count_matching**: counts via `.iter().filter().count()`.
//! ```vole
//! func count_matching_0(arr: [i64], pred: (i64) -> bool) -> i64 {
//!     return arr.iter().filter((x: i64) => pred(x)).count()
//! }
//! let local0 = count_matching_0([1, 5, 3], (x: i64) => x > 2)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericClosureIter;

impl StmtRule for GenericClosureIter {
    fn name(&self) -> &'static str {
        "generic_closure_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        let fn_name = scope.fresh_name();
        let result_name = scope.fresh_name();
        let indent = emit.indent_str();

        let (fn_def, call_expr, result_type) = match variant {
            0 => gen_apply_all(&fn_name, emit, &indent),
            1 => gen_sum_via(&fn_name, emit, &indent),
            _ => gen_count_matching(&fn_name, emit, &indent),
        };

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "{}\n{}let {} = {}",
            fn_def, indent, result_name, call_expr
        ))
    }
}

/// Variant 1: `apply_all` -- for-loop applying closure and concatenating strings.
fn gen_apply_all(fn_name: &str, emit: &mut Emit, indent: &str) -> (String, String, TypeInfo) {
    let body_indent = format!("{}    ", indent);
    let inner_indent = format!("{}        ", indent);

    let arr = gen_i64_array(emit);

    let fn_def = format!(
        "{}func {}(arr: [i64], f: (i64) -> string) -> string {{\n\
         {}var result = \"\"\n\
         {}for item in arr {{\n\
         {}result = result + f(item)\n\
         {}}}\n\
         {}return result\n\
         {}}}",
        indent, fn_name, body_indent, body_indent, inner_indent, body_indent, body_indent, indent,
    );

    let call_expr = format!("{}({}, (x: i64) => \"{{x}}\")", fn_name, arr);

    (
        fn_def,
        call_expr,
        TypeInfo::Primitive(PrimitiveType::String),
    )
}

/// Variant 2: `sum_via` -- `.iter().map().reduce()` with closure.
fn gen_sum_via(fn_name: &str, emit: &mut Emit, indent: &str) -> (String, String, TypeInfo) {
    let body_indent = format!("{}    ", indent);

    let arr = gen_string_array(emit);

    let fn_def = format!(
        "{}func {}(arr: [string], to_num: (string) -> i64) -> i64 {{\n\
         {}return arr.iter().map((x: string) => to_num(x)).reduce(0, (acc, x) => acc + x)\n\
         {}}}",
        indent, fn_name, body_indent, indent,
    );

    let call_expr = format!("{}({}, (s: string) => s.length())", fn_name, arr);

    (fn_def, call_expr, TypeInfo::Primitive(PrimitiveType::I64))
}

/// Variant 3: `count_matching` -- `.iter().filter().count()` with predicate.
fn gen_count_matching(fn_name: &str, emit: &mut Emit, indent: &str) -> (String, String, TypeInfo) {
    let body_indent = format!("{}    ", indent);

    let arr = gen_i64_array(emit);
    let threshold = emit.gen_i64_range(1, 10);

    let fn_def = format!(
        "{}func {}(arr: [i64], pred: (i64) -> bool) -> i64 {{\n\
         {}return arr.iter().filter((x: i64) => pred(x)).count()\n\
         {}}}",
        indent, fn_name, body_indent, indent,
    );

    let call_expr = format!("{}({}, (x: i64) => x > {})", fn_name, arr, threshold);

    (fn_def, call_expr, TypeInfo::Primitive(PrimitiveType::I64))
}

/// Generate an i64 array literal with 2-4 elements.
fn gen_i64_array(emit: &mut Emit) -> String {
    let len = emit.random_in(2, 4);
    let elems: Vec<String> = (0..len)
        .map(|_| emit.gen_i64_range(1, 20).to_string())
        .collect();
    format!("[{}]", elems.join(", "))
}

/// Generate a string array literal with 2-3 elements.
fn gen_string_array(emit: &mut Emit) -> String {
    let words = ["hi", "there", "hello", "world", "foo", "bar", "test"];
    let len = emit.random_in(2, 3);
    let elems: Vec<String> = (0..len)
        .map(|_| {
            let idx = emit.gen_range(0..words.len());
            format!("\"{}\"", words[idx])
        })
        .collect();
    format!("[{}]", elems.join(", "))
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
        assert_eq!(GenericClosureIter.name(), "generic_closure_iter");
    }

    #[test]
    fn generates_func_and_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericClosureIter.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("func "), "expected func keyword, got: {text}");
        assert!(
            text.contains("let local1 = local0("),
            "expected call, got: {text}"
        );
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_apply_all = false;
        let mut found_sum_via = false;
        let mut found_count_matching = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureIter.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("f: (i64) -> string") {
                    found_apply_all = true;
                }
                if text.contains("to_num: (string) -> i64") {
                    found_sum_via = true;
                }
                if text.contains("pred: (i64) -> bool") {
                    found_count_matching = true;
                }
            }
        }
        assert!(found_apply_all, "never generated apply_all variant");
        assert!(found_sum_via, "never generated sum_via variant");
        assert!(
            found_count_matching,
            "never generated count_matching variant"
        );
    }

    #[test]
    fn adds_result_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        GenericClosureIter.generate(&mut scope, &mut emit, &rule_params);
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!GenericClosureIter.precondition(&scope, &params));
    }

    #[test]
    fn apply_all_has_explicit_type_annotation() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureIter.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("f: (i64) -> string") {
                    assert!(
                        text.contains("(x: i64) =>"),
                        "lambda must have explicit type annotation, got: {text}"
                    );
                    return;
                }
            }
        }
        panic!("never generated apply_all variant");
    }

    #[test]
    fn sum_via_has_explicit_type_annotation() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureIter.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("to_num: (string) -> i64") {
                    assert!(
                        text.contains("(s: string) =>"),
                        "lambda must have explicit type annotation, got: {text}"
                    );
                    return;
                }
            }
        }
        panic!("never generated sum_via variant");
    }

    #[test]
    fn count_matching_has_explicit_type_annotation() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureIter.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("pred: (i64) -> bool") {
                    assert!(
                        text.contains("(x: i64) =>"),
                        "lambda must have explicit type annotation, got: {text}"
                    );
                    return;
                }
            }
        }
        panic!("never generated count_matching variant");
    }
}
