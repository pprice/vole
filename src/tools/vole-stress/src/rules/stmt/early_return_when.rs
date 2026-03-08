//! Rule: module-level functions with early returns from loops and when expressions.
//!
//! Exercises control flow codegen -- return from within loops, and when
//! expressions as return values.
//!
//! Two variants:
//!
//! **Variant 0 -- when-return (~50%):**
//! ```vole
//! func classify_local0(x: i64) -> string {
//!     return when {
//!         x < 0 => "negative"
//!         x == 0 => "zero"
//!         _ => "positive"
//!     }
//! }
//! let local1 = classify_local0(-5)
//! assert(local1 == "negative")
//! ```
//!
//! **Variant 1 -- loop-early-return (~50%):**
//! ```vole
//! func first_positive_local0(arr: [i64]) -> i64 {
//!     for item in arr {
//!         if item > 0 {
//!             return item
//!         }
//!     }
//!     return -1
//! }
//! let local1 = first_positive_local0([0, -3, 7, 2])
//! assert(local1 == 7)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EarlyReturnWhen;

impl StmtRule for EarlyReturnWhen {
    fn name(&self) -> &'static str {
        "early_return_when"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if emit.gen_bool(0.5) {
            emit_when_return(scope, emit)
        } else {
            emit_loop_early_return(scope, emit)
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- when-return: classify an i64 via a when expression
// ---------------------------------------------------------------------------

/// Classification templates.  Each entry is:
///   (label_prefix, [(condition_expr, result_literal, test_input, expected_output), ...], wildcard_result)
///
/// The condition_expr uses `x` as the parameter name.
const CLASSIFY_TEMPLATES: &[ClassifyTemplate] = &[
    // positive / negative / zero
    ClassifyTemplate {
        label: "classify",
        arms: &[("x < 0", "negative"), ("x == 0", "zero")],
        wildcard: "positive",
        cases: &[(-5, "negative"), (0, "zero"), (7, "positive")],
    },
    // sign: small / medium / large (by absolute value)
    ClassifyTemplate {
        label: "size_of",
        arms: &[("x < 10", "small"), ("x < 100", "medium")],
        wildcard: "large",
        cases: &[(3, "small"), (42, "medium"), (999, "large")],
    },
    // even / odd
    ClassifyTemplate {
        label: "parity",
        arms: &[("x % 2 == 0", "even")],
        wildcard: "odd",
        cases: &[(4, "even"), (7, "odd")],
    },
    // range buckets
    ClassifyTemplate {
        label: "bucket",
        arms: &[("x <= 0", "non-positive"), ("x <= 50", "low")],
        wildcard: "high",
        cases: &[(-1, "non-positive"), (25, "low"), (100, "high")],
    },
];

struct ClassifyTemplate {
    label: &'static str,
    arms: &'static [(&'static str, &'static str)],
    wildcard: &'static str,
    cases: &'static [(i64, &'static str)],
}

fn emit_when_return(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let tmpl_idx = emit.gen_range(0..CLASSIFY_TEMPLATES.len());
    let tmpl = &CLASSIFY_TEMPLATES[tmpl_idx];

    let fn_name = scope.fresh_name();
    let fn_label = format!("{}_{}", tmpl.label, fn_name);

    // Build the when arms.
    let mut arm_lines = Vec::new();
    for &(cond, result) in tmpl.arms {
        arm_lines.push(format!("        {} => \"{}\"", cond, result));
    }
    arm_lines.push(format!("        _ => \"{}\"", tmpl.wildcard));

    let decl = format!(
        "func {}(x: i64) -> string {{\n    return when {{\n{}\n    }}\n}}",
        fn_label,
        arm_lines.join("\n"),
    );
    scope.add_module_decl(decl);

    // Pick a random test case from the template.
    let case_idx = emit.gen_range(0..tmpl.cases.len());
    let (input, expected) = tmpl.cases[case_idx];

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == \"{}\")",
        result_name, fn_label, input, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- loop-early-return: return early from a for loop
// ---------------------------------------------------------------------------

/// Loop-return templates.  Each entry is:
///   (label_prefix, condition_on_item, fallback_return, array_elements, expected_result)
const LOOP_TEMPLATES: &[LoopTemplate] = &[
    LoopTemplate {
        label: "first_positive",
        condition: "item > 0",
        fallback: "-1",
        arrays: &[
            (&[0, -3, 7, 2], "7"),
            (&[-1, -2, -3], "-1"),
            (&[5, 10, 15], "5"),
        ],
    },
    LoopTemplate {
        label: "first_even",
        condition: "item % 2 == 0",
        fallback: "-1",
        arrays: &[(&[1, 3, 4, 6], "4"), (&[1, 3, 5], "-1"), (&[2, 4, 6], "2")],
    },
    LoopTemplate {
        label: "first_over_ten",
        condition: "item > 10",
        fallback: "0",
        arrays: &[(&[1, 5, 12, 3], "12"), (&[1, 2, 3], "0"), (&[20, 30], "20")],
    },
    LoopTemplate {
        label: "first_negative",
        condition: "item < 0",
        fallback: "0",
        arrays: &[
            (&[3, 1, -2, 5], "-2"),
            (&[1, 2, 3], "0"),
            (&[-5, -1, 0], "-5"),
        ],
    },
];

struct LoopTemplate {
    label: &'static str,
    condition: &'static str,
    fallback: &'static str,
    arrays: &'static [(&'static [i64], &'static str)],
}

fn emit_loop_early_return(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let tmpl_idx = emit.gen_range(0..LOOP_TEMPLATES.len());
    let tmpl = &LOOP_TEMPLATES[tmpl_idx];

    let fn_name = scope.fresh_name();
    let fn_label = format!("{}_{}", tmpl.label, fn_name);

    let decl = format!(
        "func {}(arr: [i64]) -> i64 {{\n    for item in arr {{\n        if {} {{\n            return item\n        }}\n    }}\n    return {}\n}}",
        fn_label, tmpl.condition, tmpl.fallback,
    );
    scope.add_module_decl(decl);

    // Pick a random test case.
    let case_idx = emit.gen_range(0..tmpl.arrays.len());
    let (elems, expected) = tmpl.arrays[case_idx];

    let arr_str = format!(
        "[{}]",
        elems
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == {})",
        result_name, fn_label, arr_str, indent, result_name, expected,
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
        assert_eq!(EarlyReturnWhen.name(), "early_return_when");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!EarlyReturnWhen.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(EarlyReturnWhen.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!EarlyReturnWhen.precondition(&scope, &params));
    }

    #[test]
    fn generates_when_return_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = EarlyReturnWhen.generate(&mut scope, &mut emit, &test_params()) {
                // when-return variant produces string results with quoted expected values
                if text.contains("assert(") && text.contains("== \"") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for when-return variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return when {"),
                        "expected return when in decl: {decl}"
                    );
                    assert!(
                        decl.contains("_ =>"),
                        "expected wildcard arm in decl: {decl}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated when-return variant in 100 seeds");
    }

    #[test]
    fn generates_loop_early_return_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = EarlyReturnWhen.generate(&mut scope, &mut emit, &test_params()) {
                // loop-early-return variant has array literal in the call
                if text.contains("[") && text.contains("]") && !text.contains("== \"") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for loop-early-return variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("for item in arr"),
                        "expected for loop in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return item"),
                        "expected early return in decl: {decl}"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated loop-early-return variant in 100 seeds"
        );
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        EarlyReturnWhen.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = EarlyReturnWhen.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
        let result_local = scope.locals.last().expect("should add result local");
        // Result type depends on variant: String (when) or I64 (loop).
        assert!(
            result_local.1 == TypeInfo::Primitive(PrimitiveType::String)
                || result_local.1 == TypeInfo::Primitive(PrimitiveType::I64),
            "result must be string or i64, got: {:?}",
            result_local.1,
        );
    }
}
