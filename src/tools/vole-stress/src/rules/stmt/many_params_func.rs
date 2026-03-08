//! Rule: module-level functions with many parameters (8-12) to stress calling
//! conventions and register allocation.
//!
//! Generates functions whose parameter counts exceed the number of
//! register-passed arguments, forcing some parameters onto the stack.
//! Each variant computes a deterministic result from its parameters and
//! asserts correctness at the call site.
//!
//! Three variants:
//!
//! **Variant 0 -- 8-param sum:**
//! ```vole
//! func mpf_local0(p0: i64, p1: i64, p2: i64, p3: i64, p4: i64, p5: i64, p6: i64, p7: i64) -> i64 {
//!     return p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7
//! }
//! assert(mpf_local0(1, 2, 3, 4, 5, 6, 7, 8) == 36)
//! ```
//!
//! **Variant 1 -- 10-param arithmetic (sum of first 5 + product of next 2 + sum of last 3):**
//! ```vole
//! func mpf_local0(p0: i64, p1: i64, p2: i64, p3: i64, p4: i64, p5: i64, p6: i64, p7: i64, p8: i64, p9: i64) -> i64 {
//!     return p0 + p1 + p2 + p3 + p4 + p5 * p6 + p7 + p8 + p9
//! }
//! assert(mpf_local0(1, 2, 3, 4, 5, 6, 7, 8, 9, 1) == 60)
//! ```
//!
//! **Variant 2 -- 12-param chain (p0 + p1*p2 - p3 + p4*p5 - p6 + p7*p8 - p9 + p10*p11):**
//! ```vole
//! func mpf_local0(p0: i64, ..., p11: i64) -> i64 {
//!     return p0 + p1 * p2 - p3 + p4 * p5 - p6 + p7 * p8 - p9 + p10 * p11
//! }
//! assert(mpf_local0(1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3) == 40)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct ManyParamsFunc;

impl StmtRule for ManyParamsFunc {
    fn name(&self) -> &'static str {
        "many_params_func"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_8_param_sum(scope, emit),
            1 => emit_10_param_arithmetic(scope, emit),
            _ => emit_12_param_chain(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build the parameter signature: "p0: i64, p1: i64, ..."
fn param_sig(count: usize) -> String {
    (0..count)
        .map(|i| format!("p{}: i64", i))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Generate `count` small positive argument values (1-9).
fn gen_args(emit: &mut Emit, count: usize) -> Vec<i64> {
    (0..count).map(|_| emit.gen_i64_range(1, 9)).collect()
}

/// Format arguments as a comma-separated string.
fn args_str(args: &[i64]) -> String {
    args.iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

// ---------------------------------------------------------------------------
// Variant 0 -- 8-param sum
// ---------------------------------------------------------------------------

fn emit_8_param_sum(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("mpf_{}", fn_name);

    let body_expr = (0..8)
        .map(|i| format!("p{}", i))
        .collect::<Vec<_>>()
        .join(" + ");

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_label,
        param_sig(8),
        body_expr,
    );
    scope.add_module_decl(decl);

    let args = gen_args(emit, 8);
    let expected: i64 = args.iter().sum();

    Some(format!(
        "assert({}({}) == {})",
        fn_label,
        args_str(&args),
        expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- 10-param arithmetic
// sum of first 5 + (p5 * p6) + sum of last 3
// body: p0 + p1 + p2 + p3 + p4 + p5 * p6 + p7 + p8 + p9
// ---------------------------------------------------------------------------

fn emit_10_param_arithmetic(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("mpf_{}", fn_name);

    // p0 + p1 + p2 + p3 + p4 + p5 * p6 + p7 + p8 + p9
    let body_expr = "p0 + p1 + p2 + p3 + p4 + p5 * p6 + p7 + p8 + p9";

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_label,
        param_sig(10),
        body_expr,
    );
    scope.add_module_decl(decl);

    let args = gen_args(emit, 10);
    // Compute expected: sum of first 5 + (p5 * p6) + sum of last 3
    let expected: i64 = args[0]
        + args[1]
        + args[2]
        + args[3]
        + args[4]
        + args[5] * args[6]
        + args[7]
        + args[8]
        + args[9];

    Some(format!(
        "assert({}({}) == {})",
        fn_label,
        args_str(&args),
        expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- 12-param chain
// p0 + p1*p2 - p3 + p4*p5 - p6 + p7*p8 - p9 + p10*p11
// ---------------------------------------------------------------------------

fn emit_12_param_chain(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("mpf_{}", fn_name);

    let body_expr = "p0 + p1 * p2 - p3 + p4 * p5 - p6 + p7 * p8 - p9 + p10 * p11";

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_label,
        param_sig(12),
        body_expr,
    );
    scope.add_module_decl(decl);

    let args = gen_args(emit, 12);
    // Compute expected: p0 + p1*p2 - p3 + p4*p5 - p6 + p7*p8 - p9 + p10*p11
    let expected: i64 = args[0] + args[1] * args[2] - args[3] + args[4] * args[5] - args[6]
        + args[7] * args[8]
        - args[9]
        + args[10] * args[11];

    Some(format!(
        "assert({}({}) == {})",
        fn_label,
        args_str(&args),
        expected,
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
        assert_eq!(ManyParamsFunc.name(), "many_params_func");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!ManyParamsFunc.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ManyParamsFunc.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyParamsFunc.precondition(&scope, &params));
    }

    #[test]
    fn generates_8_param_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamsFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                // 8-param variant has exactly 8 i64 params (not 10 or 12)
                let param_count = decl.matches(": i64").count();
                if param_count == 8 {
                    found = true;
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7"),
                        "expected sum body in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated 8-param variant in 100 seeds");
    }

    #[test]
    fn generates_10_param_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamsFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                let param_count = decl.matches(": i64").count();
                if param_count == 10 {
                    found = true;
                    assert!(
                        decl.contains("p5 * p6"),
                        "expected multiplication in 10-param body: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated 10-param variant in 100 seeds");
    }

    #[test]
    fn generates_12_param_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamsFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                let param_count = decl.matches(": i64").count();
                if param_count == 12 {
                    found = true;
                    assert!(
                        decl.contains("p1 * p2"),
                        "expected p1*p2 in 12-param body: {decl}"
                    );
                    assert!(
                        decl.contains("p10 * p11"),
                        "expected p10*p11 in 12-param body: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated 12-param variant in 100 seeds");
    }

    #[test]
    fn assert_checks_correct_result() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamsFunc.generate(&mut scope, &mut emit, &test_params()) {
                // Format: assert(mpf_localN(a1, a2, ...) == EXPECTED)
                // Find the inner function call's opening paren (second '(' in the string).
                let first_open = text.find('(').unwrap();
                let inner_open = text[first_open + 1..].find('(').unwrap() + first_open + 1;
                let args_start = inner_open + 1;

                // Find ") ==" to delimit the end of args.
                let args_end_marker = text.find(") ==").unwrap();
                let args_str = &text[args_start..args_end_marker];
                let args: Vec<i64> = args_str
                    .split(", ")
                    .map(|s| s.trim().parse::<i64>().unwrap())
                    .collect();

                // Parse the expected value after "== " and before the final ")".
                let eq_pos = text.find("== ").unwrap();
                let close_pos = text.rfind(')').unwrap();
                let expected_str = &text[eq_pos + 3..close_pos];
                let expected: i64 = expected_str
                    .parse()
                    .unwrap_or_else(|_| panic!("failed to parse expected from: {text}"));

                // Determine variant from arg count and recompute expected.
                let decl = &scope.module_decls[0];
                let computed = if args.len() == 8 {
                    args.iter().sum::<i64>()
                } else if args.len() == 10 {
                    args[0]
                        + args[1]
                        + args[2]
                        + args[3]
                        + args[4]
                        + args[5] * args[6]
                        + args[7]
                        + args[8]
                        + args[9]
                } else if args.len() == 12 {
                    args[0] + args[1] * args[2] - args[3] + args[4] * args[5] - args[6]
                        + args[7] * args[8]
                        - args[9]
                        + args[10] * args[11]
                } else {
                    panic!("unexpected arg count {} in: {text}", args.len());
                };

                assert_eq!(
                    computed, expected,
                    "assert result mismatch for seed {seed}: {text} (decl: {decl})"
                );
            }
        }
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        ManyParamsFunc.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn does_not_add_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = ManyParamsFunc.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            scope.locals.is_empty(),
            "many_params_func should not add locals to scope"
        );
    }

    #[test]
    fn exercises_all_three_variants() {
        let table = SymbolTable::new();
        let mut saw_8 = false;
        let mut saw_10 = false;
        let mut saw_12 = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(_text) = ManyParamsFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                let param_count = decl.matches(": i64").count();
                match param_count {
                    8 => saw_8 = true,
                    10 => saw_10 = true,
                    12 => saw_12 = true,
                    _ => {}
                }
            }

            if saw_8 && saw_10 && saw_12 {
                break;
            }
        }

        assert!(saw_8, "never generated 8-param variant in 200 seeds");
        assert!(saw_10, "never generated 10-param variant in 200 seeds");
        assert!(saw_12, "never generated 12-param variant in 200 seeds");
    }
}
