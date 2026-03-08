//! Rule: module-level function with many i64 parameters (8 or 12) that sums
//! them all.
//!
//! The function is emitted as a module-level declaration via
//! [`Scope::add_module_decl`] so that the generated code stays in the correct
//! scope.  The call site asserts the sum equals the expected total.
//!
//! Two variants:
//!
//! **Variant 0 -- 8 i64 params:**
//! ```vole
//! func sum8_local0(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64 {
//!     return a + b + c + d + e + f + g + h
//! }
//! let local1 = sum8_local0(1, 2, 3, 4, 5, 6, 7, 8)
//! assert(local1 == 36)
//! ```
//!
//! **Variant 1 -- 12 i64 params:**
//! ```vole
//! func sum12_local0(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: i64, j: i64, k: i64, l: i64) -> i64 {
//!     return a + b + c + d + e + f + g + h + i + j + k + l
//! }
//! let local1 = sum12_local0(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
//! assert(local1 == 78)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyParams;

/// Fixed alphabet for parameter names.
const PARAM_NAMES: &[&str] = &["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"];

impl StmtRule for ManyParams {
    fn name(&self) -> &'static str {
        "many_params"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_sum(scope, emit, 8),
            _ => emit_sum(scope, emit, 12),
        }
    }
}

// ---------------------------------------------------------------------------
// Shared implementation for both variants
// ---------------------------------------------------------------------------

fn emit_sum(scope: &mut Scope, emit: &mut Emit, num_params: usize) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("sum{}_{}", num_params, fn_name);

    let names = &PARAM_NAMES[..num_params];

    // Build parameter signature: "a: i64, b: i64, ..."
    let param_sig: String = names
        .iter()
        .map(|n| format!("{}: i64", n))
        .collect::<Vec<_>>()
        .join(", ");

    // Build body: "return a + b + c + ..."
    let sum_expr: String = names.join(" + ");

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_label, param_sig, sum_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments with small i64 literals and compute expected sum.
    let mut args: Vec<i64> = Vec::with_capacity(num_params);
    for _ in 0..num_params {
        args.push(emit.gen_i64_range(1, 20));
    }
    let expected: i64 = args.iter().sum();

    let call_args: String = args
        .iter()
        .map(|v| format!("{}", v))
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == {})",
        result_name, fn_label, call_args, indent, result_name, expected,
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

    #[test]
    fn name_is_correct() {
        assert_eq!(ManyParams.name(), "many_params");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // No module => precondition fails
        assert!(!ManyParams.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ManyParams.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyParams.precondition(&scope, &params));
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
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParams.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum8_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for 8-param variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    // Should have exactly 8 params
                    let param_count = decl.matches(": i64").count();
                    assert_eq!(param_count, 8, "expected 8 i64 params in decl: {decl}");
                    assert!(
                        decl.contains("a + b + c + d + e + f + g + h"),
                        "expected sum of 8 params in body: {decl}"
                    );
                    // Should have assert in generated code
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated 8-param variant in 100 seeds");
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
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParams.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum12_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for 12-param variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    // Should have exactly 12 params
                    let param_count = decl.matches(": i64").count();
                    assert_eq!(param_count, 12, "expected 12 i64 params in decl: {decl}");
                    assert!(
                        decl.contains("a + b + c + d + e + f + g + h + i + j + k + l"),
                        "expected sum of 12 params in body: {decl}"
                    );
                    // Should have assert in generated code
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated 12-param variant in 100 seeds");
    }

    #[test]
    fn assert_checks_correct_sum() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParams.generate(&mut scope, &mut emit, &params) {
                // Extract the call arguments and the expected sum from the assert
                // Format: "let localN = sum{8|12}_localM(a1, a2, ...)\nassert(localN == SUM)"
                let lines: Vec<&str> = text.lines().collect();
                assert!(lines.len() >= 2, "expected at least 2 lines: {text}");

                // Parse arguments from the let line
                let let_line = lines[0];
                let args_start = let_line.find('(').unwrap() + 1;
                let args_end = let_line.rfind(')').unwrap();
                let args_str = &let_line[args_start..args_end];
                let computed_sum: i64 = args_str
                    .split(", ")
                    .map(|s| s.trim().parse::<i64>().unwrap())
                    .sum();

                // Parse expected from the assert line
                let assert_line = lines[1].trim();
                let eq_pos = assert_line.find("== ").unwrap();
                let close_pos = assert_line.rfind(')').unwrap();
                let expected: i64 = assert_line[eq_pos + 3..close_pos].parse().unwrap();

                assert_eq!(
                    computed_sum, expected,
                    "assert sum mismatch for seed {seed}: {text}"
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
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ManyParams.generate(&mut scope, &mut emit, &params);
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
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ManyParams.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
        let result_local = scope.locals.last().expect("should add result local");
        assert_eq!(
            result_local.1,
            TypeInfo::Primitive(PrimitiveType::I64),
            "result must be i64"
        );
    }

    #[test]
    fn exercises_both_variants() {
        let table = SymbolTable::new();
        let mut saw_8 = false;
        let mut saw_12 = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParams.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum8_") {
                    saw_8 = true;
                }
                if text.contains("sum12_") {
                    saw_12 = true;
                }
            }

            if saw_8 && saw_12 {
                break;
            }
        }

        assert!(saw_8, "never generated 8-param variant in 200 seeds");
        assert!(saw_12, "never generated 12-param variant in 200 seeds");
    }
}
