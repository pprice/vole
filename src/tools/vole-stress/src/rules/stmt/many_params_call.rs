//! Rule: module-level function with many parameters (8-12) to stress calling
//! conventions.
//!
//! The function is emitted as a module-level declaration via
//! [`Scope::add_module_decl`] so that vole-fmt keeps it as a `func` rather
//! than rewriting it to a lambda (lambdas can't handle this many params as
//! well).
//!
//! Two variants are chosen at random:
//!
//! **Variant 0 -- many i64 params (sum):**
//! ```vole
//! func sum_many_42918(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64 {
//!     return a + b + c + d + e + f + g + h
//! }
//! let result_42918 = sum_many_42918(1, 2, 3, 4, 5, 6, 7, 8)
//! ```
//!
//! **Variant 1 -- many mixed-type params:**
//! ```vole
//! func process_42918(a: i64, b: string, c: f64, d: bool, e: i64, f: string, g: i64, h: f64) -> i64 {
//!     return a + e + g
//! }
//! let result_42918 = process_42918(10, "hello", 3.14, true, 20, "world", 30, 2.72)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyParamsCall;

/// Fixed alphabet for parameter names.
const PARAM_NAMES: &[&str] = &["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"];

/// Mixed types drawn from for variant 1.
const MIXED_TYPES: &[PrimitiveType] = &[
    PrimitiveType::I64,
    PrimitiveType::String,
    PrimitiveType::F64,
    PrimitiveType::Bool,
];

impl StmtRule for ManyParamsCall {
    fn name(&self) -> &'static str {
        "many_params_call"
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
            0 => emit_i64_sum(scope, emit),
            _ => emit_mixed_params(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: many i64 params -- sum them all
// ---------------------------------------------------------------------------

fn emit_i64_sum(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_params = emit.random_in(8, 12);
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("sum_many_{}", uid);

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
        fn_name, param_sig, sum_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments with small i64 literals.
    let call_args: String = (0..num_params)
        .map(|i| format!("{}", i as i64 + 1))
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("let {} = {}({})", result_name, fn_name, call_args,))
}

// ---------------------------------------------------------------------------
// Variant 1: many mixed-type params -- return i64 (sum of i64 params)
// ---------------------------------------------------------------------------

fn emit_mixed_params(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_params = emit.random_in(8, 10);
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("process_{}", uid);

    let names = &PARAM_NAMES[..num_params];

    // Assign a random type to each param, ensuring at least 2 are i64.
    let mut param_types: Vec<PrimitiveType> = Vec::with_capacity(num_params);
    for _ in 0..num_params {
        let idx = emit.gen_range(0..MIXED_TYPES.len());
        param_types.push(MIXED_TYPES[idx]);
    }

    // Ensure at least 2 i64 params so the body has something to sum.
    let i64_count = param_types
        .iter()
        .filter(|t| matches!(t, PrimitiveType::I64))
        .count();
    if i64_count < 2 {
        // Force the first two non-i64 slots to i64.
        let mut forced = 0;
        for t in param_types.iter_mut() {
            if forced >= 2 - i64_count {
                break;
            }
            if !matches!(t, PrimitiveType::I64) {
                *t = PrimitiveType::I64;
                forced += 1;
            }
        }
    }

    // Build parameter signature: "a: i64, b: string, c: f64, ..."
    let param_sig: String = names
        .iter()
        .zip(param_types.iter())
        .map(|(n, t)| format!("{}: {}", n, t.as_str()))
        .collect::<Vec<_>>()
        .join(", ");

    // Body: return sum of all i64 params.
    let i64_params: Vec<&str> = names
        .iter()
        .zip(param_types.iter())
        .filter(|(_, t)| matches!(t, PrimitiveType::I64))
        .map(|(n, _)| *n)
        .collect();
    let sum_expr = i64_params.join(" + ");

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_name, param_sig, sum_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments with appropriate literals for each type.
    let call_args: String = param_types
        .iter()
        .map(|t| emit.literal(&TypeInfo::Primitive(*t)))
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("let {} = {}({})", result_name, fn_name, call_args,))
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
        assert_eq!(ManyParamsCall.name(), "many_params_call");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // No module => precondition fails
        assert!(!ManyParamsCall.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ManyParamsCall.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyParamsCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_sum_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamsCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum_many_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for i64 sum"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    // Should use named params (a, b, c, ...)
                    assert!(
                        decl.contains("a: i64"),
                        "expected named param 'a: i64' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("h: i64"),
                        "expected named param 'h: i64' in decl: {decl}"
                    );
                    // Body should sum params
                    assert!(
                        decl.contains("a + b + c"),
                        "expected sum expression in decl: {decl}"
                    );
                    // Result should be i64
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::I64),
                        "sum result must be i64"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated i64 sum variant in 100 seeds");
    }

    #[test]
    fn generates_mixed_params_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamsCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("process_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for mixed params"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    // Should use named params
                    assert!(
                        decl.contains("a:"),
                        "expected named param 'a' in decl: {decl}"
                    );
                    // Should have at least some non-i64 types (mixed)
                    let has_mixed =
                        decl.contains("string") || decl.contains("f64") || decl.contains("bool");
                    assert!(has_mixed, "expected mixed types in decl: {decl}");
                    // Result should be i64
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::I64),
                        "mixed params result must be i64"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated mixed params variant in 100 seeds");
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

        ManyParamsCall.generate(&mut scope, &mut emit, &params);
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

        let result = ManyParamsCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
    }

    #[test]
    fn i64_sum_param_count_in_range() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if ManyParamsCall
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                let decl = &scope.module_decls[0];
                // Count typed params by counting ": " in the signature line
                let sig = decl.lines().next().unwrap();
                let param_count = sig.matches(": ").count();
                // Both variants: 8-12 or 8-10
                assert!(
                    (8..=12).contains(&param_count),
                    "expected 8-12 params, got {} for seed {}: {}",
                    param_count,
                    seed,
                    sig,
                );
            }
        }
    }

    #[test]
    fn result_name_uses_uid() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        if let Some(text) = ManyParamsCall.generate(&mut scope, &mut emit, &params) {
            assert!(
                text.contains("result_"),
                "expected result_NNNNN in code: {text}"
            );
        }
    }

    #[test]
    fn mixed_params_has_at_least_two_i64() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamsCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("process_") {
                    let decl = &scope.module_decls[0];
                    let i64_count = decl.matches(": i64").count();
                    assert!(
                        i64_count >= 2,
                        "expected >= 2 i64 params in mixed variant, got {}: {}",
                        i64_count,
                        decl,
                    );
                    // Body should have a + expression with at least 2 terms
                    assert!(decl.contains(" + "), "expected sum in body: {}", decl,);
                }
            }
        }
    }
}
