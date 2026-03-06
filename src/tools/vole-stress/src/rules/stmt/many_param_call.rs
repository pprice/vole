//! Rule: module-level function with many homogeneous parameters (6-10).
//!
//! Generates a module-level function via [`Scope::add_module_decl`] with 6-10
//! parameters of the same type, then calls it with literal values.  This
//! stresses calling conventions and register allocation when many arguments
//! of the same type must be threaded through to a return value.
//!
//! Two variants are chosen at random:
//!
//! **Variant 1 -- sum (all i64)**
//! ```vole
//! func sum_local0(p0: i64, p1: i64, p2: i64, p3: i64, p4: i64, p5: i64) -> i64 {
//!     return p0 + p1 + p2 + p3 + p4 + p5
//! }
//! let local1 = sum_local0(1, 2, 3, 4, 5, 6)
//! ```
//!
//! **Variant 2 -- concat (all string)**
//! ```vole
//! func concat_local0(p0: string, p1: string, p2: string, p3: string, p4: string, p5: string) -> string {
//!     return p0 + p1 + p2 + p3 + p4 + p5
//! }
//! let local1 = concat_local0("a", "b", "c", "d", "e", "f")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyParamCall;

impl StmtRule for ManyParamCall {
    fn name(&self) -> &'static str {
        "many_param_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Only fire outside class methods -- module-level decls cannot be
        // spliced inside a class body.
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_sum(scope, emit),
            _ => emit_concat(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: sum -- all i64 parameters, returns i64
// ---------------------------------------------------------------------------

fn emit_sum(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_params = emit.random_in(6, 10);

    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("sum_{}", fn_id);

    // Build parameter signature: "p0: i64, p1: i64, ..."
    let param_sig: String = (0..num_params)
        .map(|i| format!("p{}: i64", i))
        .collect::<Vec<_>>()
        .join(", ");

    // Build body: "return p0 + p1 + p2 + ..."
    let sum_expr: String = (0..num_params)
        .map(|i| format!("p{}", i))
        .collect::<Vec<_>>()
        .join(" + ");

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_name, param_sig, sum_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments with i64 literals.
    let call_args: String = (0..num_params)
        .map(|_| {
            let val = emit.gen_i64_range(1, 20);
            format!("{}", val)
        })
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("let {} = {}({})", result_name, fn_name, call_args,))
}

// ---------------------------------------------------------------------------
// Variant 2: concat -- all string parameters, returns string
// ---------------------------------------------------------------------------

/// Short string literals for call arguments.
const STRING_ARGS: &[&str] = &[
    "\"a\"", "\"b\"", "\"c\"", "\"d\"", "\"e\"", "\"f\"", "\"g\"", "\"h\"", "\"j\"", "\"k\"",
];

fn emit_concat(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_params = emit.random_in(6, 10);

    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("concat_{}", fn_id);

    // Build parameter signature: "p0: string, p1: string, ..."
    let param_sig: String = (0..num_params)
        .map(|i| format!("p{}: string", i))
        .collect::<Vec<_>>()
        .join(", ");

    // Build body: "return p0 + p1 + p2 + ..."
    let concat_expr: String = (0..num_params)
        .map(|i| format!("p{}", i))
        .collect::<Vec<_>>()
        .join(" + ");

    let decl = format!(
        "func {}({}) -> string {{\n    return {}\n}}",
        fn_name, param_sig, concat_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments with short string literals.
    let call_args: String = (0..num_params)
        .map(|_| {
            let idx = emit.gen_range(0..STRING_ARGS.len());
            STRING_ARGS[idx].to_string()
        })
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
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
        assert_eq!(ManyParamCall.name(), "many_param_call");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No class => precondition passes
        assert!(ManyParamCall.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyParamCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_sum_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum_") {
                    found = true;
                    // Verify module decl was registered
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for sum"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p0: i64"),
                        "expected i64 param type in decl: {decl}"
                    );
                    // Verify 6-10 params
                    let param_count = decl.matches("p").count() - 1; // subtract "return p0"
                    assert!(
                        param_count >= 6,
                        "expected >= 6 params, got {param_count} in: {decl}"
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
        assert!(found, "never generated sum variant in 100 seeds");
    }

    #[test]
    fn generates_concat_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("concat_") {
                    found = true;
                    // Verify module decl was registered
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for concat"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p0: string"),
                        "expected string param type in decl: {decl}"
                    );
                    // Result should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "concat result must be string"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated concat variant in 100 seeds");
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ManyParamCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        // The func name consumes one fresh_name, the result consumes another.
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ManyParamCall.generate(&mut scope, &mut emit, &params);
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn param_count_in_range() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            ManyParamCall.generate(&mut scope, &mut emit, &params);
            let decl = &scope.module_decls[0];
            // Count ": i64" or ": string" occurrences in the signature
            let param_count = decl.matches(": i64").count() + decl.matches(": string").count();
            assert!(
                (6..=10).contains(&param_count),
                "expected 6-10 params, got {} for seed {}: {}",
                param_count,
                seed,
                decl,
            );
        }
    }
}
