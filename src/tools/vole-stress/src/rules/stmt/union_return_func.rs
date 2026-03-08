//! Rule: module-level functions with union return types.
//!
//! Generates a function that returns different union variants from different
//! branches, exercising union type construction in return position.  The call
//! site uses `as?` to verify the correct variant was returned.
//!
//! Two variants:
//!
//! **Variant 0 -- i64|string (~50%):**
//! ```vole
//! func union_ret_local0(x: i64) -> i64 | string {
//!     if x > 0 {
//!         return x
//!     }
//!     return "non-positive"
//! }
//! let local1 = union_ret_local0(5)
//! let local2 = local1 as? i64
//! assert(local2 != nil)
//! ```
//!
//! **Variant 1 -- bool|i64 (~50%):**
//! ```vole
//! func union_ret_local0(x: i64) -> bool | i64 {
//!     if x > 0 {
//!         return true
//!     }
//!     return x
//! }
//! let local1 = union_ret_local0(5)
//! let local2 = local1 as? bool
//! assert(local2 != nil)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct UnionReturnFunc;

impl StmtRule for UnionReturnFunc {
    fn name(&self) -> &'static str {
        "union_return_func"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if emit.gen_bool(0.5) {
            emit_i64_string_variant(scope, emit)
        } else {
            emit_bool_i64_variant(scope, emit)
        }
    }
}

// ---------------------------------------------------------------------------
// Templates
// ---------------------------------------------------------------------------

/// i64|string templates.  Each entry:
///   (label, condition_on_x, i64_return_expr, string_literal, test_input, expected_cast_type, expected_cast_succeeds)
const I64_STRING_TEMPLATES: &[UnionTemplate] = &[
    UnionTemplate {
        label: "classify",
        condition: "x > 0",
        first_return: "x",
        second_return: "\"non-positive\"",
        first_type: "i64",
        second_type: "string",
        cases: &[
            // (input, cast_target, cast_succeeds)
            (5, "i64", true),
            (-1, "string", true),
            (0, "string", true),
        ],
    },
    UnionTemplate {
        label: "tag",
        condition: "x >= 0",
        first_return: "x",
        second_return: "\"negative\"",
        first_type: "i64",
        second_type: "string",
        cases: &[(10, "i64", true), (-3, "string", true), (0, "i64", true)],
    },
    UnionTemplate {
        label: "label_or_val",
        condition: "x % 2 == 0",
        first_return: "x",
        second_return: "\"odd\"",
        first_type: "i64",
        second_type: "string",
        cases: &[(4, "i64", true), (7, "string", true), (0, "i64", true)],
    },
];

/// bool|i64 templates.
const BOOL_I64_TEMPLATES: &[UnionTemplate] = &[
    UnionTemplate {
        label: "check",
        condition: "x > 0",
        first_return: "true",
        second_return: "x",
        first_type: "bool",
        second_type: "i64",
        cases: &[(5, "bool", true), (-1, "i64", true), (0, "i64", true)],
    },
    UnionTemplate {
        label: "flag",
        condition: "x == 0",
        first_return: "false",
        second_return: "x",
        first_type: "bool",
        second_type: "i64",
        cases: &[(0, "bool", true), (42, "i64", true), (-5, "i64", true)],
    },
    UnionTemplate {
        label: "pass_fail",
        condition: "x >= 10",
        first_return: "true",
        second_return: "x",
        first_type: "bool",
        second_type: "i64",
        cases: &[(10, "bool", true), (100, "bool", true), (3, "i64", true)],
    },
];

struct UnionTemplate {
    label: &'static str,
    condition: &'static str,
    first_return: &'static str,
    second_return: &'static str,
    first_type: &'static str,
    second_type: &'static str,
    cases: &'static [(i64, &'static str, bool)],
}

// ---------------------------------------------------------------------------
// Variant 0 -- i64 | string
// ---------------------------------------------------------------------------

fn emit_i64_string_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    emit_union_variant(scope, emit, I64_STRING_TEMPLATES)
}

// ---------------------------------------------------------------------------
// Variant 1 -- bool | i64
// ---------------------------------------------------------------------------

fn emit_bool_i64_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    emit_union_variant(scope, emit, BOOL_I64_TEMPLATES)
}

// ---------------------------------------------------------------------------
// Shared generation logic
// ---------------------------------------------------------------------------

fn emit_union_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    templates: &[UnionTemplate],
) -> Option<String> {
    let tmpl_idx = emit.gen_range(0..templates.len());
    let tmpl = &templates[tmpl_idx];

    let fn_name = scope.fresh_name();
    let fn_label = format!("{}_{}", tmpl.label, fn_name);

    let decl = format!(
        "func {}(x: i64) -> {} | {} {{\n    if {} {{\n        return {}\n    }}\n    return {}\n}}",
        fn_label,
        tmpl.first_type,
        tmpl.second_type,
        tmpl.condition,
        tmpl.first_return,
        tmpl.second_return,
    );
    scope.add_module_decl(decl);

    // Pick a random test case.
    let case_idx = emit.gen_range(0..tmpl.cases.len());
    let (input, cast_target, _cast_succeeds) = tmpl.cases[case_idx];

    // Call the function and bind the result.
    let result_name = scope.fresh_name();
    // Do NOT add the union result to scope -- it's a union type and not safely usable.

    // Bind the as? cast result to a variable.
    let cast_name = scope.fresh_name();
    // Do NOT add the Optional cast result to scope -- it's Optional and not safely usable.

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{indent}let {} = {} as? {}\n{indent}assert({} != nil)",
        result_name, fn_label, input, cast_name, result_name, cast_target, cast_name,
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
        assert_eq!(UnionReturnFunc.name(), "union_return_func");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!UnionReturnFunc.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(UnionReturnFunc.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!UnionReturnFunc.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_string_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = UnionReturnFunc.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("as? i64") || text.contains("as? string") {
                    // Check that a module decl was added with the i64 | string return type.
                    let decl = &scope.module_decls[0];
                    if decl.contains("-> i64 | string") {
                        found = true;
                        assert!(
                            decl.contains("return x") || decl.contains("return \""),
                            "expected return variants in decl: {decl}"
                        );
                        assert!(
                            text.contains("as?"),
                            "expected as? cast in call site: {text}"
                        );
                        assert!(
                            text.contains("!= nil"),
                            "expected nil check in call site: {text}"
                        );
                        break;
                    }
                }
            }
        }
        assert!(found, "never generated i64|string variant in 100 seeds");
    }

    #[test]
    fn generates_bool_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = UnionReturnFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                if decl.contains("-> bool | i64") {
                    found = true;
                    assert!(
                        decl.contains("return true") || decl.contains("return false"),
                        "expected bool return in decl: {decl}"
                    );
                    assert!(
                        text.contains("as?"),
                        "expected as? cast in call site: {text}"
                    );
                    assert!(
                        text.contains("!= nil"),
                        "expected nil check in call site: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated bool|i64 variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        UnionReturnFunc.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn does_not_add_locals_to_scope() {
        // Union and Optional results should NOT be added to scope.
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = UnionReturnFunc.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            scope.locals.is_empty(),
            "union/optional results should not be added to scope"
        );
    }
}
