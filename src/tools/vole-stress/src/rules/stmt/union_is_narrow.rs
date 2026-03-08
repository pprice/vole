//! Rule: generate functions with union parameter types and `is` check narrowing.
//!
//! Stresses the `IsCheck` codegen path for union parameters by generating
//! module-level functions that accept a 2-variant union parameter and use
//! `if param is Type` blocks to narrow each variant before returning a
//! stringified result.  Each variant is checked in its own `if` block, ending
//! with `unreachable`.
//!
//! Three union pairings are supported:
//!
//! **Variant 0 -- `i64 | string`:**
//! ```vole
//! func narrow_local0(p: i64 | string) -> string {
//!     if p is i64 {
//!         return "number: {p}"
//!     }
//!     if p is string {
//!         return "text: {p}"
//!     }
//!     unreachable
//! }
//! let local1 = narrow_local0(42)
//! assert(local1 == "number: 42")
//! let local2 = narrow_local0("hello")
//! assert(local2 == "text: hello")
//! ```
//!
//! **Variant 1 -- `i64 | bool`:**
//! ```vole
//! func narrow_local0(p: i64 | bool) -> string {
//!     if p is i64 {
//!         return "int: {p}"
//!     }
//!     if p is bool {
//!         return "flag: {p}"
//!     }
//!     unreachable
//! }
//! let local1 = narrow_local0(10)
//! assert(local1 == "int: 10")
//! let local2 = narrow_local0(true)
//! assert(local2 == "flag: true")
//! ```
//!
//! **Variant 2 -- `string | bool`:**
//! ```vole
//! func narrow_local0(p: string | bool) -> string {
//!     if p is string {
//!         return "text: {p}"
//!     }
//!     if p is bool {
//!         return "flag: {p}"
//!     }
//!     unreachable
//! }
//! let local1 = narrow_local0("hi")
//! assert(local1 == "text: hi")
//! let local2 = narrow_local0(false)
//! assert(local2 == "flag: false")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct UnionIsNarrow;

impl StmtRule for UnionIsNarrow {
    fn name(&self) -> &'static str {
        "union_is_narrow"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Functions must be at module level, not inside class methods.
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..TEMPLATES.len());
        emit_narrow_func(scope, emit, &TEMPLATES[variant])
    }
}

// ---------------------------------------------------------------------------
// Templates
// ---------------------------------------------------------------------------

struct NarrowTemplate {
    /// Label prefix for the function name.
    label: &'static str,
    /// First variant type.
    first_type: PrimitiveType,
    /// Second variant type.
    second_type: PrimitiveType,
    /// Label used in the string return for the first type.
    first_label: &'static str,
    /// Label used in the string return for the second type.
    second_label: &'static str,
    /// Test cases: (literal_for_first_variant, expected_output_for_first_variant,
    ///              literal_for_second_variant, expected_output_for_second_variant)
    cases: &'static [NarrowCase],
}

struct NarrowCase {
    first_literal: &'static str,
    first_expected: &'static str,
    second_literal: &'static str,
    second_expected: &'static str,
}

const TEMPLATES: &[NarrowTemplate] = &[
    // i64 | string
    NarrowTemplate {
        label: "narrow",
        first_type: PrimitiveType::I64,
        second_type: PrimitiveType::String,
        first_label: "number",
        second_label: "text",
        cases: &[
            NarrowCase {
                first_literal: "42",
                first_expected: "number: 42",
                second_literal: "\"hello\"",
                second_expected: "text: hello",
            },
            NarrowCase {
                first_literal: "0",
                first_expected: "number: 0",
                second_literal: "\"world\"",
                second_expected: "text: world",
            },
            NarrowCase {
                first_literal: "99",
                first_expected: "number: 99",
                second_literal: "\"vole\"",
                second_expected: "text: vole",
            },
        ],
    },
    // i64 | bool
    NarrowTemplate {
        label: "narrow",
        first_type: PrimitiveType::I64,
        second_type: PrimitiveType::Bool,
        first_label: "int",
        second_label: "flag",
        cases: &[
            NarrowCase {
                first_literal: "10",
                first_expected: "int: 10",
                second_literal: "true",
                second_expected: "flag: true",
            },
            NarrowCase {
                first_literal: "7",
                first_expected: "int: 7",
                second_literal: "false",
                second_expected: "flag: false",
            },
            NarrowCase {
                first_literal: "1",
                first_expected: "int: 1",
                second_literal: "true",
                second_expected: "flag: true",
            },
        ],
    },
    // string | bool
    NarrowTemplate {
        label: "narrow",
        first_type: PrimitiveType::String,
        second_type: PrimitiveType::Bool,
        first_label: "text",
        second_label: "flag",
        cases: &[
            NarrowCase {
                first_literal: "\"hi\"",
                first_expected: "text: hi",
                second_literal: "false",
                second_expected: "flag: false",
            },
            NarrowCase {
                first_literal: "\"test\"",
                first_expected: "text: test",
                second_literal: "true",
                second_expected: "flag: true",
            },
            NarrowCase {
                first_literal: "\"foo\"",
                first_expected: "text: foo",
                second_literal: "false",
                second_expected: "flag: false",
            },
        ],
    },
];

// ---------------------------------------------------------------------------
// Generation
// ---------------------------------------------------------------------------

fn emit_narrow_func(scope: &mut Scope, emit: &mut Emit, tmpl: &NarrowTemplate) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("{}_{}", tmpl.label, fn_name);

    let first_type_str = tmpl.first_type.as_str();
    let second_type_str = tmpl.second_type.as_str();

    // Build the module-level function declaration.
    let decl = format!(
        concat!(
            "func {}(p: {} | {}) -> string {{\n",
            "    if p is {} {{\n",
            "        return \"{}: {{p}}\"\n",
            "    }}\n",
            "    if p is {} {{\n",
            "        return \"{}: {{p}}\"\n",
            "    }}\n",
            "    unreachable\n",
            "}}"
        ),
        fn_label,
        first_type_str,
        second_type_str,
        first_type_str,
        tmpl.first_label,
        second_type_str,
        tmpl.second_label,
    );
    scope.add_module_decl(decl);

    // Pick a random test case.
    let case_idx = emit.gen_range(0..tmpl.cases.len());
    let case = &tmpl.cases[case_idx];

    let indent = emit.indent_str();

    // Bind call results and assert for each variant.
    let local_first = scope.fresh_name();
    scope.add_local(
        local_first.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let local_second = scope.fresh_name();
    scope.add_local(
        local_second.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {first} = {fn_label}({first_lit})\n\
         {indent}assert({first} == \"{first_exp}\")\n\
         {indent}let {second} = {fn_label}({second_lit})\n\
         {indent}assert({second} == \"{second_exp}\")",
        first = local_first,
        fn_label = fn_label,
        first_lit = case.first_literal,
        first_exp = case.first_expected,
        second = local_second,
        second_lit = case.second_literal,
        second_exp = case.second_expected,
        indent = indent,
    );

    Some(code)
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
        assert_eq!(UnionIsNarrow.name(), "union_is_narrow");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!UnionIsNarrow.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(UnionIsNarrow.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!UnionIsNarrow.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_string_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = UnionIsNarrow.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                if decl.contains("p: i64 | string") {
                    found = true;
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p is i64"),
                        "expected is-check for i64 in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p is string"),
                        "expected is-check for string in decl: {decl}"
                    );
                    assert!(
                        decl.contains("unreachable"),
                        "expected unreachable in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(
                        text.contains("number:") || text.contains("text:"),
                        "expected narrowing result in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated i64|string variant in 200 seeds");
    }

    #[test]
    fn generates_i64_bool_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = UnionIsNarrow.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                if decl.contains("p: i64 | bool") {
                    found = true;
                    assert!(
                        decl.contains("p is i64"),
                        "expected is-check for i64 in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p is bool"),
                        "expected is-check for bool in decl: {decl}"
                    );
                    assert!(
                        decl.contains("unreachable"),
                        "expected unreachable in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated i64|bool variant in 200 seeds");
    }

    #[test]
    fn generates_string_bool_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = UnionIsNarrow.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                if decl.contains("p: string | bool") {
                    found = true;
                    assert!(
                        decl.contains("p is string"),
                        "expected is-check for string in decl: {decl}"
                    );
                    assert!(
                        decl.contains("p is bool"),
                        "expected is-check for bool in decl: {decl}"
                    );
                    assert!(
                        decl.contains("unreachable"),
                        "expected unreachable in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated string|bool variant in 200 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        UnionIsNarrow.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn adds_two_string_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = UnionIsNarrow.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        // Two locals for the two call-site let-bindings, plus one consumed
        // by fresh_name for the function label.
        // The function name uses one fresh_name, then two more for call results.
        // But fresh_name counter is shared: fn_name = local0, first = local1, second = local2.
        // Only local1 and local2 are added via add_local.
        assert_eq!(
            scope.locals.len(),
            2,
            "expected 2 locals, got {}",
            scope.locals.len()
        );
        for (name, ty, _) in &scope.locals {
            assert_eq!(
                *ty,
                TypeInfo::Primitive(PrimitiveType::String),
                "expected string type for local '{}', got {:?}",
                name,
                ty
            );
        }
    }

    #[test]
    fn exercises_all_three_variants() {
        let table = SymbolTable::new();
        let mut saw_i64_string = false;
        let mut saw_i64_bool = false;
        let mut saw_string_bool = false;

        for seed in 0..300 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if UnionIsNarrow
                .generate(&mut scope, &mut emit, &test_params())
                .is_some()
            {
                let decl = &scope.module_decls[0];
                if decl.contains("p: i64 | string") {
                    saw_i64_string = true;
                }
                if decl.contains("p: i64 | bool") {
                    saw_i64_bool = true;
                }
                if decl.contains("p: string | bool") {
                    saw_string_bool = true;
                }
            }

            if saw_i64_string && saw_i64_bool && saw_string_bool {
                break;
            }
        }

        assert!(
            saw_i64_string,
            "never generated i64|string variant in 300 seeds"
        );
        assert!(
            saw_i64_bool,
            "never generated i64|bool variant in 300 seeds"
        );
        assert!(
            saw_string_bool,
            "never generated string|bool variant in 300 seeds"
        );
    }
}
