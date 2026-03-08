//! Rule: functions with default parameter values called with varying argument counts.
//!
//! Generates module-level functions that have one required parameter and one or two
//! default parameters, then emits 2-3 assert calls exercising the defaults and
//! named-argument overrides.
//!
//! Three templates (picked randomly):
//!
//! **Template 0 -- i64, one default:**
//! ```vole
//! func dpf_local0(x: i64, factor: i64 = 3) -> i64 {
//!     return x * factor
//! }
//! assert(dpf_local0(7) == 21)
//! assert(dpf_local0(7, factor: 5) == 35)
//! ```
//!
//! **Template 1 -- i64, two defaults:**
//! ```vole
//! func dpf_local0(x: i64, mult: i64 = 2, add: i64 = 10) -> i64 {
//!     return x * mult + add
//! }
//! assert(dpf_local0(5) == 20)
//! assert(dpf_local0(5, mult: 3) == 25)
//! assert(dpf_local0(5, mult: 3, add: 0) == 15)
//! ```
//!
//! **Template 2 -- string, one default:**
//! ```vole
//! func dpf_local0(x: string, prefix: string = "item") -> string {
//!     return "{prefix}:{x}"
//! }
//! assert(dpf_local0("hello") == "item:hello")
//! assert(dpf_local0("hello", prefix: "val") == "val:hello")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct DefaultParamFunc;

impl StmtRule for DefaultParamFunc {
    fn name(&self) -> &'static str {
        "default_param_func"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_i64_one_default(scope, emit),
            1 => emit_i64_two_defaults(scope, emit),
            _ => emit_string_one_default(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Template 0 -- i64, one default: x * factor
// ---------------------------------------------------------------------------

fn emit_i64_one_default(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_label = format!("dpf_{}", uid);

    let default_factor = emit.gen_i64_range(2, 9);

    let decl = format!(
        "func {}(x: i64, factor: i64 = {}) -> i64 {{\n    return x * factor\n}}",
        fn_label, default_factor,
    );
    scope.add_module_decl(decl);

    let x_val = emit.gen_i64_range(1, 20);
    let override_factor = emit.gen_i64_range(2, 9);

    // Call 1: all defaults
    let expected_default = x_val * default_factor;
    let assert1 = format!("assert({}({}) == {})", fn_label, x_val, expected_default);

    // Call 2: override factor
    let expected_override = x_val * override_factor;
    let assert2 = format!(
        "assert({}({}, factor: {}) == {})",
        fn_label, x_val, override_factor, expected_override,
    );

    Some(format!("{}\n{}", assert1, assert2))
}

// ---------------------------------------------------------------------------
// Template 1 -- i64, two defaults: x * mult + add
// ---------------------------------------------------------------------------

fn emit_i64_two_defaults(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_label = format!("dpf_{}", uid);

    let default_mult = emit.gen_i64_range(2, 6);
    let default_add = emit.gen_i64_range(1, 20);

    let decl = format!(
        "func {}(x: i64, mult: i64 = {}, add: i64 = {}) -> i64 {{\n    return x * mult + add\n}}",
        fn_label, default_mult, default_add,
    );
    scope.add_module_decl(decl);

    let x_val = emit.gen_i64_range(1, 15);
    let override_mult = emit.gen_i64_range(2, 6);
    let override_add = emit.gen_i64_range(0, 20);

    // Call 1: all defaults
    let expected1 = x_val * default_mult + default_add;
    let assert1 = format!("assert({}({}) == {})", fn_label, x_val, expected1);

    // Call 2: override mult only
    let expected2 = x_val * override_mult + default_add;
    let assert2 = format!(
        "assert({}({}, mult: {}) == {})",
        fn_label, x_val, override_mult, expected2,
    );

    // Call 3: override both
    let expected3 = x_val * override_mult + override_add;
    let assert3 = format!(
        "assert({}({}, mult: {}, add: {}) == {})",
        fn_label, x_val, override_mult, override_add, expected3,
    );

    Some(format!("{}\n{}\n{}", assert1, assert2, assert3))
}

// ---------------------------------------------------------------------------
// Template 2 -- string, one default: "{prefix}:{x}"
// ---------------------------------------------------------------------------

/// String literals used as the required argument.
const STRING_VALS: &[&str] = &["hello", "world", "test", "data", "foo", "bar"];

/// String literals used as the default prefix.
const DEFAULT_PREFIXES: &[&str] = &["item", "key", "tag", "node", "row"];

/// String literals used as the override prefix.
const OVERRIDE_PREFIXES: &[&str] = &["val", "obj", "ref", "src", "out"];

fn emit_string_one_default(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_label = format!("dpf_{}", uid);

    let default_prefix = DEFAULT_PREFIXES[emit.gen_range(0..DEFAULT_PREFIXES.len())];

    // Use curly-brace interpolation in the body: "{prefix}:{x}"
    let decl = format!(
        "func {}(x: string, prefix: string = \"{}\") -> string {{\n    return \"{{prefix}}:{{x}}\"\n}}",
        fn_label, default_prefix,
    );
    scope.add_module_decl(decl);

    let x_val = STRING_VALS[emit.gen_range(0..STRING_VALS.len())];
    let override_prefix = OVERRIDE_PREFIXES[emit.gen_range(0..OVERRIDE_PREFIXES.len())];

    // Call 1: all defaults
    let expected1 = format!("{}:{}", default_prefix, x_val);
    let assert1 = format!("assert({}(\"{}\") == \"{}\")", fn_label, x_val, expected1,);

    // Call 2: override prefix
    let expected2 = format!("{}:{}", override_prefix, x_val);
    let assert2 = format!(
        "assert({}(\"{}\", prefix: \"{}\") == \"{}\")",
        fn_label, x_val, override_prefix, expected2,
    );

    Some(format!("{}\n{}", assert1, assert2))
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
        assert_eq!(DefaultParamFunc.name(), "default_param_func");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!DefaultParamFunc.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(DefaultParamFunc.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!DefaultParamFunc.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_one_default_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = DefaultParamFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                // Template 0: one default param, "factor"
                if decl.contains("factor: i64 =") && !decl.contains("mult:") {
                    found = true;
                    assert!(
                        decl.contains("return x * factor"),
                        "expected body in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(
                        text.contains("factor:"),
                        "expected named arg override in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated i64 one-default variant in 100 seeds"
        );
    }

    #[test]
    fn generates_i64_two_defaults_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = DefaultParamFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                // Template 1: two default params, "mult" and "add"
                if decl.contains("mult: i64 =") && decl.contains("add: i64 =") {
                    found = true;
                    assert!(
                        decl.contains("return x * mult + add"),
                        "expected body in decl: {decl}"
                    );
                    assert!(text.contains("mult:"), "expected named arg in code: {text}");
                    assert!(
                        text.contains("add:"),
                        "expected second named arg in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated i64 two-defaults variant in 100 seeds"
        );
    }

    #[test]
    fn generates_string_one_default_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = DefaultParamFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                // Template 2: string default, "prefix"
                if decl.contains("prefix: string =") {
                    found = true;
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        text.contains("prefix:"),
                        "expected named arg in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated string one-default variant in 100 seeds"
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

        DefaultParamFunc.generate(&mut scope, &mut emit, &test_params());
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

        let result = DefaultParamFunc.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            scope.locals.is_empty(),
            "default_param_func should not add locals to scope"
        );
    }

    #[test]
    fn exercises_all_three_variants() {
        let table = SymbolTable::new();
        let mut saw_i64_one = false;
        let mut saw_i64_two = false;
        let mut saw_string = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(_text) = DefaultParamFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                if decl.contains("factor: i64 =") && !decl.contains("mult:") {
                    saw_i64_one = true;
                } else if decl.contains("mult: i64 =") && decl.contains("add: i64 =") {
                    saw_i64_two = true;
                } else if decl.contains("prefix: string =") {
                    saw_string = true;
                }
            }

            if saw_i64_one && saw_i64_two && saw_string {
                break;
            }
        }

        assert!(
            saw_i64_one,
            "never generated i64 one-default variant in 200 seeds"
        );
        assert!(
            saw_i64_two,
            "never generated i64 two-defaults variant in 200 seeds"
        );
        assert!(
            saw_string,
            "never generated string one-default variant in 200 seeds"
        );
    }

    #[test]
    fn i64_one_default_asserts_are_correct() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = DefaultParamFunc.generate(&mut scope, &mut emit, &test_params()) {
                let decl = &scope.module_decls[0];
                if !decl.contains("factor: i64 =") || decl.contains("mult:") {
                    continue;
                }

                // Parse default factor from decl: "factor: i64 = N"
                let factor_pos = decl.find("factor: i64 = ").unwrap() + "factor: i64 = ".len();
                let factor_end = decl[factor_pos..].find(')').unwrap() + factor_pos;
                let default_factor: i64 = decl[factor_pos..factor_end].parse().unwrap();

                // Parse asserts from text
                let lines: Vec<&str> = text.lines().collect();
                assert_eq!(lines.len(), 2, "expected 2 asserts for template 0");

                // First assert: func(x) == x * default_factor
                let line1 = lines[0];
                let x_start = line1.find('(').unwrap() + 1;
                let inner_open = line1[x_start..].find('(').unwrap() + x_start + 1;
                let inner_close = line1[inner_open..].find(')').unwrap() + inner_open;
                let x_val: i64 = line1[inner_open..inner_close].parse().unwrap();

                let eq_pos = line1.find("== ").unwrap() + 3;
                let end_pos = line1.rfind(')').unwrap();
                let expected: i64 = line1[eq_pos..end_pos].parse().unwrap();
                assert_eq!(
                    x_val * default_factor,
                    expected,
                    "default call mismatch for seed {seed}: {line1}"
                );
            }
        }
    }
}
