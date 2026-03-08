//! Rule: module-level function with a `when` expression containing many arms
//! (20 or 30) to stress-test when-expression compilation.
//!
//! The function is emitted as a module-level declaration via
//! [`Scope::add_module_decl`].  The call site asserts the result equals the
//! expected string for a specific input value.
//!
//! Two variants:
//!
//! **Variant 0 -- 20 arms:**
//! ```vole
//! func classify20_local0(x: i64) -> string {
//!     return when {
//!         x == 0 => "val_0"
//!         x == 1 => "val_1"
//!         ...
//!         x == 19 => "val_19"
//!         _ => "other"
//!     }
//! }
//! let local1 = classify20_local0(5)
//! assert(local1 == "val_5")
//! ```
//!
//! **Variant 1 -- 30 arms:**
//! ```vole
//! func classify30_local0(x: i64) -> string {
//!     return when {
//!         x == 0 => "val_0"
//!         ...
//!         x == 29 => "val_29"
//!         _ => "other"
//!     }
//! }
//! let local1 = classify30_local0(10)
//! assert(local1 == "val_10")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyWhenArms;

impl StmtRule for ManyWhenArms {
    fn name(&self) -> &'static str {
        "many_when_arms"
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
            0 => emit_when_func(scope, emit, 20),
            _ => emit_when_func(scope, emit, 30),
        }
    }
}

// ---------------------------------------------------------------------------
// Shared implementation for both variants
// ---------------------------------------------------------------------------

fn emit_when_func(scope: &mut Scope, emit: &mut Emit, num_arms: usize) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("classify{}_{}", num_arms, fn_name);
    let param_name = "x";

    // Build when arms: x == 0 => "val_0", x == 1 => "val_1", ...
    let mut arms = Vec::with_capacity(num_arms + 1);
    for i in 0..num_arms {
        arms.push(format!(
            "        {} == {} => \"val_{}\"",
            param_name, i, i
        ));
    }
    // Wildcard default arm.
    arms.push("        _ => \"other\"".to_string());

    let decl = format!(
        "func {}({}: i64) -> string {{\n    return when {{\n{}\n    }}\n}}",
        fn_label,
        param_name,
        arms.join("\n"),
    );
    scope.add_module_decl(decl);

    // Pick a test value: either a value within the arms or one outside (to test wildcard).
    let test_in_range = emit.gen_range(0..4) != 0; // 75% chance of in-range
    let test_val: i64;
    let expected: String;
    if test_in_range {
        let idx = emit.gen_range(0..num_arms);
        test_val = idx as i64;
        expected = format!("val_{}", idx);
    } else {
        // Pick a value outside the arm range to exercise the wildcard.
        test_val = num_arms as i64 + emit.gen_i64_range(1, 100);
        expected = "other".to_string();
    }

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == \"{}\")",
        result_name, fn_label, test_val, indent, result_name, expected,
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
        assert_eq!(ManyWhenArms.name(), "many_when_arms");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!ManyWhenArms.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ManyWhenArms.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyWhenArms.precondition(&scope, &params));
    }

    #[test]
    fn generates_20_arm_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyWhenArms.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("classify20_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for 20-arm variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("when {"),
                        "expected when expression in decl: {decl}"
                    );
                    // Should have exactly 20 value arms + 1 wildcard = 21 arrows
                    let arrow_count = decl.matches(" => ").count();
                    assert_eq!(
                        arrow_count, 21,
                        "expected 21 arms (20 + wildcard) in decl, got {arrow_count}: {decl}"
                    );
                    assert!(
                        decl.contains("x == 0 => \"val_0\""),
                        "expected first arm in decl: {decl}"
                    );
                    assert!(
                        decl.contains("x == 19 => \"val_19\""),
                        "expected last value arm in decl: {decl}"
                    );
                    assert!(
                        decl.contains("_ => \"other\""),
                        "expected wildcard arm in decl: {decl}"
                    );
                    assert!(
                        text.contains("assert("),
                        "expected assert in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated 20-arm variant in 100 seeds");
    }

    #[test]
    fn generates_30_arm_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyWhenArms.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("classify30_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for 30-arm variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    // Should have exactly 30 value arms + 1 wildcard = 31 arrows
                    let arrow_count = decl.matches(" => ").count();
                    assert_eq!(
                        arrow_count, 31,
                        "expected 31 arms (30 + wildcard) in decl, got {arrow_count}: {decl}"
                    );
                    assert!(
                        decl.contains("x == 29 => \"val_29\""),
                        "expected last value arm in decl: {decl}"
                    );
                    assert!(
                        text.contains("assert("),
                        "expected assert in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated 30-arm variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        ManyWhenArms.generate(&mut scope, &mut emit, &test_params());
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

        let result = ManyWhenArms.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
        let result_local = scope.locals.last().expect("should add result local");
        assert_eq!(
            result_local.1,
            TypeInfo::Primitive(PrimitiveType::String),
            "result must be string"
        );
    }

    #[test]
    fn exercises_both_variants() {
        let table = SymbolTable::new();
        let mut saw_20 = false;
        let mut saw_30 = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyWhenArms.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("classify20_") {
                    saw_20 = true;
                }
                if text.contains("classify30_") {
                    saw_30 = true;
                }
            }

            if saw_20 && saw_30 {
                break;
            }
        }

        assert!(saw_20, "never generated 20-arm variant in 200 seeds");
        assert!(saw_30, "never generated 30-arm variant in 200 seeds");
    }

    #[test]
    fn assert_checks_correct_value() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyWhenArms.generate(&mut scope, &mut emit, &test_params()) {
                let lines: Vec<&str> = text.lines().collect();
                assert!(lines.len() >= 2, "expected at least 2 lines: {text}");

                let let_line = lines[0];
                // Extract function call argument
                let args_start = let_line.rfind('(').unwrap() + 1;
                let args_end = let_line.rfind(')').unwrap();
                let call_arg: i64 = let_line[args_start..args_end].trim().parse().unwrap();

                // Extract expected string from assert
                let assert_line = lines[1].trim();
                let eq_pos = assert_line.find("== \"").unwrap();
                let close_pos = assert_line.rfind("\")").unwrap();
                let expected = &assert_line[eq_pos + 4..close_pos];

                // Determine the number of arms from the function name
                let num_arms: usize = if let_line.contains("classify20_") {
                    20
                } else {
                    30
                };

                // Verify: if call_arg is in [0, num_arms), expected should be "val_{call_arg}"
                // otherwise it should be "other"
                if call_arg >= 0 && (call_arg as usize) < num_arms {
                    assert_eq!(
                        expected,
                        format!("val_{}", call_arg),
                        "wrong expected for in-range call_arg={} seed={}: {text}",
                        call_arg,
                        seed,
                    );
                } else {
                    assert_eq!(
                        expected, "other",
                        "wrong expected for out-of-range call_arg={} seed={}: {text}",
                        call_arg, seed,
                    );
                }
            }
        }
    }
}
