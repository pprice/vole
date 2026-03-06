//! Rule: module-level function with a match expression containing many arms
//! (15-30) to stress the switch optimization codegen path.
//!
//! The function is emitted as a module-level declaration via
//! [`Scope::add_module_decl`] so it stays as a proper `func`.
//!
//! Two variants are chosen at random:
//!
//! **Variant 0 -- match returning string:**
//! ```vole
//! func classify_42918(n: i64) -> string {
//!     return match n {
//!         0 => "val_0",
//!         1 => "val_1",
//!         ...
//!         19 => "val_19",
//!         _ => "other"
//!     }
//! }
//! let result_42918 = classify_42918(5)
//! ```
//!
//! **Variant 1 -- match returning i64:**
//! ```vole
//! func lookup_42918(n: i64) -> i64 {
//!     return match n {
//!         0 => 100,
//!         1 => 201,
//!         ...
//!         24 => 2500,
//!         _ => -1
//!     }
//! }
//! let result_42918 = lookup_42918(10)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyMatchArms;

impl StmtRule for ManyMatchArms {
    fn name(&self) -> &'static str {
        "many_match_arms"
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
            0 => emit_string_match(scope, emit),
            _ => emit_i64_match(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: match returning string
// ---------------------------------------------------------------------------

fn emit_string_match(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_arms = emit.random_in(15, 25);
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("classify_{}", uid);

    // Build match arms: consecutive integers mapping to string literals.
    let mut arms = Vec::with_capacity(num_arms + 1);
    for i in 0..num_arms {
        arms.push(format!("        {} => \"val_{}\"", i, i));
    }
    arms.push("        _ => \"other\"".to_string());

    let decl = format!(
        "func {}(n: i64) -> string {{\n    return match n {{\n{}\n    }}\n}}",
        fn_name,
        arms.join("\n"),
    );
    scope.add_module_decl(decl);

    // Call with a value inside the match range.
    let call_arg = emit.gen_range(0..num_arms);

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!("let {} = {}({})", result_name, fn_name, call_arg))
}

// ---------------------------------------------------------------------------
// Variant 1: match returning i64
// ---------------------------------------------------------------------------

fn emit_i64_match(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_arms = emit.random_in(20, 30);
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("lookup_{}", uid);

    // Build match arms: consecutive integers mapping to arithmetic values.
    let mut arms = Vec::with_capacity(num_arms + 1);
    for i in 0..num_arms {
        let value = (i as i64) * 100 + (i as i64);
        arms.push(format!("        {} => {}", i, value));
    }
    arms.push("        _ => -1".to_string());

    let decl = format!(
        "func {}(n: i64) -> i64 {{\n    return match n {{\n{}\n    }}\n}}",
        fn_name,
        arms.join("\n"),
    );
    scope.add_module_decl(decl);

    // Call with a value inside the match range.
    let call_arg = emit.gen_range(0..num_arms);

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("let {} = {}({})", result_name, fn_name, call_arg))
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
        assert_eq!(ManyMatchArms.name(), "many_match_arms");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!ManyMatchArms.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ManyMatchArms.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyMatchArms.precondition(&scope, &params));
    }

    #[test]
    fn generates_string_match_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyMatchArms.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("classify_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for string match"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("n: i64"),
                        "expected param 'n: i64' in decl: {decl}"
                    );
                    // Should have val_ string literals
                    assert!(
                        decl.contains("\"val_0\""),
                        "expected val_0 string in decl: {decl}"
                    );
                    // Should have wildcard arm
                    assert!(
                        decl.contains("_ => \"other\""),
                        "expected wildcard arm in decl: {decl}"
                    );
                    // Count arms (15-25 + wildcard)
                    let arrow_count = decl.matches(" => ").count();
                    assert!(
                        (16..=26).contains(&arrow_count),
                        "expected 16-26 arms (15-25 + wildcard), got {arrow_count}"
                    );
                    // Result should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "string match result must be string"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated string match variant in 100 seeds");
    }

    #[test]
    fn generates_i64_match_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyMatchArms.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("lookup_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for i64 match"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("n: i64"),
                        "expected param 'n: i64' in decl: {decl}"
                    );
                    // Should have wildcard arm returning -1
                    assert!(
                        decl.contains("_ => -1"),
                        "expected wildcard arm returning -1 in decl: {decl}"
                    );
                    // Count arms (20-30 + wildcard)
                    let arrow_count = decl.matches(" => ").count();
                    assert!(
                        (21..=31).contains(&arrow_count),
                        "expected 21-31 arms (20-30 + wildcard), got {arrow_count}"
                    );
                    // Result should be i64
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::I64),
                        "i64 match result must be i64"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated i64 match variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        ManyMatchArms.generate(&mut scope, &mut emit, &test_params());
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

        let result = ManyMatchArms.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
    }

    #[test]
    fn result_name_uses_uid() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        if let Some(text) = ManyMatchArms.generate(&mut scope, &mut emit, &test_params()) {
            assert!(
                text.contains("result_"),
                "expected result_NNNNN in code: {text}"
            );
        }
    }

    #[test]
    fn consecutive_arm_values() {
        let table = SymbolTable::new();
        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            ManyMatchArms.generate(&mut scope, &mut emit, &test_params());
            let decl = &scope.module_decls[0];

            // Extract all numeric arm values (lines with " => " but not the wildcard).
            let mut arm_values: Vec<i64> = Vec::new();
            for line in decl.lines() {
                let trimmed = line.trim();
                if trimmed.starts_with('_') || !trimmed.contains(" => ") {
                    continue;
                }
                let val_str = trimmed.split(" => ").next().unwrap().trim();
                if let Ok(v) = val_str.parse::<i64>() {
                    arm_values.push(v);
                }
            }

            // Verify consecutive integers starting from 0
            for (i, &v) in arm_values.iter().enumerate() {
                assert_eq!(
                    v, i as i64,
                    "expected arm {} to have value {}, got {} (seed {})",
                    i, i, v, seed
                );
            }
        }
    }

    #[test]
    fn call_arg_within_range() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyMatchArms.generate(&mut scope, &mut emit, &test_params()) {
                // Extract the call argument from "fn_name(arg)"
                let paren_open = text.rfind('(').unwrap();
                let paren_close = text.rfind(')').unwrap();
                let arg_str = &text[paren_open + 1..paren_close];
                let arg: usize = arg_str.parse().expect("call arg should be a number");

                // Count non-wildcard arms in the decl
                let decl = &scope.module_decls[0];
                let num_arms = decl
                    .lines()
                    .filter(|l| {
                        let t = l.trim();
                        t.contains(" => ") && !t.starts_with('_')
                    })
                    .count();

                assert!(
                    arg < num_arms,
                    "call arg {} should be < num_arms {} (seed {})",
                    arg,
                    num_arms,
                    seed,
                );
            }
        }
    }
}
