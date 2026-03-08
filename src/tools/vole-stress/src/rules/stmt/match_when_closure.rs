//! Rule: closures containing match/when expressions that capture outer variables.
//!
//! Exercises closure captures + pattern matching + string interpolation together.
//!
//! **Variant 1 -- match in closure with capture (string result):**
//! ```vole
//! let x = 42
//! let f = (y: i64) -> string => match y {
//!     42 => "found {x}"
//!     _ => "nope"
//! }
//! assert(f(42) == "found 42")
//! assert(f(0) == "nope")
//! ```
//!
//! **Variant 2 -- when in closure with capture (string result):**
//! ```vole
//! let label = "ok"
//! let check = (n: i64) -> string => when {
//!     n > 10 => "{label}: big"
//!     n > 0 => "{label}: small"
//!     _ => "{label}: zero"
//! }
//! assert(check(20) == "ok: big")
//! assert(check(5) == "ok: small")
//! assert(check(0) == "ok: zero")
//! ```
//!
//! **Variant 3 -- nested match in closure with arithmetic capture (i64 result):**
//! ```vole
//! let base = 100
//! let classify = (a: i64, b: bool) -> i64 => match b {
//!     true => match a {
//!         0 => base
//!         _ => base + a
//!     }
//!     _ => base - a
//! }
//! assert(classify(5, true) == 105)
//! assert(classify(5, false) == 95)
//! assert(classify(0, true) == 100)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchWhenClosure;

impl StmtRule for MatchWhenClosure {
    fn name(&self) -> &'static str {
        "match_when_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_match_closure(scope, emit),
            1 => emit_when_closure(scope, emit),
            _ => emit_nested_match_closure(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1 -- match in closure with string interpolation capture
// ---------------------------------------------------------------------------

fn emit_match_closure(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let indent = emit.indent_str();

    // Create captured i64 variable with a known value
    let captured_name = scope.fresh_name();
    let captured_val = emit.gen_i64_range(1, 99);

    // Create the closure
    let closure_name = scope.fresh_name();

    // Pick a match literal that we'll test against
    let match_lit = emit.gen_i64_range(0, 9);

    // Build match arms: one specific arm and a wildcard
    let hit_str = format!("found {}", captured_val);
    let miss_strs = ["nope", "miss", "other", "none"];
    let miss_str = miss_strs[emit.gen_range(0..miss_strs.len())];

    let closure_def = format!(
        "let {} = {}\n\
         {}let {} = (y: i64) -> string => match y {{\n\
         {}    {} => \"found {{{}}}\",\n\
         {}    _ => \"{}\",\n\
         {}}}",
        captured_name,
        captured_val,
        indent,
        closure_name,
        indent,
        match_lit,
        captured_name,
        indent,
        miss_str,
        indent,
    );

    // Add captured var to scope
    scope.add_local(
        captured_name,
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Add closure to scope as string-returning
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // Generate assertions
    // Call with the matching literal => "found {captured_val}"
    let assert_hit = format!("assert({}({}) == \"{}\")", closure_name, match_lit, hit_str,);

    // Call with a different literal => miss_str
    let mut other_lit = emit.gen_i64_range(0, 9);
    while other_lit == match_lit {
        other_lit = emit.gen_i64_range(0, 9);
    }
    let assert_miss = format!(
        "assert({}({}) == \"{}\")",
        closure_name, other_lit, miss_str,
    );

    Some(format!(
        "{}\n{}{}\n{}{}",
        closure_def, indent, assert_hit, indent, assert_miss,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- when in closure with string interpolation capture
// ---------------------------------------------------------------------------

fn emit_when_closure(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let indent = emit.indent_str();

    // Create captured string variable
    let captured_name = scope.fresh_name();
    let label_choices = ["ok", "status", "info", "tag", "msg"];
    let label_val = label_choices[emit.gen_range(0..label_choices.len())];

    // Create the closure
    let closure_name = scope.fresh_name();

    // Pick thresholds for conditions
    let high_thresh = emit.gen_i64_range(10, 20);
    let low_thresh = emit.gen_i64_range(1, 9);

    // Suffixes for each arm
    let big_suffix = ["big", "high", "large", "major"];
    let small_suffix = ["small", "low", "tiny", "minor"];
    let zero_suffix = ["zero", "none", "nil", "empty"];

    let big = big_suffix[emit.gen_range(0..big_suffix.len())];
    let small = small_suffix[emit.gen_range(0..small_suffix.len())];
    let zero = zero_suffix[emit.gen_range(0..zero_suffix.len())];

    let closure_def = format!(
        "let {} = \"{}\"\n\
         {}let {} = (n: i64) -> string => when {{\n\
         {}    n > {} => \"{{{}}}: {}\",\n\
         {}    n > {} => \"{{{}}}: {}\",\n\
         {}    _ => \"{{{}}}: {}\",\n\
         {}}}",
        captured_name,
        label_val,
        indent,
        closure_name,
        indent,
        high_thresh,
        captured_name,
        big,
        indent,
        low_thresh,
        captured_name,
        small,
        indent,
        captured_name,
        zero,
        indent,
    );

    // Add captured var to scope
    scope.add_local(
        captured_name,
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // Add closure to scope as string-returning
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // Generate assertions with pre-computed expected values
    let big_test = high_thresh + emit.gen_i64_range(1, 10);
    let small_test = low_thresh + 1; // guaranteed > low_thresh but need <= high_thresh
    // Ensure small_test <= high_thresh
    let small_test = if small_test > high_thresh {
        low_thresh + 1
    } else {
        small_test
    };
    let zero_test = emit.gen_i64_range(-5, 0);
    // Ensure zero_test <= low_thresh
    let zero_test = if zero_test > low_thresh { 0 } else { zero_test };

    let expected_big = format!("{}: {}", label_val, big);
    let expected_small = format!("{}: {}", label_val, small);
    let expected_zero = format!("{}: {}", label_val, zero);

    let assert_big = format!(
        "assert({}({}) == \"{}\")",
        closure_name, big_test, expected_big,
    );
    let assert_small = format!(
        "assert({}({}) == \"{}\")",
        closure_name, small_test, expected_small,
    );
    let assert_zero = format!(
        "assert({}({}) == \"{}\")",
        closure_name, zero_test, expected_zero,
    );

    Some(format!(
        "{}\n{}{}\n{}{}\n{}{}",
        closure_def, indent, assert_big, indent, assert_small, indent, assert_zero,
    ))
}

// ---------------------------------------------------------------------------
// Variant 3 -- nested match in closure with arithmetic capture
// ---------------------------------------------------------------------------

fn emit_nested_match_closure(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let indent = emit.indent_str();

    // Create captured i64 variable (the base value)
    let captured_name = scope.fresh_name();
    let base_val = emit.gen_i64_range(10, 200);

    // Create the closure
    let closure_name = scope.fresh_name();

    // Pick the specific match value for inner match
    let inner_match_val = 0_i64;

    // Build the closure:
    // (a: i64, b: bool) -> i64 => match b {
    //     true => match a {
    //         0 => base
    //         _ => base + a
    //     }
    //     _ => base - a
    // }
    let closure_def = format!(
        "let {} = {}\n\
         {}let {} = (a: i64, b: bool) -> i64 => match b {{\n\
         {}    true => match a {{\n\
         {}        {} => {},\n\
         {}        _ => {} + a,\n\
         {}    }},\n\
         {}    _ => {} - a,\n\
         {}}}",
        captured_name,
        base_val,
        indent,
        closure_name,
        indent,
        indent,
        inner_match_val,
        captured_name,
        indent,
        captured_name,
        indent,
        indent,
        captured_name,
        indent,
    );

    // Add captured var to scope
    scope.add_local(
        captured_name,
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Add closure to scope as i64-returning
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Generate assertions with pre-computed expected values
    let test_a = emit.gen_i64_range(1, 20);

    // classify(test_a, true) == base_val + test_a
    let expected_true = base_val + test_a;
    let assert_true = format!(
        "assert({}({}, true) == {})",
        closure_name, test_a, expected_true,
    );

    // classify(test_a, false) == base_val - test_a
    let expected_false = base_val - test_a;
    let assert_false = format!(
        "assert({}({}, false) == {})",
        closure_name, test_a, expected_false,
    );

    // classify(0, true) == base_val
    let assert_zero = format!("assert({}(0, true) == {})", closure_name, base_val,);

    Some(format!(
        "{}\n{}{}\n{}{}\n{}{}",
        closure_def, indent, assert_true, indent, assert_false, indent, assert_zero,
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
    use crate::symbols::{ModuleId, SymbolTable};
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
        assert_eq!(MatchWhenClosure.name(), "match_when_closure");
    }

    #[test]
    fn precondition_requires_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!MatchWhenClosure.precondition(&scope, &params));

        // With module_id => precondition passes
        scope.module_id = Some(ModuleId(0));
        assert!(MatchWhenClosure.precondition(&scope, &params));
    }

    #[test]
    fn generates_match_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MatchWhenClosure
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains("match y {") {
                assert!(
                    text.contains("(y: i64) -> string =>"),
                    "expected match closure signature, got: {text}"
                );
                assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
                assert!(text.contains("assert("), "expected assertions, got: {text}");
                found = true;
                break;
            }
        }
        assert!(found, "never generated match variant in 100 seeds");
    }

    #[test]
    fn generates_when_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MatchWhenClosure
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains("when {") {
                assert!(
                    text.contains("(n: i64) -> string =>"),
                    "expected when closure signature, got: {text}"
                );
                assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
                // Should have 3 assertions for when variant
                let assert_count = text.matches("assert(").count();
                assert!(
                    assert_count == 3,
                    "expected 3 assertions for when variant, got {assert_count}: {text}"
                );
                found = true;
                break;
            }
        }
        assert!(found, "never generated when variant in 100 seeds");
    }

    #[test]
    fn generates_nested_match_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MatchWhenClosure
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains("match b {") {
                assert!(
                    text.contains("(a: i64, b: bool) -> i64 =>"),
                    "expected nested match closure signature, got: {text}"
                );
                assert!(
                    text.contains("match a {"),
                    "expected inner match on a, got: {text}"
                );
                // Should have 3 assertions for nested match variant
                let assert_count = text.matches("assert(").count();
                assert!(
                    assert_count == 3,
                    "expected 3 assertions for nested match variant, got {assert_count}: {text}"
                );
                found = true;
                break;
            }
        }
        assert!(found, "never generated nested match variant in 100 seeds");
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_match = false;
        let mut found_when = false;
        let mut found_nested = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MatchWhenClosure
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if text.contains("match y {") {
                found_match = true;
            } else if text.contains("when {") {
                found_when = true;
            } else if text.contains("match b {") {
                found_nested = true;
            }

            if found_match && found_when && found_nested {
                break;
            }
        }

        assert!(found_match, "never generated match variant in 200 seeds");
        assert!(found_when, "never generated when variant in 200 seeds");
        assert!(
            found_nested,
            "never generated nested match variant in 200 seeds"
        );
    }

    #[test]
    fn adds_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MatchWhenClosure.generate(&mut scope, &mut emit, &test_params());
        // Each variant adds: captured var + closure = 2 locals
        assert_eq!(
            scope.locals.len(),
            initial_len + 2,
            "expected 2 new locals (captured var + closure), got {} total (started with {})",
            scope.locals.len(),
            initial_len,
        );
    }

    #[test]
    fn match_arms_have_trailing_commas() {
        let table = SymbolTable::new();
        for seed in 0..30 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MatchWhenClosure
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Every result arm line (containing "=>") inside match/when should end
            // with a comma. Lines opening a nested match/when are excluded.
            for line in text.lines() {
                let trimmed = line.trim();
                if trimmed.contains("=>")
                    && !trimmed.starts_with("let")
                    && !trimmed.starts_with("assert")
                    && !trimmed.ends_with('{')
                {
                    assert!(
                        trimmed.ends_with(','),
                        "seed {seed}: arm should end with comma: {trimmed}"
                    );
                }
            }
        }
    }

    #[test]
    fn string_interpolation_uses_captured_var() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MatchWhenClosure
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Variant 1 and 2 use string interpolation with captured var
            if text.contains("match y {") || text.contains("when {") {
                // Should contain {local...} interpolation syntax
                assert!(
                    text.contains("{local"),
                    "seed {seed}: expected string interpolation with captured var, got: {text}"
                );
                found = true;
                break;
            }
        }
        assert!(found, "never found a string-interpolation variant");
    }
}
