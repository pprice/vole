//! Rule: closures containing `when` expressions inside iterator chains.
//!
//! Picks a random i64 array variable from scope and generates
//! `.iter().map(...)` with a closure whose body is a `when` expression,
//! then collects the result.
//!
//! **Pattern A -- i64 arithmetic (i64 -> i64):**
//! ```vole
//! let result = arr.iter().map((x: i64) => when {
//!     x > 3 => x * 2
//!     _ => x
//! }).collect()
//! ```
//!
//! **Pattern B -- string literals (i64 -> string):**
//! ```vole
//! let result = arr.iter().map((x: i64) => when {
//!     x % 2 == 0 => "even"
//!     _ => "odd"
//! }).collect()
//! ```
//!
//! **Pattern C -- string interpolation (i64 -> string):**
//! ```vole
//! let result = arr.iter().map((x: i64) => when {
//!     x > 15 => "big:{x}"
//!     _ => "small:{x}"
//! }).collect()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureWhenIter;

impl StmtRule for ClosureWhenIter {
    fn name(&self) -> &'static str {
        "closure_when_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Find i64 array variables in scope.
        let array_candidates: Vec<String> = scope
            .vars_matching(|v| {
                matches!(
                    &v.type_info,
                    TypeInfo::Array(elem)
                        if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .into_iter()
            .map(|v| v.name)
            .collect();

        if array_candidates.is_empty() {
            return None;
        }

        let arr_idx = emit.gen_range(0..array_candidates.len());
        let arr_name = &array_candidates[arr_idx];

        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_i64_arithmetic(scope, emit, arr_name),
            1 => emit_string_literals(scope, emit, arr_name),
            _ => emit_string_interpolation(scope, emit, arr_name),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant A: i64 -> i64 (arithmetic in when arms)
// ---------------------------------------------------------------------------

fn emit_i64_arithmetic(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    let threshold = emit.random_in(1, 10);
    let op = ["<", ">", ">=", "<="][emit.gen_range(0..4)];
    let multiplier = emit.random_in(2, 5);
    let offset = emit.random_in(1, 10);

    let cond_body = match emit.gen_range(0..3) {
        0 => format!("x * {}", multiplier),
        1 => format!("x + {}", offset),
        _ => format!("x * {} + {}", multiplier, offset),
    };

    let default_body = match emit.gen_range(0..3) {
        0 => "x".to_string(),
        1 => format!("x + {}", emit.random_in(1, 5)),
        _ => format!("x * {}", emit.random_in(1, 3)),
    };

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    Some(format!(
        "let {} = {}.iter().map((x: i64) => when {{\n{}x {} {} => {}\n{}_ => {}\n{}}}).collect()",
        result_name,
        arr_name,
        inner_indent,
        op,
        threshold,
        cond_body,
        inner_indent,
        default_body,
        indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant B: i64 -> string (string literals in when arms)
// ---------------------------------------------------------------------------

fn emit_string_literals(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    let (condition, true_label, false_label) = match emit.gen_range(0..3) {
        0 => {
            let threshold = emit.random_in(1, 10);
            (format!("x > {}", threshold), "big", "small")
        }
        1 => ("x % 2 == 0".to_string(), "even", "odd"),
        _ => {
            let threshold = emit.random_in(1, 10);
            (format!("x < {}", threshold), "low", "high")
        }
    };

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    Some(format!(
        "let {} = {}.iter().map((x: i64) => when {{\n{}{} => \"{}\"\n{}_ => \"{}\"\n{}}}).collect()",
        result_name,
        arr_name,
        inner_indent,
        condition,
        true_label,
        inner_indent,
        false_label,
        indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant C: i64 -> string (interpolation in when arms)
// ---------------------------------------------------------------------------

fn emit_string_interpolation(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let indent = emit.indent_str();
    let inner_indent = format!("{}    ", indent);

    let (condition, true_prefix, false_prefix) = match emit.gen_range(0..3) {
        0 => {
            let threshold = emit.random_in(5, 20);
            (format!("x > {}", threshold), "big", "small")
        }
        1 => ("x % 2 == 0".to_string(), "even", "odd"),
        _ => {
            let threshold = emit.random_in(1, 10);
            (format!("x >= {}", threshold), "high", "low")
        }
    };

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    Some(format!(
        "let {} = {}.iter().map((x: i64) => when {{\n{}{} => \"{}:{{x}}\"\n{}_ => \"{}:{{x}}\"\n{}}}).collect()",
        result_name,
        arr_name,
        inner_indent,
        condition,
        true_prefix,
        inner_indent,
        false_prefix,
        indent,
    ))
}

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
        assert_eq!(ClosureWhenIter.name(), "closure_when_iter");
    }

    #[test]
    fn returns_none_without_i64_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Only an i64 scalar, no array.
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ClosureWhenIter
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_i64_array_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureWhenIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".iter().map("),
            "expected iter().map(), got: {text}"
        );
        assert!(
            text.contains("when {"),
            "expected when expression, got: {text}"
        );
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
        assert!(
            text.contains(".collect()"),
            "expected .collect(), got: {text}"
        );
    }

    #[test]
    fn adds_result_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureWhenIter.generate(&mut scope, &mut emit, &params);
        // Should add 1 local: the result variable.
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_i64 = false;
        let mut found_string_literal = false;
        let mut found_interpolation = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local(
                "nums".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureWhenIter.generate(&mut scope, &mut emit, &params) {
                if text.contains("(x: i64) => when") && !text.contains('"') {
                    found_i64 = true;
                } else if text.contains(":{x}") {
                    found_interpolation = true;
                } else if text.contains('"') && !text.contains(":{x}") {
                    found_string_literal = true;
                }
            }
        }
        assert!(found_i64, "never generated i64 arithmetic variant");
        assert!(
            found_string_literal,
            "never generated string literal variant"
        );
        assert!(
            found_interpolation,
            "never generated string interpolation variant"
        );
    }

    #[test]
    fn result_type_is_array() {
        let table = SymbolTable::new();

        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local(
                "data".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if ClosureWhenIter
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                // The added local should be an array type.
                let (_, ref ty, _) = scope.locals[scope.locals.len() - 1];
                assert!(
                    matches!(ty, TypeInfo::Array(_)),
                    "expected array type, got: {ty:?}"
                );
            }
        }
    }

    #[test]
    fn uses_array_variable_name() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "my_items".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureWhenIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("my_items.iter()"),
            "expected array name in chain, got: {text}"
        );
    }
}
