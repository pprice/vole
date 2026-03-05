//! Rule: iterator `.map()` with string interpolation capturing a scope variable.
//!
//! Generates patterns like:
//! ```vole
//! let result = arr.iter().map((elem: i64) => "{captured}_{elem}").collect()
//! ```
//!
//! Or with a filter prefix:
//! ```vole
//! let result = arr.iter().filter((elem: i64) => elem > 0).map((elem: i64) => "{captured}:{elem}").collect()
//! ```
//!
//! Exercises closure capture, string interpolation inside closures, and
//! iterator pipeline compilation.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterMapInterpolation;

impl StmtRule for IterMapInterpolation {
    fn name(&self) -> &'static str {
        "iter_map_interpolation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Need at least one [i64] array variable in scope.
        let i64_array_vars: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();

        if i64_array_vars.is_empty() {
            return None;
        }

        // Need at least one string variable in scope.
        let string_vars: Vec<String> = collect_string_vars(scope);
        if string_vars.is_empty() {
            return None;
        }

        // Pick the array and captured string variable.
        let arr_name = &i64_array_vars[emit.gen_range(0..i64_array_vars.len())];
        let captured_var = &string_vars[emit.gen_range(0..string_vars.len())];

        let result_name = scope.fresh_name();
        let param_name = scope.fresh_name();

        let separators = ["_", ":", "-", "="];
        let sep = separators[emit.gen_range(0..separators.len())];

        let use_filter = emit.gen_bool(0.5);

        let code = if use_filter {
            // Filter variant: .filter((p: i64) => p > N or p != 0).map((p: i64) => "...").collect()
            let filter_param = scope.fresh_name();
            let filter_cond = generate_filter_condition(emit, &filter_param);
            format!(
                "let {} = {}.iter().filter(({}: i64) => {}).map(({}: i64) => \"{{{}}}{}{{{}}}\").collect()",
                result_name,
                arr_name,
                filter_param,
                filter_cond,
                param_name,
                captured_var,
                sep,
                param_name
            )
        } else {
            // Direct map variant: .map((p: i64) => "...").collect()
            format!(
                "let {} = {}.iter().map(({}: i64) => \"{{{}}}{}{{{}}}\").collect()",
                result_name, arr_name, param_name, captured_var, sep, param_name
            )
        };

        scope.add_local(
            result_name,
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );

        Some(code)
    }
}

/// Collect all string-typed variables in scope (locals + params).
fn collect_string_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(param.name.clone());
        }
    }
    out
}

/// Generate a simple filter condition for the filter variant.
fn generate_filter_condition(emit: &mut Emit, param: &str) -> String {
    if emit.gen_bool(0.5) {
        let n = emit.gen_i64_range(-2, 5);
        format!("{} > {}", param, n)
    } else {
        format!("{} != 0", param)
    }
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
        assert_eq!(IterMapInterpolation.name(), "iter_map_interpolation");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Only a string variable, no arrays.
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            IterMapInterpolation
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn returns_none_without_strings() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Only an i64 array, no string variables.
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            IterMapInterpolation
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_array_and_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMapInterpolation.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".map("), "expected .map( in: {text}");
        assert!(text.contains("{"), "expected interpolation {{ in: {text}");
        assert!(
            text.contains(".collect()"),
            "expected .collect() in: {text}"
        );
    }

    #[test]
    fn generates_multiple_seeds_without_panic() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local(
                "nums".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            scope.add_local(
                "label".into(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = IterMapInterpolation.generate(&mut scope, &mut emit, &params);
            assert!(result.is_some(), "seed {} returned None", seed);
            let text = result.unwrap();
            assert!(
                text.starts_with("let "),
                "seed {} unexpected: {}",
                seed,
                text
            );
        }
    }
}
