//! Rule: `.iter().filter_map(closure).collect()` on arrays.
//!
//! Generates `filter_map` calls that combine filtering and transformation in
//! one step. The closure returns `T?` — either a transformed value or `nil`.
//!
//! Variant 0: i64 array with modulo check (returns `x * M` or `nil`)
//! Variant 1: string array with length check (returns `s.to_upper()` or `nil`)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct FilterMapCollect;

impl StmtRule for FilterMapCollect {
    fn name(&self) -> &'static str {
        "filter_map_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem)| matches!(elem, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _)| name)
            .collect();

        let string_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem)| matches!(elem, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _)| name)
            .collect();

        let has_i64 = !i64_arrays.is_empty();
        let has_string = !string_arrays.is_empty();

        if !has_i64 && !has_string {
            return None;
        }

        // Choose variant based on what's available.
        let variant = if has_i64 && has_string {
            emit.gen_range(0..2)
        } else if has_i64 {
            0
        } else {
            1
        };

        let name = scope.fresh_name();

        match variant {
            0 => {
                // Variant 0: i64 filter_map with modulo check
                let idx = emit.gen_range(0..i64_arrays.len());
                let arr_name = &i64_arrays[idx];
                let divisor = emit.random_in(2, 5);
                let multiplier = emit.random_in(2, 10);

                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );

                Some(format!(
                    "let {name} = {arr_name}.iter().filter_map((x: i64) -> i64? => {{\n\
                     \x20   if x % {divisor} == 0 {{\n\
                     \x20       return x * {multiplier}\n\
                     \x20   }}\n\
                     \x20   return nil\n\
                     }}).collect()\n\
                     assert({name}.length() >= 0)",
                ))
            }
            _ => {
                // Variant 1: string filter_map with length check
                let idx = emit.gen_range(0..string_arrays.len());
                let arr_name = &string_arrays[idx];
                let min_len = emit.random_in(1, 3);

                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );

                Some(format!(
                    "let {name} = {arr_name}.iter().filter_map((s: string) -> string? => {{\n\
                     \x20   if s.length() > {min_len} {{\n\
                     \x20       return s.to_upper()\n\
                     \x20   }}\n\
                     \x20   return nil\n\
                     }}).collect()\n\
                     assert({name}.length() >= 0)",
                ))
            }
        }
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
        assert_eq!(FilterMapCollect.name(), "filter_map_collect");
    }

    #[test]
    fn generates_i64_filter_map() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "nums".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FilterMapCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".filter_map("),
            "expected .filter_map(...), got: {text}"
        );
        assert!(
            text.contains("-> i64?"),
            "expected return type annotation, got: {text}"
        );
        assert!(
            text.contains(".collect()"),
            "expected .collect(), got: {text}"
        );
    }

    #[test]
    fn generates_string_filter_map() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "words".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FilterMapCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".filter_map("),
            "expected .filter_map(...), got: {text}"
        );
        assert!(
            text.contains("-> string?"),
            "expected return type annotation, got: {text}"
        );
        assert!(
            text.contains(".to_upper()"),
            "expected .to_upper(), got: {text}"
        );
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            FilterMapCollect
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }

    #[test]
    fn exercises_multiple_seeds() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local(
                "nums".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            scope.add_local(
                "strs".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = FilterMapCollect.generate(&mut scope, &mut emit, &rule_params);
            assert!(result.is_some(), "seed {} returned None", seed);
            let text = result.unwrap();
            assert!(
                text.contains(".filter_map("),
                "seed {} missing .filter_map: {}",
                seed,
                text
            );
            assert!(
                text.contains(".collect()"),
                "seed {} missing .collect(): {}",
                seed,
                text
            );
        }
    }
}
