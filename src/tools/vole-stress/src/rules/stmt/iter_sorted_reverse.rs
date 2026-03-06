//! Rule: `.iter().sorted().collect()`, `.iter().reverse().collect()`,
//! `.iter().unique().collect()` and combinations thereof.
//!
//! Tests Iterable default method dispatch paths (sorted, reverse, unique).
//! Uses parameter arrays (guaranteed non-empty) for safe iteration.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterSortedReverse;

impl StmtRule for IterSortedReverse {
    fn name(&self) -> &'static str {
        "iter_sorted_reverse"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arrays = collect_i64_arrays(scope);
        if arrays.is_empty() {
            return None;
        }

        let arr_name = &arrays[emit.gen_range(0..arrays.len())];
        let name = scope.fresh_name();

        let variant = emit.gen_range(0..5);
        let code = match variant {
            0 => {
                // arr.iter().sorted().collect()
                format!("let {} = {}.iter().sorted().collect()", name, arr_name)
            }
            1 => {
                // arr.iter().reverse().collect()
                format!("let {} = {}.iter().reverse().collect()", name, arr_name)
            }
            2 => {
                // arr.iter().sorted().reverse().collect()
                format!(
                    "let {} = {}.iter().sorted().reverse().collect()",
                    name, arr_name
                )
            }
            3 => {
                // arr.iter().unique().collect()
                format!("let {} = {}.iter().unique().collect()", name, arr_name)
            }
            _ => {
                // arr.iter().sorted().take(N).collect()
                let n = emit.random_in(1, 3);
                format!(
                    "let {} = {}.iter().sorted().take({}).collect()",
                    name, arr_name, n
                )
            }
        };

        scope.add_local(
            name,
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        Some(code)
    }
}

fn collect_i64_arrays(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Array(elem) = ty {
            if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                out.push(name.clone());
            }
        }
    }
    for param in scope.params {
        if let TypeInfo::Array(elem) = &param.param_type {
            if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                out.push(param.name.clone());
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(IterSortedReverse.name(), "iter_sorted_reverse");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            IterSortedReverse
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_param_array() {
        let table = SymbolTable::new();
        let params_list = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params_list, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterSortedReverse.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()."), "got: {text}");
        assert!(
            text.contains(".sorted()") || text.contains(".reverse()") || text.contains(".unique()"),
            "got: {text}"
        );
    }

    #[test]
    fn generates_with_local_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "nums".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterSortedReverse.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
    }

    #[test]
    fn all_variants_produce_collect() {
        let table = SymbolTable::new();
        let params_list = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];

        for seed in 0..100 {
            let mut scope = Scope::new(params_list, &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = IterSortedReverse.generate(&mut scope, &mut emit, &params) {
                assert!(text.contains(".collect()"), "got: {text}");
            }
        }
    }
}
