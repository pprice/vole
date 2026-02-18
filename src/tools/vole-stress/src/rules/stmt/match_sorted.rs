//! Rule: match on sorted array length.
//!
//! Picks a numeric array parameter, sorts it, collects, and matches on `.length()`:
//! ```vole
//! let result = match arr.iter().sorted().collect().length() {
//!     0 => "empty", 1 => "one", _ => "many"
//! }
//! ```

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchSorted;

impl StmtRule for MatchSorted {
    fn name(&self) -> &'static str {
        "match_sorted"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params = collect_numeric_array_params(scope);
        if array_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_params.len());
        let arr = &array_params[idx];
        let name = scope.fresh_name();

        let mut used = HashSet::new();
        let mut arms = Vec::new();
        let labels = ["\"empty\"", "\"one\"", "\"two\"", "\"few\""];
        let num_arms = emit.random_in(2, 3);
        for i in 0..num_arms {
            let v = i as i64;
            if used.insert(v) {
                arms.push(format!("{} => {}", v, labels[i.min(labels.len() - 1)]));
            }
        }
        arms.push("_ => \"many\"".to_string());

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {}.iter().sorted().collect().length() {{ {} }}",
            name,
            arr,
            arms.join(", ")
        ))
    }
}

fn collect_numeric_array_params(scope: &Scope) -> Vec<String> {
    scope
        .params
        .iter()
        .filter_map(|p| match &p.param_type {
            TypeInfo::Array(inner) => match inner.as_ref() {
                TypeInfo::Primitive(
                    PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64,
                ) => Some(p.name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect()
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
        assert_eq!(MatchSorted.name(), "match_sorted");
    }

    #[test]
    fn returns_none_without_numeric_array_params() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchSorted
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_i64_array_param() {
        let table = SymbolTable::new();
        let fn_params = [ParamInfo {
            name: "nums".into(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(&fn_params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchSorted.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("nums.iter().sorted().collect().length()"),
            "got: {text}"
        );
        assert!(text.contains("\"many\""), "got: {text}");
    }
}
