//! Rule: match on sorted array length.
//!
//! Generates `match arr.iter().sorted().collect().length() { 0 => "empty", _ => "has items" }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchSortedLength;

impl StmtRule for MatchSortedLength {
    fn name(&self) -> &'static str {
        "match_sorted_length"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<String> = scope
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
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let arr = &array_params[emit.gen_range(0..array_params.len())];
        let name = scope.fresh_name();

        let mut used = std::collections::HashSet::new();
        let mut arms = Vec::new();
        let labels = ["\"empty\"", "\"one\"", "\"two\"", "\"few\""];
        for i in 0..emit.random_in(2, 3) {
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
        assert_eq!(MatchSortedLength.name(), "match_sorted_length");
    }

    #[test]
    fn generates_match() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchSortedLength.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "got: {text}");
        assert!(text.contains(".sorted()"), "got: {text}");
    }
}
