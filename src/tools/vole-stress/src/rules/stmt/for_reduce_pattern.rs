//! Rule: manual for-loop reduce pattern.
//!
//! Generates `let mut acc = 0; for x in arr.iter() { acc = acc + x }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForReducePattern;

impl StmtRule for ForReducePattern {
    fn name(&self) -> &'static str {
        "for_reduce_pattern"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                        Some((p.name.clone(), *prim))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_params.len());
        let (arr_name, prim) = &array_params[idx];
        let acc_name = scope.fresh_name();
        let iter_name = scope.fresh_name();

        let suffix = if matches!(prim, PrimitiveType::I32) {
            "_i32"
        } else {
            ""
        };

        scope.protected_vars.push(acc_name.clone());
        scope.add_local(acc_name.clone(), TypeInfo::Primitive(*prim), true);

        Some(format!(
            "let mut {} = 0{}\nfor {} in {}.iter() {{\n    {} = {} + {}\n}}",
            acc_name, suffix, iter_name, arr_name, acc_name, acc_name, iter_name
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
        assert_eq!(ForReducePattern.name(), "for_reduce_pattern");
    }

    #[test]
    fn generates_for_reduce() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForReducePattern.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains(".iter()"), "got: {text}");
    }
}
