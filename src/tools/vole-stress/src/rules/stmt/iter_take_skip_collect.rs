//! Rule: `.iter().take(N).collect()` or `.iter().skip(N).collect()`.
//!
//! Uses parameter arrays with known length to avoid empty-array issues.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct IterTakeSkipCollect;

impl StmtRule for IterTakeSkipCollect {
    fn name(&self) -> &'static str {
        "iter_take_skip_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<(String, TypeInfo)> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(_) => Some((p.name.clone(), p.param_type.clone())),
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_params.len());
        let (arr_name, arr_type) = &array_params[idx];
        let name = scope.fresh_name();
        let n = emit.random_in(1, 3);

        scope.add_local(name.clone(), arr_type.clone(), false);
        if emit.gen_bool(0.5) {
            Some(format!(
                "let {} = {}.iter().take({}).collect()",
                name, arr_name, n
            ))
        } else {
            Some(format!(
                "let {} = {}.iter().skip({}).collect()",
                name, arr_name, n
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, PrimitiveType, SymbolTable};
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
        assert_eq!(IterTakeSkipCollect.name(), "iter_take_skip_collect");
    }

    #[test]
    fn generates_take_or_skip() {
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

        let result = IterTakeSkipCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".take(") || text.contains(".skip("),
            "got: {text}"
        );
    }
}
