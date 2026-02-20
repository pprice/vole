//! Rule: chained string method calls.
//!
//! Generates `str.to_upper().to_lower().length()` or similar chains.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ChainedStringMethods;

impl StmtRule for ChainedStringMethods {
    fn name(&self) -> &'static str {
        "chained_string_methods"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .into_iter()
            .map(|v| v.name)
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let str_name = &string_vars[emit.gen_range(0..string_vars.len())];
        let result_name = scope.fresh_name();

        let transforms = [".to_upper()", ".to_lower()", ".trim()"];
        let chain_len = emit.random_in(2, 3);
        let mut chain = String::new();
        for _ in 0..chain_len {
            chain.push_str(transforms[emit.gen_range(0..transforms.len())]);
        }

        let (terminal, result_type) = match emit.gen_range(0..3) {
            0 => (
                ".length()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            1 => (
                ".contains(\"a\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            _ => (String::new(), TypeInfo::Primitive(PrimitiveType::String)),
        };

        scope.add_local(result_name.clone(), result_type, false);
        Some(format!(
            "let {} = {}{}{}",
            result_name, str_name, chain, terminal
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
        assert_eq!(ChainedStringMethods.name(), "chained_string_methods");
    }

    #[test]
    fn generates_chain() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "s".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ChainedStringMethods.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".to_upper()")
                || text.contains(".to_lower()")
                || text.contains(".trim()"),
            "got: {text}"
        );
    }
}
