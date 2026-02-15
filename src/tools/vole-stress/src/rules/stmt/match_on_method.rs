//! Rule: match on method call result (small variant).
//!
//! Generates match on `str.length()`, `num.to_string()`, or `str.trim()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchOnMethod;

impl StmtRule for MatchOnMethod {
    fn name(&self) -> &'static str {
        "match_on_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let result_name = scope.fresh_name();

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

        let i64_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::I64)))
            .into_iter()
            .map(|v| v.name)
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() && i64_vars.is_empty() {
            return None;
        }

        let variant = emit.gen_range(0..3);
        match variant {
            0 if !string_vars.is_empty() => {
                let var = &string_vars[emit.gen_range(0..string_vars.len())];
                let val0 = emit.gen_i64_range(-5, 5);
                let val_default = emit.gen_i64_range(-5, 5);
                let arm_len = emit.gen_i64_range(0, 10);
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = match {}.length() {{ {} => {}, _ => {} }}",
                    result_name, var, arm_len, val0, val_default
                ))
            }
            1 if !i64_vars.is_empty() => {
                let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
                let strs = ["\"0\"", "\"1\"", "\"-1\"", "\"42\""];
                let arm_str = strs[emit.gen_range(0..strs.len())];
                let val_true = emit.gen_i64_range(-10, 10);
                let val_false = emit.gen_i64_range(-10, 10);
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = match {}.to_string() {{ {} => {}, _ => {} }}",
                    result_name, var, arm_str, val_true, val_false
                ))
            }
            _ if !string_vars.is_empty() => {
                let var = &string_vars[emit.gen_range(0..string_vars.len())];
                let method = match emit.gen_range(0..3) {
                    0 => "trim",
                    1 => "to_lower",
                    _ => "to_upper",
                };
                let match_str = match emit.gen_range(0..3) {
                    0 => "\"\"",
                    1 => "\"hello\"",
                    _ => "\"test\"",
                };
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = match {}.{}() {{ {} => true, _ => false }}",
                    result_name, var, method, match_str
                ))
            }
            _ => None,
        }
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchOnMethod.name(), "match_on_method");
    }

    #[test]
    fn generates_match_on_string() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "s".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchOnMethod.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "got: {text}");
    }
}
