//! Rule: match on iterator terminal result.
//!
//! Finds an i64/i32 array parameter and generates a match on an iterator
//! terminal (.count(), .sum(), .filter().count()) with 2 literal arms
//! and a wildcard arm.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchIterTerminal;

impl StmtRule for MatchIterTerminal {
    fn name(&self) -> &'static str {
        "match_iter_terminal"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_vars: Vec<String> = scope
            .params
            .iter()
            .filter(|p| {
                if let TypeInfo::Array(inner) = &p.param_type {
                    matches!(
                        inner.as_ref(),
                        TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                    )
                } else {
                    false
                }
            })
            .map(|p| p.name.clone())
            .collect();

        if array_vars.is_empty() {
            return None;
        }

        let arr_name = array_vars[emit.gen_range(0..array_vars.len())].clone();
        let result_name = scope.fresh_name();

        let terminal = match emit.gen_range(0..3) {
            0 => ".iter().count()".to_string(),
            1 => ".iter().sum()".to_string(),
            _ => {
                let n = emit.gen_i64_range(-5, 2);
                format!(".iter().filter((x) => x > {}).count()", n)
            }
        };

        let result_type = emit.random_primitive_type();
        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        let arm_val1 = emit.literal(&result_type);
        let arm_val2 = emit.literal(&result_type);
        let wildcard_val = emit.literal(&result_type);

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {}{} {{\n\
             {}0 => {}\n\
             {}1 => {}\n\
             {}_ => {}\n\
             {}}}",
            result_name,
            arr_name,
            terminal,
            inner_indent,
            arm_val1,
            inner_indent,
            arm_val2,
            inner_indent,
            wildcard_val,
            indent,
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
        assert_eq!(MatchIterTerminal.name(), "match_iter_terminal");
    }

    #[test]
    fn generates_match_on_iter() {
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

        let result = MatchIterTerminal.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "got: {text}");
        assert!(text.contains(".iter()"), "got: {text}");
    }
}
