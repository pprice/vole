//! Rule: match on array element.
//!
//! Finds an i64/i32 array parameter and generates a match on `arr[0]`
//! with 2 literal pattern arms and a wildcard arm.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchArrayElem;

impl StmtRule for MatchArrayElem {
    fn name(&self) -> &'static str {
        "match_array_elem"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Only use parameter arrays (guaranteed non-empty by generator).
        let array_vars: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Array(inner) = &p.param_type {
                    if let TypeInfo::Primitive(pr) = inner.as_ref() {
                        if matches!(pr, PrimitiveType::I64 | PrimitiveType::I32) {
                            return Some((p.name.clone(), *pr));
                        }
                    }
                }
                None
            })
            .collect();

        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();
        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        let lit1 = emit.literal(&TypeInfo::Primitive(elem_prim));
        let lit2 = emit.literal(&TypeInfo::Primitive(elem_prim));
        let arm_val1 = emit.literal(&result_type);
        let arm_val2 = emit.literal(&result_type);
        let wildcard_val = emit.literal(&result_type);

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {}[0] {{\n\
             {}{} => {}\n\
             {}{} => {}\n\
             {}_ => {}\n\
             {}}}",
            result_name,
            arr_name,
            inner_indent,
            lit1,
            arm_val1,
            inner_indent,
            lit2,
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
        assert_eq!(MatchArrayElem.name(), "match_array_elem");
    }

    #[test]
    fn generates_match_on_elem() {
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

        let result = MatchArrayElem.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match arr[0]"), "got: {text}");
    }
}
