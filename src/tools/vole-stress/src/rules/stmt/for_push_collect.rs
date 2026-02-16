//! Rule: for-in loop pushing derived values to a mutable array.
//!
//! Generates `let mut result: [i64] = []; for item in arr.iter() { result.push(transform) }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForPushCollect;

impl StmtRule for ForPushCollect {
    fn name(&self) -> &'static str {
        "for_push_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_arrays: Vec<String> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner)
                    if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) =>
                {
                    Some(p.name.clone())
                }
                _ => None,
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let source_name = &i64_arrays[emit.gen_range(0..i64_arrays.len())];
        let result_name = scope.fresh_name();
        let iter_name = scope.fresh_name();

        let transform = build_transform(emit, &iter_name);

        scope.add_local(
            result_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            true,
        );
        scope.protected_vars.push(result_name.clone());

        let indent = emit.indent_str();
        let inner = format!("{}    ", indent);

        Some(format!(
            "let mut {}: [i64] = []\n\
             {}for {} in {}.iter() {{\n\
             {}{}.push({})\n\
             {}}}",
            result_name, indent, iter_name, source_name, inner, result_name, transform, indent,
        ))
    }
}

/// Build a transformation expression for the loop body.
fn build_transform(emit: &mut Emit, iter_name: &str) -> String {
    match emit.gen_range(0..3) {
        0 => {
            let mult = emit.random_in(2, 5);
            let add = emit.random_in(0, 10);
            format!("{} * {} + {}", iter_name, mult, add)
        }
        1 => {
            let add = emit.random_in(1, 20);
            format!("{} + {}", iter_name, add)
        }
        _ => {
            format!(
                "when {{ {} > 0 => {}, _ => 0 - {} }}",
                iter_name, iter_name, iter_name
            )
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
        assert_eq!(ForPushCollect.name(), "for_push_collect");
    }

    #[test]
    fn generates_for_push() {
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

        let result = ForPushCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains(".push("), "got: {text}");
    }
}
