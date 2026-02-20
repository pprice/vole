//! Rule: when expression with iterator predicate condition.
//!
//! Generates `when { arr.iter().any((x) => x > 0) => "yes", _ => "no" }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenIterPredicate;

impl StmtRule for WhenIterPredicate {
    fn name(&self) -> &'static str {
        "when_iter_predicate"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let prim_arrays: Vec<(String, PrimitiveType)> = scope
            .array_vars()
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                        return Some((name, prim));
                    }
                }
                None
            })
            .collect();

        if prim_arrays.is_empty() {
            return None;
        }

        let (arr_name, _) = &prim_arrays[emit.gen_range(0..prim_arrays.len())];
        let name = scope.fresh_name();

        let predicate = if emit.gen_bool(0.5) { "any" } else { "all" };
        let threshold = emit.gen_i64_range(0, 10);

        let (true_val, false_val, result_ty) = if emit.gen_bool(0.5) {
            let t = emit.gen_i64_range(1, 100);
            let f = emit.gen_i64_range(1, 100);
            (
                format!("{}", t),
                format!("{}", f),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else {
            (
                "\"yes\"".to_string(),
                "\"no\"".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            )
        };

        scope.add_local(name.clone(), result_ty, false);
        Some(format!(
            "let {} = when {{ {}.iter().{}((x) => x > {}) => {}, _ => {} }}",
            name, arr_name, predicate, threshold, true_val, false_val
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
        assert_eq!(WhenIterPredicate.name(), "when_iter_predicate");
    }

    #[test]
    fn generates_when() {
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

        let result = WhenIterPredicate.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(text.contains(".iter()."), "got: {text}");
    }
}
