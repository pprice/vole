//! Rule: reverse collect on array parameter.
//!
//! Generates `arr.iter().reverse().collect()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ReverseCollect;

impl StmtRule for ReverseCollect {
    fn name(&self) -> &'static str {
        "reverse_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arrays: Vec<(String, TypeInfo)> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem_ty)| {
                matches!(
                    elem_ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::String
                            | PrimitiveType::F64
                    )
                )
            })
            .collect();

        if arrays.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..arrays.len());
        let (arr_name, elem_ty) = &arrays[idx];
        let name = scope.fresh_name();
        let arr_type = TypeInfo::Array(Box::new(elem_ty.clone()));

        scope.add_local(name.clone(), arr_type, false);
        Some(format!(
            "let {} = {}.iter().reverse().collect()",
            name, arr_name
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ReverseCollect.name(), "reverse_collect");
    }

    #[test]
    fn generates_reverse() {
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

        let result = ReverseCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".reverse().collect()"), "got: {text}");
    }
}
