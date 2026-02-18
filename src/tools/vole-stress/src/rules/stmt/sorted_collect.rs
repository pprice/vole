//! Rule: sorted collect on array parameter.
//!
//! Generates `arr.iter().sorted().collect()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SortedCollect;

impl StmtRule for SortedCollect {
    fn name(&self) -> &'static str {
        "sorted_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let numeric_arrays: Vec<(String, TypeInfo)> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem_ty)| {
                matches!(
                    elem_ty,
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                )
            })
            .collect();

        if numeric_arrays.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..numeric_arrays.len());
        let (arr_name, elem_ty) = &numeric_arrays[idx];
        let name = scope.fresh_name();
        let arr_type = TypeInfo::Array(Box::new(elem_ty.clone()));

        scope.add_local(name.clone(), arr_type, false);
        Some(format!(
            "let {} = {}.iter().sorted().collect()",
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
        assert_eq!(SortedCollect.name(), "sorted_collect");
    }

    #[test]
    fn generates_sorted() {
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

        let result = SortedCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".sorted().collect()"), "got: {text}");
    }
}
