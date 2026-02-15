//! Rule: sorted + accumulation loop.
//!
//! Generates `let sorted = arr.iter().sorted().collect(); let mut acc = 0; for x in sorted.iter() { acc = acc + x }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SortedIterAccum;

impl StmtRule for SortedIterAccum {
    fn name(&self) -> &'static str {
        "sorted_iter_accum"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|param| match &param.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                        Some((param.name.clone(), *prim))
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
        let (arr_name, elem_prim) = &array_params[idx];
        let sorted_name = scope.fresh_name();
        let acc_name = scope.fresh_name();
        let iter_var = scope.fresh_name();
        let indent = emit.indent_str();

        let zero = if *elem_prim == PrimitiveType::I32 {
            "0_i32"
        } else {
            "0"
        };

        let arr_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(*elem_prim)));
        scope.add_local(sorted_name.clone(), arr_type, false);
        scope.protected_vars.push(acc_name.clone());
        scope.add_local(acc_name.clone(), TypeInfo::Primitive(*elem_prim), true);

        Some(format!(
            "let {} = {}.iter().sorted().collect()\n\
             {}let mut {} = {}\n\
             {}for {} in {}.iter() {{\n\
             {}    {} = {} + {}\n\
             {}}}",
            sorted_name,
            arr_name,
            indent,
            acc_name,
            zero,
            indent,
            iter_var,
            sorted_name,
            indent,
            acc_name,
            acc_name,
            iter_var,
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(SortedIterAccum.name(), "sorted_iter_accum");
    }

    #[test]
    fn generates_sorted_accum() {
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

        let result = SortedIterAccum.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".sorted()"), "got: {text}");
        assert!(text.contains("for"), "got: {text}");
    }
}
