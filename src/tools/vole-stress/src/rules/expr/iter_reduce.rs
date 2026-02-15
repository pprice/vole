//! Rule: iterator reduce expression.
//!
//! Generates `.iter().reduce()` expressions:
//! - `i64` from `[i64]`: `arr.iter().reduce(0, (acc, x) => acc + x)`
//! - `string` from `[string]`: `arr.iter().reduce("", (acc, x) => acc + x + " ")`
//! - `string` from `[i64]`: map-then-reduce

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterReduce;

impl ExprRule for IterReduce {
    fn name(&self) -> &'static str {
        "iter_reduce"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.06)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.array_vars().is_empty()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let array_vars = scope.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| match expected_type {
                TypeInfo::Primitive(PrimitiveType::I64) => {
                    matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64))
                }
                TypeInfo::Primitive(PrimitiveType::String) => {
                    matches!(
                        elem_ty,
                        TypeInfo::Primitive(PrimitiveType::String | PrimitiveType::I64)
                    )
                }
                _ => false,
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        match (expected_type, elem_ty) {
            (TypeInfo::Primitive(PrimitiveType::I64), TypeInfo::Primitive(PrimitiveType::I64)) => {
                Some(format!(
                    "{}.iter().reduce(0, (acc, x) => acc + x)",
                    var_name
                ))
            }
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::String),
            ) => Some(format!(
                "{}.iter().reduce(\"\", (acc, x) => acc + x + \" \")",
                var_name
            )),
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::I64),
            ) => Some(format!(
                "{}.iter().map((x) => \"\" + x).reduce(\"\", (acc, s) => acc + s + \",\")",
                var_name
            )),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(IterReduce.name(), "iter_reduce");
    }

    #[test]
    fn generates_reduce_i64() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterReduce.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".reduce("), "expected reduce, got: {text}");
    }
}
