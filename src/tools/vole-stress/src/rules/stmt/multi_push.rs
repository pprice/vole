//! Rule: multiple push operations onto a mutable array.
//!
//! Generates `arr.push(val)` calls in sequence on an existing mutable array.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MultiPush;

impl StmtRule for MultiPush {
    fn name(&self) -> &'static str {
        "multi_push"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut_arrays: Vec<String> = scope
            .locals
            .iter()
            .filter(|(name, ty, is_mut)| {
                *is_mut
                    && !scope.protected_vars.contains(name)
                    && matches!(
                        ty,
                        TypeInfo::Array(elem) if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                    )
            })
            .map(|(name, _, _)| name.clone())
            .collect();

        if mut_arrays.is_empty() {
            return None;
        }

        let arr_name = &mut_arrays[emit.gen_range(0..mut_arrays.len())];
        let num_pushes = emit.random_in(2, 4);
        let indent = emit.indent_str();

        let mut stmts = Vec::new();
        for _ in 0..num_pushes {
            let val = emit.gen_i64_range(-50, 50);
            stmts.push(format!("{}.push({})", arr_name, val));
        }

        Some(stmts.join(&format!("\n{}", indent)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MultiPush.name(), "multi_push");
    }

    #[test]
    fn returns_none_without_mutable_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(MultiPush.generate(&mut scope, &mut emit, &params).is_none());
    }

    #[test]
    fn generates_pushes_with_mutable_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            true,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MultiPush.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".push("), "got: {text}");
    }
}
