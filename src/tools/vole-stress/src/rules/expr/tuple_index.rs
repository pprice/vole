//! Rule: tuple index expression.
//!
//! Generates `tupleVar[index]` for tuple-typed variables that contain
//! an element matching the expected type. Tuple indexing uses a constant
//! integer literal index (Vole requires compile-time constant indices
//! for tuples).

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;

pub struct TupleIndex;

impl ExprRule for TupleIndex {
    fn name(&self) -> &'static str {
        "tuple_index"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Tuple(..)))
            .first()
            .is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let tuple_vars = scope.vars_matching(|v| matches!(v.type_info, TypeInfo::Tuple(..)));

        // Build candidates: (var_name, index) pairs where elem type matches target
        let mut candidates: Vec<(String, usize)> = Vec::new();
        for var in &tuple_vars {
            if let TypeInfo::Tuple(ref elem_types) = var.type_info {
                for (i, elem_ty) in elem_types.iter().enumerate() {
                    if elem_ty == expected_type {
                        candidates.push((var.name.clone(), i));
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, elem_index) = &candidates[idx];
        Some(format!("{}[{}]", var_name, elem_index))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::{PrimitiveType, SymbolTable};
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
        assert_eq!(TupleIndex.name(), "tuple_index");
    }

    #[test]
    fn generates_index_for_tuple() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "tup".into(),
            TypeInfo::Tuple(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ]),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TupleIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert_eq!(text, "tup[0]");
    }

    #[test]
    fn returns_none_when_no_match() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "tup".into(),
            TypeInfo::Tuple(vec![TypeInfo::Primitive(PrimitiveType::I64)]),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TupleIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_none());
    }
}
