//! Rule: fixed array index expression.
//!
//! Generates `fixedArrVar[index]` for fixed-array-typed variables whose
//! element type matches the expected primitive type. The index is a constant
//! within bounds of the array size.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct FixedArrayIndex;

impl ExprRule for FixedArrayIndex {
    fn name(&self) -> &'static str {
        "fixed_array_index"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.12)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::FixedArray(..)))
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
        let prim = match expected_type {
            TypeInfo::Primitive(p) => *p,
            _ => return None,
        };

        let target = TypeInfo::Primitive(prim);

        // Collect fixed-array-typed variables whose element type matches
        let fixed_array_vars: Vec<_> = scope
            .vars_matching(|v| matches!(&v.type_info, TypeInfo::FixedArray(..)))
            .into_iter()
            .filter_map(|v| match &v.type_info {
                TypeInfo::FixedArray(elem, size) if **elem == target => {
                    Some((v.name.clone(), *size))
                }
                _ => None,
            })
            .collect();

        if fixed_array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..fixed_array_vars.len());
        let (var_name, size) = &fixed_array_vars[idx];

        // Use a constant index within bounds
        let max_index = size.saturating_sub(1);
        let index = emit.random_in(0, max_index);
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64",
        };
        Some(format!("{}[{}{}]", var_name, index, suffix))
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
        assert_eq!(FixedArrayIndex.name(), "fixed_array_index");
    }

    #[test]
    fn generates_index_for_fixed_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(PrimitiveType::I64)), 5),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FixedArrayIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("arr["), "expected arr[, got: {text}");
        assert!(text.ends_with(']'), "expected ], got: {text}");
    }

    #[test]
    fn returns_none_for_non_primitive() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(PrimitiveType::I64)), 5),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FixedArrayIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_none());
    }
}
