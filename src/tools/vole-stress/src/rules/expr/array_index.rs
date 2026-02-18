//! Rule: array index expression.
//!
//! Generates `arrVar[0_i64]` on parameter arrays (guaranteed non-empty).
//! Uses index 0 to stay within bounds. Only parameters are used because
//! local arrays from `.iter().collect()` or similar may be empty.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct ArrayIndex;

impl ExprRule for ArrayIndex {
    fn name(&self) -> &'static str {
        "array_index"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Only use parameter arrays (guaranteed non-empty by the test harness).
        scope
            .params
            .iter()
            .any(|p| matches!(p.param_type, TypeInfo::Array(_)))
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

        // Only use parameter arrays (guaranteed non-empty).
        let target = TypeInfo::Primitive(prim);
        let candidates: Vec<_> = scope
            .params
            .iter()
            .filter(|p| {
                if let TypeInfo::Array(elem) = &p.param_type {
                    **elem == target
                } else {
                    false
                }
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var_name = &candidates[idx].name;

        // Use index 0 to stay within bounds
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            _ => "_i64",
        };
        Some(format!("{}[0{}]", var_name, suffix))
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
        assert_eq!(ArrayIndex.name(), "array_index");
    }

    #[test]
    fn returns_none_without_array_vars() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ArrayIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_index_with_matching_param_array() {
        use crate::symbols::ParamInfo;
        let table = SymbolTable::new();
        let param_infos = vec![ParamInfo {
            name: "arr".into(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let scope = Scope::new(&param_infos, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ArrayIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("arr["), "expected array index, got: {text}");
    }

    #[test]
    fn returns_none_for_local_array_only() {
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

        // Local arrays should be skipped (might be empty)
        let result = ArrayIndex.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
