//! Rule: iterator flat_map+collect expression.
//!
//! Generates `arr.iter().flat_map((x) => [x, expr]).collect()` for
//! i64 and i32 array types. Optionally chains `.filter()` after
//! flat_map.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterFlatMapCollect;

impl ExprRule for IterFlatMapCollect {
    fn name(&self) -> &'static str {
        "iter_flat_map_collect"
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
        let target_elem = match expected_type {
            TypeInfo::Array(inner) => inner.as_ref(),
            _ => return None,
        };

        let is_i64 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I64));
        let is_i32 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I32));
        if !is_i64 && !is_i32 {
            return None;
        }

        let array_vars = scope.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        let (body_elems, suffix) = gen_flat_map_body(emit, is_i32);

        Some(format!(
            "{}.iter().flat_map((x) => [{}]){}.collect()",
            var_name, body_elems, suffix
        ))
    }
}

fn gen_flat_map_body(emit: &mut Emit, is_i32: bool) -> (String, String) {
    if is_i32 {
        match emit.gen_range(0..10) {
            0..4 => ("x, x * 2_i32".to_string(), String::new()),
            4..6 => ("x, -x".to_string(), String::new()),
            6..8 => ("x".to_string(), String::new()),
            _ => {
                let n = emit.gen_i64_range(0, 5);
                (
                    "x, x * 2_i32".to_string(),
                    format!(".filter((y) => y > {}_i32)", n),
                )
            }
        }
    } else {
        match emit.gen_range(0..10) {
            0..4 => ("x, x * 2".to_string(), String::new()),
            4..6 => ("x, -x".to_string(), String::new()),
            6..8 => ("x".to_string(), String::new()),
            _ => {
                let n = emit.gen_i64_range(0, 5);
                ("x, x * 2".to_string(), format!(".filter((y) => y > {})", n))
            }
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
        assert_eq!(IterFlatMapCollect.name(), "iter_flat_map_collect");
    }

    #[test]
    fn generates_flat_map_collect() {
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

        let result = IterFlatMapCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".flat_map("),
            "expected flat_map, got: {text}"
        );
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }

    #[test]
    fn returns_none_for_string_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterFlatMapCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        );
        assert!(result.is_none());
    }
}
