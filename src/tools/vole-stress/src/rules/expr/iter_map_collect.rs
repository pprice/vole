//! Rule: iterator map+collect expression.
//!
//! Generates `arr.iter().map((x) => body).collect()` where the map
//! closure transforms elements from the source type to the target type.
//!
//! Supported same-type mappings: i64->i64, f64->f64, i32->i32,
//! string->string, bool->bool.
//! Supported cross-type mappings: i64->bool, string->i64.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterMapCollect;

impl ExprRule for IterMapCollect {
    fn name(&self) -> &'static str {
        "iter_map_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
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

        let array_vars = scope.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, src_elem)| can_map_types(src_elem, target_elem))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, src_elem) = candidates[idx];

        let body = generate_map_body(emit, src_elem, target_elem)?;

        Some(format!(
            "{}.iter().map((x) => {}).collect()",
            var_name, body
        ))
    }
}

fn can_map_types(src: &TypeInfo, target: &TypeInfo) -> bool {
    use PrimitiveType::*;
    matches!(
        (src, target),
        (TypeInfo::Primitive(I64), TypeInfo::Primitive(I64))
            | (TypeInfo::Primitive(F64), TypeInfo::Primitive(F64))
            | (TypeInfo::Primitive(I32), TypeInfo::Primitive(I32))
            | (TypeInfo::Primitive(String), TypeInfo::Primitive(String))
            | (TypeInfo::Primitive(Bool), TypeInfo::Primitive(Bool))
            | (TypeInfo::Primitive(I64), TypeInfo::Primitive(Bool))
            | (TypeInfo::Primitive(String), TypeInfo::Primitive(I64))
    )
}

fn generate_map_body(emit: &mut Emit, src: &TypeInfo, target: &TypeInfo) -> Option<String> {
    use PrimitiveType::*;
    match (src, target) {
        (TypeInfo::Primitive(I64), TypeInfo::Primitive(I64)) => Some(match emit.gen_range(0..4) {
            0 => "x * 2".to_string(),
            1 => "x + 1".to_string(),
            2 => "x % 10".to_string(),
            _ => "-x".to_string(),
        }),
        (TypeInfo::Primitive(F64), TypeInfo::Primitive(F64)) => Some(match emit.gen_range(0..3) {
            0 => "x * 2.0".to_string(),
            1 => "x + 1.0".to_string(),
            _ => "-x".to_string(),
        }),
        (TypeInfo::Primitive(I32), TypeInfo::Primitive(I32)) => Some(match emit.gen_range(0..2) {
            0 => "x * 2_i32".to_string(),
            _ => "x + 1_i32".to_string(),
        }),
        (TypeInfo::Primitive(String), TypeInfo::Primitive(String)) => {
            Some(match emit.gen_range(0..3) {
                0 => "x.trim()".to_string(),
                1 => "x.to_upper()".to_string(),
                _ => "x.to_lower()".to_string(),
            })
        }
        (TypeInfo::Primitive(Bool), TypeInfo::Primitive(Bool)) => Some("!x".to_string()),
        (TypeInfo::Primitive(I64), TypeInfo::Primitive(Bool)) => Some(match emit.gen_range(0..2) {
            0 => "x > 0".to_string(),
            _ => "x % 2 == 0".to_string(),
        }),
        (TypeInfo::Primitive(String), TypeInfo::Primitive(I64)) => Some("x.length()".to_string()),
        _ => None,
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
        assert_eq!(IterMapCollect.name(), "iter_map_collect");
    }

    #[test]
    fn generates_map_collect_for_i64_array() {
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

        let result = IterMapCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter().map("), "expected map, got: {text}");
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }

    #[test]
    fn returns_none_for_non_array() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMapCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
