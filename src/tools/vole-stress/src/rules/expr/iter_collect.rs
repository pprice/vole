//! Rule: iterator collect expressions.
//!
//! Generates array-producing iterator chains:
//! - `arr.iter().skip(N).take(M).collect()`
//! - `arr.iter().sorted().collect()`
//! - `arr.iter().filter((x) => pred).collect()`
//! - `arr.iter().unique().collect()`
//!
//! Target type must be `[T]` where `T` matches an existing array var element.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterCollect;

impl ExprRule for IterCollect {
    fn name(&self) -> &'static str {
        "iter_collect"
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
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // Pick a chain variant
        match emit.gen_range(0..5_usize) {
            0 => {
                // skip+take
                let skip = emit.gen_i64_range(0, 1);
                let take = emit.gen_i64_range(1, 2);
                Some(format!(
                    "{}.iter().skip({}).take({}).collect()",
                    var_name, skip, take
                ))
            }
            1 => {
                // take only
                let take = emit.gen_i64_range(1, 3);
                Some(format!("{}.iter().take({}).collect()", var_name, take))
            }
            2 => {
                // sorted (only for integer types)
                if matches!(
                    target_elem,
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                ) {
                    if emit.gen_bool(0.3) {
                        Some(format!("{}.iter().sorted().reverse().collect()", var_name))
                    } else {
                        Some(format!("{}.iter().sorted().collect()", var_name))
                    }
                } else {
                    Some(format!("{}.iter().collect()", var_name))
                }
            }
            3 => {
                // filter
                if let Some(pred) = gen_filter_pred(emit, target_elem) {
                    Some(format!(
                        "{}.iter().filter((x) => {}).collect()",
                        var_name, pred
                    ))
                } else {
                    Some(format!("{}.iter().collect()", var_name))
                }
            }
            _ => {
                // unique (integer types)
                if matches!(
                    target_elem,
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                ) {
                    Some(format!("{}.iter().unique().collect()", var_name))
                } else {
                    Some(format!("{}.iter().collect()", var_name))
                }
            }
        }
    }
}

fn gen_filter_pred(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}", n))
        }
        TypeInfo::Primitive(PrimitiveType::I32) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}_i32", n))
        }
        TypeInfo::Primitive(PrimitiveType::F64) => {
            let n = emit.gen_i64_range(0, 50);
            Some(format!("x > {}.0", n))
        }
        TypeInfo::Primitive(PrimitiveType::Bool) => Some("x".to_string()),
        TypeInfo::Primitive(PrimitiveType::String) => {
            let n = emit.gen_i64_range(0, 3);
            Some(format!("x.length() > {}", n))
        }
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(IterCollect.name(), "iter_collect");
    }

    #[test]
    fn generates_collect_for_array() {
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

        let result = IterCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "expected iter, got: {text}");
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }

    #[test]
    fn returns_none_for_non_array() {
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

        let result = IterCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
