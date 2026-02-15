//! Rule: iterator sum expression.
//!
//! Generates `arrVar.iter().sum()` or with optional `.filter()`/`.map()`
//! chaining. Works for `i64` and `f64` target types.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterSum;

impl ExprRule for IterSum {
    fn name(&self) -> &'static str {
        "iter_sum"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
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
        let target_prim = match expected_type {
            TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::F64)) => *p,
            _ => return None,
        };

        let array_vars = scope.array_vars();
        let target_ty = TypeInfo::Primitive(target_prim);
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| *elem_ty == target_ty)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // ~30% chance: chain a .filter() before .sum()
        if emit.gen_bool(0.3) {
            let pred = match target_prim {
                PrimitiveType::I64 => {
                    let n = emit.gen_i64_range(0, 5);
                    format!("x > {}", n)
                }
                PrimitiveType::F64 => {
                    let n = emit.gen_i64_range(0, 10);
                    format!("x > {}.0", n)
                }
                _ => return Some(format!("{}.iter().sum()", var_name)),
            };
            return Some(format!("{}.iter().filter((x) => {}).sum()", var_name, pred));
        }

        // ~20% chance: chain a .map() before .sum()
        if emit.gen_bool(0.2) {
            let body = match target_prim {
                PrimitiveType::I64 => match emit.gen_range(0..3_usize) {
                    0 => "x * 2",
                    1 => "x + 1",
                    _ => "-x",
                },
                PrimitiveType::F64 => match emit.gen_range(0..2_usize) {
                    0 => "x * 2.0",
                    _ => "x + 1.0",
                },
                _ => return Some(format!("{}.iter().sum()", var_name)),
            };
            return Some(format!("{}.iter().map((x) => {}).sum()", var_name, body));
        }

        Some(format!("{}.iter().sum()", var_name))
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
        assert_eq!(IterSum.name(), "iter_sum");
    }

    #[test]
    fn generates_sum_with_i64_array() {
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

        let result = IterSum.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "expected iter, got: {text}");
    }

    #[test]
    fn returns_none_for_non_numeric() {
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

        let result = IterSum.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_none());
    }
}
