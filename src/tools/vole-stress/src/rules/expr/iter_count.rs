//! Rule: iterator count expression.
//!
//! Generates `arrVar.iter().count()` or `arrVar.iter().filter(...).count()`
//! when an array-typed variable is in scope. Result type is `i64`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterCount;

impl ExprRule for IterCount {
    fn name(&self) -> &'static str {
        "iter_count"
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
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            return None;
        }

        let array_vars = scope.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (var_name, elem_ty) = &array_vars[idx];

        // ~40% chance to chain a .filter() before .count()
        if emit.gen_bool(0.4) {
            if let Some(pred) = gen_predicate(emit, elem_ty) {
                return Some(format!(
                    "{}.iter().filter((x) => {}).count()",
                    var_name, pred
                ));
            }
        }

        Some(format!("{}.iter().count()", var_name))
    }
}

fn gen_predicate(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}", n))
        }
        TypeInfo::Primitive(PrimitiveType::F64) => {
            let n = emit.gen_i64_range(0, 50);
            Some(format!("x > {}.0", n))
        }
        TypeInfo::Primitive(PrimitiveType::I32) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}", n))
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
        assert_eq!(IterCount.name(), "iter_count");
    }

    #[test]
    fn generates_count_with_array() {
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

        let result = IterCount.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "expected iter, got: {text}");
        assert!(text.contains(".count()"), "expected count, got: {text}");
    }
}
