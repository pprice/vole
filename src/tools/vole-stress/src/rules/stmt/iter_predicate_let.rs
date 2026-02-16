//! Rule: iterator predicate let-binding.
//!
//! Generates `let b = arr.iter().any((x) => x > 0)` or `.all(...)` on numeric
//! array locals.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterPredicateLet;

impl StmtRule for IterPredicateLet {
    fn name(&self) -> &'static str {
        "iter_predicate_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_vars: Vec<(String, PrimitiveType)> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Array(_)))
            .into_iter()
            .filter_map(|v| {
                if let TypeInfo::Array(inner) = &v.type_info {
                    if let TypeInfo::Primitive(
                        p @ (PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64),
                    ) = inner.as_ref()
                    {
                        return Some((v.name, *p));
                    }
                }
                None
            })
            .collect();

        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let result_name = scope.fresh_name();

        let suffix = match elem_prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::F64 => "_f64",
            _ => "",
        };

        let method = if emit.gen_bool(0.5) { "any" } else { "all" };
        let threshold = emit.random_in(0, 5);
        let op = match emit.gen_range(0..3) {
            0 => ">",
            1 => "<",
            _ => ">=",
        };

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!(
            "let {} = {}.iter().{}((x) => x {} {}{})",
            result_name, arr_name, method, op, threshold, suffix
        ))
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
        assert_eq!(IterPredicateLet.name(), "iter_predicate_let");
    }

    #[test]
    fn generates_predicate() {
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
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterPredicateLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".any(") || text.contains(".all("),
            "got: {text}"
        );
    }
}
