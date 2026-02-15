//! Rule: null coalescing expression.
//!
//! Generates `optVar ?? defaultExpr` when an optional-typed variable with
//! matching inner type is in scope. Optionally chains multiple optionals.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;

pub struct NullCoalesce;

impl ExprRule for NullCoalesce {
    fn name(&self) -> &'static str {
        "null_coalesce"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.12),
            Param::prob("chain_probability", 0.30),
        ]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Optional(_)))
            .first()
            .is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        // Find optional vars whose inner type matches expected_type
        let candidates: Vec<_> = scope
            .vars_matching(|v| {
                if let TypeInfo::Optional(inner) = &v.type_info {
                    **inner == *expected_type
                } else {
                    false
                }
            })
            .into_iter()
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let first_var = &candidates[idx].name;

        let chain_prob = params.prob("chain_probability");
        if candidates.len() >= 2 && emit.gen_bool(chain_prob) {
            // Chain: optA ?? optB ?? default
            let mut chain_parts = vec![first_var.clone()];
            let max_extra = (candidates.len() - 1).min(2);
            let extra_count = emit.random_in(1, max_extra);

            let mut used = std::collections::HashSet::new();
            used.insert(idx);

            for _ in 0..extra_count {
                let remaining: Vec<usize> = (0..candidates.len())
                    .filter(|i| !used.contains(i))
                    .collect();
                if remaining.is_empty() {
                    break;
                }
                let pick = emit.gen_range(0..remaining.len());
                let chosen_idx = remaining[pick];
                used.insert(chosen_idx);
                chain_parts.push(candidates[chosen_idx].name.clone());
            }

            let default_expr = emit.sub_expr(expected_type, scope);
            chain_parts.push(default_expr);
            return Some(format!("({})", chain_parts.join(" ?? ")));
        }

        let default_expr = emit.sub_expr(expected_type, scope);
        Some(format!("({} ?? {})", first_var, default_expr))
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(NullCoalesce.name(), "null_coalesce");
    }

    #[test]
    fn returns_none_without_optional_vars() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(0.0)),
        ]);

        let result = NullCoalesce.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_coalesce_with_optional_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "opt".into(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(0.0)),
        ]);

        let result = NullCoalesce.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("??"), "expected ??, got: {text}");
    }
}
