//! Rule: match expression.
//!
//! Generates `match subject { pattern => value, _ => default }` expressions.
//! Matches on a numeric or bool subject with literal patterns and a wildcard
//! default arm. Optionally uses `unreachable` for the wildcard.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct MatchExpr;

impl ExprRule for MatchExpr {
    fn name(&self) -> &'static str {
        "match_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.10),
            Param::prob("unreachable_probability", 0.05),
            Param::count("max_arms", 4),
        ]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let unreachable_prob = params.prob("unreachable_probability");
        let max_arms = params.count("max_arms").max(2);
        let use_unreachable = emit.gen_bool(unreachable_prob);

        // Pick a subject type for matching
        let subject_prim = match emit.gen_range(0..3_usize) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            _ => PrimitiveType::Bool,
        };
        let subject_ty = TypeInfo::Primitive(subject_prim);

        let arm_count = emit.random_in(2, max_arms);
        let mut arms = Vec::new();

        if use_unreachable {
            // Generate a known literal subject and match it
            let subject_literal = emit.literal(&subject_ty);
            let first_value = emit.sub_expr(expected_type, scope);
            arms.push(format!("{} => {}", subject_literal, first_value));

            for _ in 1..arm_count - 1 {
                let pattern = emit.literal(&subject_ty);
                let value = emit.sub_expr(expected_type, scope);
                arms.push(format!("{} => {}", pattern, value));
            }

            arms.push("_ => unreachable".to_string());

            return Some(format!(
                "match {} {{ {} }}",
                subject_literal,
                arms.join(", ")
            ));
        }

        // Normal match with sub_expr subject
        let subject = emit.sub_expr(&subject_ty, scope);

        for _ in 0..arm_count - 1 {
            let pattern = emit.literal(&subject_ty);
            let value = emit.sub_expr(expected_type, scope);
            arms.push(format!("{} => {}", pattern, value));
        }

        let default_value = emit.sub_expr(expected_type, scope);
        arms.push(format!("_ => {}", default_value));

        Some(format!("match {} {{ {} }}", subject, arms.join(", ")))
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
        assert_eq!(MatchExpr.name(), "match_expr");
    }

    #[test]
    fn generates_match() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("unreachable_probability", ParamValue::Probability(0.0)),
            ("max_arms", ParamValue::Count(4)),
        ]);

        let result = MatchExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "expected match expr, got: {text}");
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
    }
}
