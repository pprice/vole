//! Rule: multi-arm when expression.
//!
//! Generates a when expression with 2-4 arms. Optionally uses `unreachable`
//! in the wildcard arm when one preceding condition is guaranteed true.
//! Works for any expected type.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct WhenExpr;

impl ExprRule for WhenExpr {
    fn name(&self) -> &'static str {
        "when_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.12),
            Param::prob("unreachable_probability", 0.05),
            Param::prob("multi_arm_probability", 0.35),
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
        let multi_arm_prob = params.prob("multi_arm_probability");

        let use_unreachable = emit.gen_bool(unreachable_prob);
        let arm_count = if emit.gen_bool(multi_arm_prob) {
            emit.random_in(3, 4)
        } else {
            2
        };

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let mut arms = Vec::new();

        if use_unreachable {
            let value = emit.sub_expr(expected_type, scope);
            arms.push(format!("true => {}", value));

            for _ in 1..arm_count - 1 {
                let cond = emit.sub_expr(&bool_ty, scope);
                let arm_value = emit.sub_expr(expected_type, scope);
                arms.push(format!("{} => {}", cond, arm_value));
            }

            arms.push("_ => unreachable".to_string());
        } else {
            for _ in 0..arm_count - 1 {
                let cond = emit.sub_expr(&bool_ty, scope);
                let value = emit.sub_expr(expected_type, scope);
                arms.push(format!("{} => {}", cond, value));
            }

            let default_value = emit.sub_expr(expected_type, scope);
            arms.push(format!("_ => {}", default_value));
        }

        Some(format!("when {{ {} }}", arms.join(", ")))
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
        assert_eq!(WhenExpr.name(), "when_expr");
    }

    #[test]
    fn generates_when_with_wildcard() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("unreachable_probability", ParamValue::Probability(0.0)),
            ("multi_arm_probability", ParamValue::Probability(0.0)),
        ]);

        let result = WhenExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "expected when expr, got: {text}");
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
    }
}
