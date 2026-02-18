//! Rule: conditional (if/when) expression.
//!
//! Generates a 2-arm `when { cond => then, _ => else }` expression.
//! Works for any expected type.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

/// Strip Optional wrappers so that when arms produce a consistent concrete
/// type.  See [`super::when_expr::strip_optional_type`] for rationale.
fn strip_optional_type(ty: &TypeInfo) -> &TypeInfo {
    match ty {
        TypeInfo::Optional(inner) => strip_optional_type(inner),
        _ => ty,
    }
}

pub struct IfExpr;

impl ExprRule for IfExpr {
    fn name(&self) -> &'static str {
        "if_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        // Strip Optional wrappers so both arms produce the same concrete type.
        // literal(Optional(T)) randomly returns nil or T, which would cause
        // a type mismatch between arms.
        let arm_type = strip_optional_type(expected_type);

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let cond = emit.sub_expr(&bool_ty, scope);
        let then_expr = emit.sub_expr(arm_type, scope);
        let else_expr = emit.sub_expr(arm_type, scope);

        Some(format!(
            "when {{ {} => {}, _ => {} }}",
            cond, then_expr, else_expr
        ))
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
        assert_eq!(IfExpr.name(), "if_expr");
    }

    #[test]
    fn generates_when_expression() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IfExpr.generate(
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
