//! Rule: type test (`is`) expression.
//!
//! Generates `varName is TypeName` on a union-typed variable.
//! Result type is `bool`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IsExpr;

impl ExprRule for IsExpr {
    fn name(&self) -> &'static str {
        "is_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Union(_)))
            .first()
            .is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            return None;
        }

        let union_vars = scope.vars_matching(|v| matches!(v.type_info, TypeInfo::Union(_)));
        if union_vars.is_empty() {
            return None;
        }

        let var_idx = emit.gen_range(0..union_vars.len());
        let var = &union_vars[var_idx];
        let variants = match &var.type_info {
            TypeInfo::Union(v) => v,
            _ => return None,
        };

        if variants.is_empty() {
            return None;
        }

        let variant_idx = emit.gen_range(0..variants.len());
        let variant = &variants[variant_idx];

        // Only generate `is` for primitive variants
        match variant {
            TypeInfo::Primitive(prim) => Some(format!("({} is {})", var.name, prim.as_str())),
            _ => None,
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
        assert_eq!(IsExpr.name(), "is_expr");
    }

    #[test]
    fn returns_none_without_union_vars() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IsExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_is_expr_with_union_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "u".into(),
            TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Primitive(PrimitiveType::String),
            ]),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IsExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(" is "), "expected is expr, got: {text}");
    }
}
