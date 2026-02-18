//! Rule: direct variable reassignment (x = new_value).
//!
//! Picks a random mutable local (excluding protected variables), then
//! generates a type-compatible RHS value.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct Reassignment;

impl StmtRule for Reassignment {
    fn name(&self) -> &'static str {
        "reassignment"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.locals.iter().any(|(name, ty, is_mut)| {
            *is_mut
                && !scope.protected_vars.contains(name)
                && !matches!(ty, TypeInfo::Void | TypeInfo::TypeParam(_))
        })
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates: Vec<(String, TypeInfo)> = scope
            .locals
            .iter()
            .filter(|(name, ty, is_mut)| {
                *is_mut
                    && !scope.protected_vars.contains(name)
                    && !matches!(ty, TypeInfo::Void | TypeInfo::TypeParam(_))
            })
            .map(|(name, ty, _)| (name.clone(), ty.clone()))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, var_type) = &candidates[idx];

        let rhs = emit.literal(var_type);
        Some(format!("{} = {}", var_name, rhs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{PrimitiveType, SymbolTable};
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
        assert_eq!(Reassignment.name(), "reassignment");
    }

    #[test]
    fn generates_reassignment() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), true);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = Reassignment.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("x = "), "got: {text}");
    }

    #[test]
    fn returns_none_without_mutable_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            Reassignment
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
