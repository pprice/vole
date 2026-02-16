//! Rule: array push statement.
//!
//! Picks a random mutable dynamic array in scope and generates
//! `arr.push(value)` with a type-compatible value.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct ArrayPush;

impl StmtRule for ArrayPush {
    fn name(&self) -> &'static str {
        "array_push"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !mutable_dynamic_arrays(scope).is_empty()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = mutable_dynamic_arrays(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (arr_name, elem_type) = &candidates[idx];

        let value = emit.literal(elem_type);
        Some(format!("{}.push({})", arr_name, value))
    }
}

fn mutable_dynamic_arrays(scope: &Scope) -> Vec<(String, TypeInfo)> {
    scope
        .locals
        .iter()
        .filter_map(|(name, ty, is_mut)| {
            if *is_mut
                && !scope.protected_vars.contains(name)
                && let TypeInfo::Array(elem) = ty
            {
                return Some((name.clone(), *elem.clone()));
            }
            None
        })
        .collect()
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ArrayPush.name(), "array_push");
    }

    #[test]
    fn generates_push() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            true,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ArrayPush.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".push("), "got: {text}");
    }

    #[test]
    fn returns_none_without_mutable_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Immutable array
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ArrayPush
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
