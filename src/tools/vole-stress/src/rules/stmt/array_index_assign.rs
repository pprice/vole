//! Rule: array index assignment (arr[i] = expr).
//!
//! Picks a random mutable dynamic array in scope, generates a bounds-safe
//! index (0, since arrays may be single-element), and a type-compatible
//! RHS value matching the element type.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct ArrayIndexAssign;

impl StmtRule for ArrayIndexAssign {
    fn name(&self) -> &'static str {
        "array_index_assign"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
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

        // Use index 0 -- arrays may be single-element.
        let index = 0;
        let value = emit.literal(elem_type);

        Some(format!("{}[{}] = {}", arr_name, index, value))
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
        assert_eq!(ArrayIndexAssign.name(), "array_index_assign");
    }

    #[test]
    fn generates_index_assignment() {
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

        let result = ArrayIndexAssign.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("[0] = "), "got: {text}");
    }
}
