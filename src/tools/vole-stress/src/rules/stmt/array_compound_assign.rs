//! Rule: array index compound assignment (arr[i] += expr).
//!
//! Picks a random mutable dynamic array with numeric element type in scope,
//! generates a bounds-safe index, a compound operator (+=, -=, *=, %=),
//! and a type-compatible RHS value.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ArrayCompoundAssign;

impl StmtRule for ArrayCompoundAssign {
    fn name(&self) -> &'static str {
        "array_compound_assign"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !mutable_numeric_arrays(scope).is_empty()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = mutable_numeric_arrays(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (arr_name, elem_prim) = &candidates[idx];
        let elem_prim = *elem_prim;

        // Use index 0 -- arrays may be single-element.
        let index = 0;

        let op = match emit.gen_range(0..4) {
            0 => "+=",
            1 => "-=",
            2 => "*=",
            _ => "%=",
        };

        let value = if op == "%=" {
            emit.nonzero_literal(elem_prim)
        } else {
            emit.literal(&TypeInfo::Primitive(elem_prim))
        };

        Some(format!("{}[{}] {} {}", arr_name, index, op, value))
    }
}

fn mutable_numeric_arrays(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    scope
        .locals
        .iter()
        .filter_map(|(name, ty, is_mut)| {
            if *is_mut
                && !scope.protected_vars.contains(name)
                && let TypeInfo::Array(elem) = ty
                && let TypeInfo::Primitive(
                    p @ (PrimitiveType::I8
                    | PrimitiveType::I16
                    | PrimitiveType::I32
                    | PrimitiveType::I64
                    | PrimitiveType::I128
                    | PrimitiveType::U8
                    | PrimitiveType::U16
                    | PrimitiveType::U32
                    | PrimitiveType::U64
                    | PrimitiveType::F32
                    | PrimitiveType::F64),
                ) = **elem
            {
                return Some((name.clone(), p));
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
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ArrayCompoundAssign.name(), "array_compound_assign");
    }

    #[test]
    fn generates_compound_assign() {
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

        let result = ArrayCompoundAssign.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("arr[0] "), "got: {text}");
    }
}
