//! Rule: guarded division to avoid division by zero.
//!
//! Generates `when { b != 0 => a / b, _ => 0 }`, testing safe division
//! patterns with zero-check guards.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ZeroDivisionGuard;

impl StmtRule for ZeroDivisionGuard {
    fn name(&self) -> &'static str {
        "zero_division_guard"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let numeric_vars: Vec<(String, PrimitiveType)> = scope
            .locals
            .iter()
            .filter_map(|(name, ty, _)| match ty {
                TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                    Some((name.clone(), *p))
                }
                _ => None,
            })
            .collect();

        if numeric_vars.len() < 2 {
            return None;
        }

        let idx_a = emit.gen_range(0..numeric_vars.len());
        let mut idx_b = emit.gen_range(0..numeric_vars.len());
        while idx_b == idx_a {
            idx_b = emit.gen_range(0..numeric_vars.len());
        }

        let (a_name, a_prim) = &numeric_vars[idx_a];
        let (b_name, b_prim) = &numeric_vars[idx_b];

        // Both must be same type
        if a_prim != b_prim {
            return None;
        }

        let name = scope.fresh_name();
        let zero = match a_prim {
            PrimitiveType::I64 => "0",
            PrimitiveType::I32 => "0_i32",
            _ => return None,
        };

        let op = if emit.gen_bool(0.5) { "/" } else { "%" };

        scope.add_local(name.clone(), TypeInfo::Primitive(*a_prim), false);
        Some(format!(
            "let {} = when {{ {} != {} => {} {} {}, _ => {} }}",
            name, b_name, zero, a_name, op, b_name, zero
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
        assert_eq!(ZeroDivisionGuard.name(), "zero_division_guard");
    }

    #[test]
    fn returns_none_without_enough_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ZeroDivisionGuard
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_guarded_division() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("a".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ZeroDivisionGuard.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("when") && text.contains("!= 0"),
            "got: {text}"
        );
    }
}
