//! Rule: i64 near-boundary arithmetic operations.
//!
//! Produces expressions that operate near `i64::MAX` (9223372036854775807) to
//! test boundary handling without triggering overflow:
//! - `9223372036854775807 - 1`
//! - `(-9223372036854775807 + 1)`
//! - `(9223372036854775806 + 1)`
//! - `(4611686018427387903 * 2)`
//! - `(9223372036854775807 / 2)`
//! - `(9223372036854775807 % 100)`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct I64Boundary;

impl StmtRule for I64Boundary {
    fn name(&self) -> &'static str {
        "i64_boundary"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let choice = emit.gen_range(0..6);
        let expr = match choice {
            0 => "9223372036854775807 - 1".to_string(),
            1 => "(-9223372036854775807 + 1)".to_string(),
            2 => "(9223372036854775806 + 1)".to_string(),
            3 => "(4611686018427387903 * 2)".to_string(),
            4 => "(9223372036854775807 / 2)".to_string(),
            _ => "(9223372036854775807 % 100)".to_string(),
        };

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!("let {} = {}", name, expr))
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
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    #[test]
    fn generates_i64_boundary_expr() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = I64Boundary.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let local0 = "));
        assert!(
            text.contains("9223372036854775807")
                || text.contains("9223372036854775806")
                || text.contains("4611686018427387903")
        );
    }

    #[test]
    fn adds_i64_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        I64Boundary.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
        assert_eq!(scope.locals[0].1, TypeInfo::Primitive(PrimitiveType::I64));
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(I64Boundary.name(), "i64_boundary");
    }
}
