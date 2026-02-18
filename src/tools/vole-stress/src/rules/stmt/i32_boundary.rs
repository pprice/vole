//! Rule: i32 near-boundary arithmetic operations.
//!
//! Produces expressions that operate near `i32::MAX` (2147483647) to test
//! boundary handling without triggering overflow:
//! - `2147483647_i32 - 1_i32`
//! - `(-2147483647_i32 + 1_i32)`
//! - `(2147483646_i32 + 1_i32)`
//! - `(1073741823_i32 * 2_i32)`
//! - `(2147483647_i32 / 2_i32)`
//! - `(2147483647_i32 % 100_i32)`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct I32Boundary;

impl StmtRule for I32Boundary {
    fn name(&self) -> &'static str {
        "i32_boundary"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let choice = emit.gen_range(0..6);
        let expr = match choice {
            0 => "2147483647_i32 - 1_i32".to_string(),
            1 => "(-2147483647_i32 + 1_i32)".to_string(),
            2 => "(2147483646_i32 + 1_i32)".to_string(),
            3 => "(1073741823_i32 * 2_i32)".to_string(),
            4 => "(2147483647_i32 / 2_i32)".to_string(),
            _ => "(2147483647_i32 % 100_i32)".to_string(),
        };

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I32), false);
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
    fn generates_i32_boundary_expr() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = I32Boundary.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let local0 = "));
        assert!(text.contains("_i32"));
    }

    #[test]
    fn adds_i32_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        I32Boundary.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
        assert_eq!(scope.locals[0].1, TypeInfo::Primitive(PrimitiveType::I32));
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(I32Boundary.name(), "i32_boundary");
    }
}
