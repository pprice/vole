//! Rule: negative division and modulo edge cases.
//!
//! Produces expressions that test platform-specific truncation behavior
//! for signed division and modulo with negative operands:
//! - `(-7 / 2)`   → -3  (truncation toward zero)
//! - `(-7 % 2)`   → -1
//! - `(7 / -2)`   → -3
//! - `(7 % -2)`   → 1
//! - `(-7 / -2)`  → 3
//! - `(-7 % -2)`  → -1
//! - `(-1 / -1)`  → 1   (edge: both negative, result positive)
//! - `(1 % -1)`   → 0   (edge: modulo is zero)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NegativeDivmod;

impl StmtRule for NegativeDivmod {
    fn name(&self) -> &'static str {
        "negative_divmod"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let choice = emit.gen_range(0..8);
        let expr = match choice {
            0 => "(-7 / 2)".to_string(),
            1 => "(-7 % 2)".to_string(),
            2 => "(7 / -2)".to_string(),
            3 => "(7 % -2)".to_string(),
            4 => "(-7 / -2)".to_string(),
            5 => "(-7 % -2)".to_string(),
            6 => "(-1 / -1)".to_string(),
            _ => "(1 % -1)".to_string(),
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
    fn generates_negative_divmod_expr() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NegativeDivmod.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let local0 = "));
        assert!(text.contains('/') || text.contains('%'));
    }

    #[test]
    fn adds_i64_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        NegativeDivmod.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
        assert_eq!(scope.locals[0].1, TypeInfo::Primitive(PrimitiveType::I64));
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(NegativeDivmod.name(), "negative_divmod");
    }
}
