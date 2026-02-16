//! Rule: modulo edge-case expressions.
//!
//! Produces patterns testing modulo operator edge cases:
//! - `N % 1` (always 0)
//! - `N % N` (always 0)
//! - `0 % N` (always 0)
//! - known `a % b` with concrete values

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ModuloEdge;

impl StmtRule for ModuloEdge {
    fn name(&self) -> &'static str {
        "modulo_edge"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let choice = emit.gen_range(0..4);
        let expr = match choice {
            0 => {
                // literal % 1 == 0
                let val = emit.random_in(1, 100);
                format!("{} % 1", val)
            }
            1 => {
                // literal % itself == 0
                let val = emit.random_in(1, 100);
                format!("{} % {}", val, val)
            }
            2 => {
                // 0 % literal == 0
                let val = emit.random_in(1, 100);
                format!("0 % {}", val)
            }
            _ => {
                // known modulo: a % b where a and b are known
                let b = emit.random_in(2, 10);
                let mult = emit.random_in(1, 5);
                let rem = emit.gen_range(0..b);
                let a = b * mult + rem;
                format!("{} % {}", a, b)
            }
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn generates_modulo_expression() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ModuloEdge.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let local0 = "));
        assert!(text.contains('%'));
    }

    #[test]
    fn adds_i64_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ModuloEdge.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
        assert_eq!(scope.locals[0].1, TypeInfo::Primitive(PrimitiveType::I64));
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ModuloEdge.name(), "modulo_edge");
    }
}
