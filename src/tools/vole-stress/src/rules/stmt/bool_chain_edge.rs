//! Rule: chained boolean literal operations.
//!
//! Generates `true && false || true`, `!(true && false)`, etc.
//! Tests boolean operator codegen on literal chains.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct BoolChainEdge;

impl StmtRule for BoolChainEdge {
    fn name(&self) -> &'static str {
        "bool_chain_edge"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let expr = match emit.gen_range(0..5) {
            0 => "true && true",
            1 => "true && false || true",
            2 => "false || false || true",
            3 => "!(true && false)",
            _ => "true && !false",
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
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
    fn name_is_correct() {
        assert_eq!(BoolChainEdge.name(), "bool_chain_edge");
    }

    #[test]
    fn generates_chain() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BoolChainEdge.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
    }
}
