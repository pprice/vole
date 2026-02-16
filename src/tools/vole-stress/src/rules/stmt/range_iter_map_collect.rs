//! Rule: range-based iterator with map and collect.
//!
//! Generates `(0..5).iter().map((x) => x * 2).collect()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct RangeIterMapCollect;

impl StmtRule for RangeIterMapCollect {
    fn name(&self) -> &'static str {
        "range_iter_map_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let n = emit.random_in(2, 8);
        let multiplier = emit.random_in(1, 5);

        let map_op = match emit.gen_range(0..3) {
            0 => format!("x * {}", multiplier),
            1 => format!("x + {}", multiplier),
            _ => format!("x * {} + 1", multiplier),
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        Some(format!(
            "let {} = (0..{}).iter().map((x) => {}).collect()",
            name, n, map_op
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
        assert_eq!(RangeIterMapCollect.name(), "range_iter_map_collect");
    }

    #[test]
    fn generates_range_iter() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = RangeIterMapCollect.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter().map("), "got: {text}");
        assert!(text.contains(".collect()"), "got: {text}");
    }
}
