//! Rule: empty range (N..N) operations.
//!
//! Generates `(5..5).iter().collect()`, `(0..0).iter().count()` — empty ranges.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EmptyRange;

impl StmtRule for EmptyRange {
    fn name(&self) -> &'static str {
        "empty_range"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let n = emit.gen_range(0..11);

        match emit.gen_range(0..3) {
            0 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                Some(format!("let {} = ({}..{}).iter().collect()", name, n, n))
            }
            1 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = ({}..{}).iter().count()", name, n, n))
            }
            _ => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = ({}..{}).iter().sum()", name, n, n))
            }
        }
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
        assert_eq!(EmptyRange.name(), "empty_range");
    }

    #[test]
    fn generates_empty_range() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EmptyRange.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()."), "got: {text}");
    }
}
