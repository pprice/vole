//! Rule: single-element range operations.
//!
//! Generates `(5..6).iter().collect()` — ranges with exactly one element.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SingleElemRange;

impl StmtRule for SingleElemRange {
    fn name(&self) -> &'static str {
        "single_elem_range"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let start = emit.gen_range(0..11) as i64;

        match emit.gen_range(0..3) {
            0 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                Some(format!(
                    "let {} = ({}..{}).iter().collect()",
                    name,
                    start,
                    start + 1
                ))
            }
            1 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!(
                    "let {} = ({}..{}).iter().sum()",
                    name,
                    start,
                    start + 1
                ))
            }
            _ => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!(
                    "let {} = ({}..{}).iter().count()",
                    name,
                    start,
                    start + 1
                ))
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(SingleElemRange.name(), "single_elem_range");
    }

    #[test]
    fn generates_range() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SingleElemRange.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()."), "got: {text}");
    }
}
