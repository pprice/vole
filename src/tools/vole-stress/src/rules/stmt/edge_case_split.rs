//! Rule: edge-case string split operation.
//!
//! Tests the compiler with degenerate split results:
//! empty string, delimiter == entire string, consecutive delimiters.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EdgeCaseSplit;

impl StmtRule for EdgeCaseSplit {
    fn name(&self) -> &'static str {
        "edge_case_split"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let result_name = scope.fresh_name();

        let (input, delim) = match emit.gen_range(0..4) {
            0 => ("\"\"", "\",\""),
            1 => ("\"a\"", "\"a\""),
            2 => ("\",,\"", "\",\""),
            _ => ("\"a,b,c\"", "\",\""),
        };

        match emit.gen_range(0..3) {
            0 => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}.split({}).collect().iter().count()",
                    result_name, input, delim
                ))
            }
            1 => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}.split({}).collect()",
                    result_name, input, delim
                ))
            }
            _ => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}.split({}).count()",
                    result_name, input, delim
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
        assert_eq!(EdgeCaseSplit.name(), "edge_case_split");
    }

    #[test]
    fn generates_split() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EdgeCaseSplit.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("split("), "got: {text}");
    }
}
