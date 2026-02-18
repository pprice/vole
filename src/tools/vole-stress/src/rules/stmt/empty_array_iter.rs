//! Rule: empty array iterator operation.
//!
//! Generates empty array declarations followed by iterator terminal calls,
//! testing the compiler's handling of zero-length array iterators.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EmptyArrayIter;

impl StmtRule for EmptyArrayIter {
    fn name(&self) -> &'static str {
        "empty_array_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arr_name = scope.fresh_name();
        let result_name = scope.fresh_name();
        let indent = emit.indent_str();

        let (elem_type, type_str) = match emit.gen_range(0..3) {
            0 => (PrimitiveType::I64, "i64"),
            1 => (PrimitiveType::I32, "i32"),
            _ => (PrimitiveType::String, "string"),
        };

        // Don't register the empty array in scope — later rules (array_index)
        // would OOB-panic indexing into it.

        let terminal = match emit.gen_range(0..3) {
            0 => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = {}.iter().count()", result_name, arr_name)
            }
            1 if !matches!(elem_type, PrimitiveType::String) => {
                scope.add_local(result_name.clone(), TypeInfo::Primitive(elem_type), false);
                format!("let {} = {}.iter().sum()", result_name, arr_name)
            }
            _ => {
                // Don't register in scope — filter on empty array yields empty array.
                format!(
                    "let {} = {}.iter().filter((x) => x == x).collect()",
                    result_name, arr_name
                )
            }
        };

        Some(format!(
            "let {}: [{}] = []\n{}{}",
            arr_name, type_str, indent, terminal
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
        assert_eq!(EmptyArrayIter.name(), "empty_array_iter");
    }

    #[test]
    fn generates_empty_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EmptyArrayIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("= []"), "got: {text}");
    }
}
