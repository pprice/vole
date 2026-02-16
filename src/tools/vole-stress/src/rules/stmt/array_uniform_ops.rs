//! Rule: uniform array operations.
//!
//! Creates arrays where all elements are the same value,
//! then performs iterator operations. Tests iter sum/count on uniform data.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ArrayUniformOps;

impl StmtRule for ArrayUniformOps {
    fn name(&self) -> &'static str {
        "array_uniform_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let val = emit.gen_i64_range(0, 20);
        let count = emit.random_in(1, 5);
        let elems = vec![val.to_string(); count];
        let arr_literal = format!("[{}]", elems.join(", "));

        let arr_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        scope.add_local(
            arr_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        let op = match emit.gen_range(0..3) {
            0 => format!(
                "let {} = {}\nlet {} = {}.iter().sum()",
                arr_name, arr_literal, result_name, arr_name
            ),
            1 => format!(
                "let {} = {}\nlet {} = {}.iter().count()",
                arr_name, arr_literal, result_name, arr_name
            ),
            _ => format!(
                "let {} = {}\nlet {} = {}.length()",
                arr_name, arr_literal, result_name, arr_name
            ),
        };

        Some(op)
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
        assert_eq!(ArrayUniformOps.name(), "array_uniform_ops");
    }

    #[test]
    fn generates_uniform_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ArrayUniformOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("["), "got: {text}");
        assert!(
            text.contains("iter()") || text.contains("length()"),
            "got: {text}"
        );
    }
}
