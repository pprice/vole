//! Rule: single-element array operations.
//!
//! Creates `[val]` then performs iterator or index operations,
//! exercising boundary conditions for 1-element arrays.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SingleElemArrayOps;

impl StmtRule for SingleElemArrayOps {
    fn name(&self) -> &'static str {
        "single_elem_array_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arr_name = scope.fresh_name();
        let result_name = scope.fresh_name();
        let indent = emit.indent_str();

        let (elem_type, val) = match emit.gen_range(0..3) {
            0 => (
                PrimitiveType::I64,
                format!("{}", emit.gen_i64_range(-100, 100)),
            ),
            1 => (
                PrimitiveType::I32,
                format!("{}_i32", emit.gen_i64_range(-100, 100)),
            ),
            _ => {
                let strs = ["hello", "world", "test", "a"];
                (
                    PrimitiveType::String,
                    format!("\"{}\"", strs[emit.gen_range(0..strs.len())]),
                )
            }
        };

        scope.add_local(
            arr_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_type))),
            false,
        );

        let op = match emit.gen_range(0..4) {
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
            2 => {
                scope.add_local(result_name.clone(), TypeInfo::Primitive(elem_type), false);
                format!("let {} = {}[0]", result_name, arr_name)
            }
            _ => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_type))),
                    false,
                );
                format!(
                    "let {} = {}.iter().filter((x) => true).collect()",
                    result_name, arr_name
                )
            }
        };

        Some(format!("let {} = [{}]\n{}{}", arr_name, val, indent, op))
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
        assert_eq!(SingleElemArrayOps.name(), "single_elem_array_ops");
    }

    #[test]
    fn generates_single_elem_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SingleElemArrayOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("["), "got: {text}");
    }
}
