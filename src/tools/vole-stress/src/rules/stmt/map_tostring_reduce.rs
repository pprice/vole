//! Rule: map-to-string-then-reduce (join pattern).
//!
//! Generates `arr.iter().map((el) => el.to_string()).reduce("", (acc, el) => acc + el + ",")`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MapTostringReduce;

impl StmtRule for MapTostringReduce {
    fn name(&self) -> &'static str {
        "map_tostring_reduce"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem_ty)| matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _)| name)
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let arr_name = i64_arrays[emit.gen_range(0..i64_arrays.len())].clone();
        let name = scope.fresh_name();
        let sep = [",", "-", " "][emit.gen_range(0..3)];

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = {}.iter().map((el) => el.to_string()).reduce(\"\", (acc, el) => acc + el + \"{}\")",
            name, arr_name, sep
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(MapTostringReduce.name(), "map_tostring_reduce");
    }

    #[test]
    fn generates_reduce() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MapTostringReduce.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".reduce("), "got: {text}");
    }
}
