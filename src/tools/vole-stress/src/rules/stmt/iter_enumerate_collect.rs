//! Rule: `.iter().enumerate().collect()` chains on arrays.
//!
//! Produces `[(i64, T)]` from `[T]`.  Optionally chains `.map()` on the
//! enumerate when the element type is `i64`, summing index + value.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterEnumerateCollect;

impl StmtRule for IterEnumerateCollect {
    fn name(&self) -> &'static str {
        "iter_enumerate_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<(String, TypeInfo)> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(elem) => Some((p.name.clone(), *elem.clone())),
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_params.len());
        let (arr_name, elem_type) = &array_params[idx];
        let name = scope.fresh_name();

        // When the element type is i64, optionally chain .map() that sums index + value.
        let is_i64 = matches!(elem_type, TypeInfo::Primitive(PrimitiveType::I64));
        let use_map = is_i64 && emit.gen_bool(0.4);

        if use_map {
            // .iter().enumerate().map((p) => p[0] + p[1]).collect() -> [i64]
            let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
            scope.add_local(name.clone(), result_type, false);
            Some(format!(
                "let {} = {}.iter().enumerate().map((p) => p[0] + p[1]).collect()",
                name, arr_name
            ))
        } else {
            // .iter().enumerate().collect() -> [(i64, T)]
            let tuple_type = TypeInfo::Tuple(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                elem_type.clone(),
            ]);
            let result_type = TypeInfo::Array(Box::new(tuple_type));
            scope.add_local(name.clone(), result_type, false);
            Some(format!(
                "let {} = {}.iter().enumerate().collect()",
                name, arr_name
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, PrimitiveType, SymbolTable};
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
        assert_eq!(IterEnumerateCollect.name(), "iter_enumerate_collect");
    }

    #[test]
    fn generates_enumerate_collect() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterEnumerateCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".iter().enumerate().collect()")
                || text.contains(".iter().enumerate().map("),
            "got: {text}"
        );
    }

    #[test]
    fn generates_enumerate_on_string_array() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "names".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterEnumerateCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        // String arrays cannot use the map variant, must be plain enumerate+collect
        assert!(
            text.contains(".iter().enumerate().collect()"),
            "string arrays should use plain enumerate+collect, got: {text}"
        );
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "x".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterEnumerateCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
