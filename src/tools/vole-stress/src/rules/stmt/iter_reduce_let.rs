//! Rule: iter().reduce() on array parameters.
//!
//! Generates `let x = arr.iter().reduce(init, (acc, x) => acc + x)` for numeric
//! arrays, or string concatenation reduce for string arrays.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterReduceLet;

impl StmtRule for IterReduceLet {
    fn name(&self) -> &'static str {
        "iter_reduce_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let numeric_arrays: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                        Some((p.name.clone(), *prim))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let string_arrays: Vec<String> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner)
                    if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::String)) =>
                {
                    Some(p.name.clone())
                }
                _ => None,
            })
            .collect();

        if numeric_arrays.is_empty() && string_arrays.is_empty() {
            return None;
        }

        let name = scope.fresh_name();

        // 60% numeric reduce, 40% string reduce
        if !numeric_arrays.is_empty() && (string_arrays.is_empty() || emit.gen_bool(0.6)) {
            let idx = emit.gen_range(0..numeric_arrays.len());
            let (arr_name, prim) = &numeric_arrays[idx];
            let suffix = if matches!(prim, PrimitiveType::I32) {
                "_i32"
            } else {
                ""
            };
            let type_annot = if matches!(prim, PrimitiveType::I32) {
                "i32"
            } else {
                "i64"
            };

            let (init, op) = match emit.gen_range(0..3) {
                0 => (format!("0{}", suffix), "+"),
                1 => (format!("1{}", suffix), "*"),
                _ => (format!("0{}", suffix), "+"),
            };

            scope.add_local(name.clone(), TypeInfo::Primitive(*prim), false);
            Some(format!(
                "let {} = {}.iter().reduce({}, (acc: {}, x: {}) -> {} => acc {} x)",
                name, arr_name, init, type_annot, type_annot, type_annot, op
            ))
        } else {
            let idx = emit.gen_range(0..string_arrays.len());
            let arr_name = &string_arrays[idx];
            let seps = [", ", " ", "-", "; "];
            let sep = seps[emit.gen_range(0..seps.len())];

            scope.add_local(
                name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );
            Some(format!(
                "let {} = {}.iter().reduce(\"\", (acc, x) => acc + x + \"{}\")",
                name, arr_name, sep
            ))
        }
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
        assert_eq!(IterReduceLet.name(), "iter_reduce_let");
    }

    #[test]
    fn generates_numeric_reduce() {
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

        let result = IterReduceLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".reduce("), "got: {text}");
    }

    #[test]
    fn generates_string_reduce() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "strs".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterReduceLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".reduce("), "got: {text}");
    }
}
