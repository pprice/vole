//! Rule: last-element array access via computed index.
//!
//! Generates `arr[arr.length() - 1]` and similar patterns that test
//! runtime-computed index expressions.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct LastElemAccess;

impl StmtRule for LastElemAccess {
    fn name(&self) -> &'static str {
        "last_elem_access"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Use parameter arrays (guaranteed non-empty)
        let param_arrays: Vec<(String, TypeInfo)> = scope
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| (p.name.clone(), p.param_type.clone()))
            .collect();

        if param_arrays.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..param_arrays.len());
        let (arr_name, arr_type) = &param_arrays[idx];
        let elem_type = if let TypeInfo::Array(elem) = arr_type {
            elem.as_ref().clone()
        } else {
            return None;
        };

        let name = scope.fresh_name();

        let expr = match emit.gen_range(0..2) {
            0 => format!("{}[{}.length() - 1]", arr_name, arr_name),
            _ => format!(
                "{}[{}.length() - {}.length()]",
                arr_name, arr_name, arr_name
            ),
        };

        scope.add_local(name.clone(), elem_type, false);
        Some(format!("let {} = {}", name, expr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{PrimitiveType, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(LastElemAccess.name(), "last_elem_access");
    }

    #[test]
    fn returns_none_without_param_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            LastElemAccess
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_access_with_param_array() {
        use crate::symbols::ParamInfo;

        let func_params = vec![ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let table = SymbolTable::new();
        let mut scope = Scope::new(&func_params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LastElemAccess.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".length()"), "got: {text}");
    }
}
