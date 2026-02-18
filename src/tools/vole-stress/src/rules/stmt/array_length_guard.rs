//! Rule: safe array access with length guard.
//!
//! Generates `when { arr.length() > 0 => arr[0], _ => default }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ArrayLengthGuard;

impl StmtRule for ArrayLengthGuard {
    fn name(&self) -> &'static str {
        "array_length_guard"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim) => Some((p.name.clone(), *prim)),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_params.len());
        let (arr_name, elem_prim) = &array_params[idx];
        let name = scope.fresh_name();

        let default_val = match elem_prim {
            PrimitiveType::I64 => "0",
            PrimitiveType::I32 => "0_i32",
            PrimitiveType::Bool => "false",
            PrimitiveType::String => "\"\"",
            PrimitiveType::F64 => "0.0",
            _ => return None,
        };

        scope.add_local(name.clone(), TypeInfo::Primitive(*elem_prim), false);
        Some(format!(
            "let {} = when {{ {}.length() > 0 => {}[0], _ => {} }}",
            name, arr_name, arr_name, default_val
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
        assert_eq!(ArrayLengthGuard.name(), "array_length_guard");
    }

    #[test]
    fn generates_guard() {
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

        let result = ArrayLengthGuard.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(text.contains(".length()"), "got: {text}");
    }
}
