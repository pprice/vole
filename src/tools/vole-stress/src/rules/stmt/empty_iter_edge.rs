//! Rule: zero-take / max-skip empty iterator edge cases.
//!
//! Generates `.take(0).collect()`, `.take(0).count()`, `.skip(999).collect()`,
//! or `.skip(999).count()` on array variables.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EmptyIterEdge;

impl StmtRule for EmptyIterEdge {
    fn name(&self) -> &'static str {
        "empty_iter_edge"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();

        for var in scope.vars_matching(|v| matches!(v.type_info, TypeInfo::Array(_))) {
            if let TypeInfo::Array(inner) = &var.type_info {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(
                        p,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String
                    ) {
                        array_vars.push((var.name, *p));
                    }
                }
            }
        }

        for param in scope.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(
                        p,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String
                    ) {
                        array_vars.push((param.name.clone(), *p));
                    }
                }
            }
        }

        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let result_name = scope.fresh_name();

        match emit.gen_range(0..4) {
            0 => {
                // .take(0).collect() -> empty array
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(*elem_prim))),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().take(0).collect()",
                    result_name, arr_name
                ))
            }
            1 => {
                // .take(0).count() -> 0
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().take(0).count()",
                    result_name, arr_name
                ))
            }
            2 => {
                // .skip(999).collect() -> empty array
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(*elem_prim))),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().skip(999).collect()",
                    result_name, arr_name
                ))
            }
            _ => {
                // .skip(999).count() -> 0
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().skip(999).count()",
                    result_name, arr_name
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
    use crate::symbols::{ParamInfo, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(EmptyIterEdge.name(), "empty_iter_edge");
    }

    #[test]
    fn generates_edge_case() {
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

        let result = EmptyIterEdge.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".take(0)") || text.contains(".skip(999)"),
            "got: {text}"
        );
    }
}
