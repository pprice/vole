//! Rule: re-iterate existing array local.
//!
//! Chains a new iterator operation on an existing i64 array variable:
//! `.iter().map(...)`, `.iter().filter(...)`, `.iter().sorted()`, etc.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ReiterateLet;

impl StmtRule for ReiterateLet {
    fn name(&self) -> &'static str {
        "reiterate_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_array_vars: Vec<String> = scope
            .vars_matching(|v| {
                matches!(
                    v.type_info,
                    TypeInfo::Array(ref inner) if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .into_iter()
            .map(|v| v.name)
            .collect();

        if i64_array_vars.is_empty() {
            return None;
        }

        let arr_name = &i64_array_vars[emit.gen_range(0..i64_array_vars.len())];
        let result_name = scope.fresh_name();

        let (chain, result_type) = match emit.gen_range(0..5) {
            0 => {
                let body = map_body_i64(emit);
                (
                    format!(".iter().map((x) => {}).collect()", body),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                )
            }
            1 => {
                let pred = filter_body_i64(emit);
                (
                    format!(".iter().filter((x) => {}).count()", pred),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            2 => (
                ".iter().sorted().collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
            3 => (
                ".iter().enumerate().count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            _ => (
                ".iter().sum()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
        };

        scope.add_local(result_name.clone(), result_type, false);
        Some(format!("let {} = {}{}", result_name, arr_name, chain))
    }
}

fn map_body_i64(emit: &mut Emit) -> String {
    match emit.gen_range(0..3) {
        0 => {
            let n = emit.random_in(2, 5);
            format!("x * {}", n)
        }
        1 => {
            let n = emit.random_in(1, 10);
            format!("x + {}", n)
        }
        _ => {
            let n = emit.random_in(1, 3);
            format!("x - {}", n)
        }
    }
}

fn filter_body_i64(emit: &mut Emit) -> String {
    match emit.gen_range(0..3) {
        0 => {
            let n = emit.gen_i64_range(-5, 2);
            format!("x > {}", n)
        }
        1 => {
            let n = emit.gen_i64_range(5, 20);
            format!("x < {}", n)
        }
        _ => "x % 2 == 0".to_string(),
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
        assert_eq!(ReiterateLet.name(), "reiterate_let");
    }

    #[test]
    fn generates_reiterate() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ReiterateLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "got: {text}");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ReiterateLet
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
