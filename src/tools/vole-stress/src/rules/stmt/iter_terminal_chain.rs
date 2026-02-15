//! Rule: iterator terminal chained with a method call.
//!
//! Generates `arr.iter().count().to_string()` and similar patterns
//! that test method dispatch on temporary values from iterator terminals.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterTerminalChain;

impl StmtRule for IterTerminalChain {
    fn name(&self) -> &'static str {
        "iter_terminal_chain"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let prim_arrays = collect_numeric_arrays(scope);
        if prim_arrays.is_empty() {
            return None;
        }

        let arr_name = &prim_arrays[emit.gen_range(0..prim_arrays.len())];
        let name = scope.fresh_name();

        match emit.gen_range(0..4) {
            0 => {
                // arr.iter().count().to_string()
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().count().to_string()",
                    name, arr_name
                ))
            }
            1 => {
                // arr.iter().sum().to_string()
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().sum().to_string()",
                    name, arr_name
                ))
            }
            2 => {
                // arr.iter().filter(...).count().to_string()
                let thresh = emit.gen_i64_range(-10, 10);
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().filter((x) => x > {}).count().to_string()",
                    name, arr_name, thresh
                ))
            }
            _ => {
                // "count=" + arr.iter().count().to_string()
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = \"count=\" + {}.iter().count().to_string()",
                    name, arr_name
                ))
            }
        }
    }
}

fn collect_numeric_arrays(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Array(elem) = ty {
            if matches!(
                elem.as_ref(),
                TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
            ) {
                out.push(name.clone());
            }
        }
    }
    for param in scope.params {
        if let TypeInfo::Array(elem) = &param.param_type {
            if matches!(
                elem.as_ref(),
                TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
            ) {
                out.push(param.name.clone());
            }
        }
    }
    out
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
        assert_eq!(IterTerminalChain.name(), "iter_terminal_chain");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            IterTerminalChain
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_chain_with_array() {
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
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterTerminalChain.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()."), "got: {text}");
    }
}
