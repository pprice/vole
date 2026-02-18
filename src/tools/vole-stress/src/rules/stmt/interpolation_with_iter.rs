//! Rule: string interpolation containing an iterator terminal.
//!
//! Generates `"count: {arr.iter().count()}"` and similar patterns
//! that test iterator chains inside string interpolation braces.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct InterpolationWithIter;

impl StmtRule for InterpolationWithIter {
    fn name(&self) -> &'static str {
        "interpolation_with_iter"
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

        let prefix = ["count:", "sum=", "n=", "result:"][emit.gen_range(0..4)];

        let iter_expr = match emit.gen_range(0..3) {
            0 => format!("{}.iter().count()", arr_name),
            1 => format!("{}.iter().sum()", arr_name),
            _ => {
                let thresh = emit.gen_i64_range(-5, 5);
                format!("{}.iter().filter((x) => x > {}).count()", arr_name, thresh)
            }
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!("let {} = \"{} {{{}}}\"", name, prefix, iter_expr))
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
        assert_eq!(InterpolationWithIter.name(), "interpolation_with_iter");
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
            InterpolationWithIter
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_interpolation() {
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

        let result = InterpolationWithIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()."), "got: {text}");
    }
}
