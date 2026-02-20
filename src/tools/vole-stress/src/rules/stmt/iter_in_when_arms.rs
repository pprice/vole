//! Rule: when with iterator terminals as arm values.
//!
//! Generates `when { x > 0 => arr.iter().count(), _ => arr.iter().sum() }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterInWhenArms;

impl StmtRule for IterInWhenArms {
    fn name(&self) -> &'static str {
        "iter_in_when_arms"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        let i64_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem_ty)| matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _)| name)
            .collect();

        if i64_vars.is_empty() || i64_arrays.is_empty() {
            return None;
        }

        let cond_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let arr = &i64_arrays[emit.gen_range(0..i64_arrays.len())];
        let name = scope.fresh_name();
        let thresh = emit.gen_i64_range(-5, 10);

        let terminals = ["count()", "sum()"];
        let t1 = terminals[emit.gen_range(0..terminals.len())];
        let t2 = terminals[emit.gen_range(0..terminals.len())];

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!(
            "let {} = when {{ {} > {} => {}.iter().{}, _ => {}.iter().{} }}",
            name, cond_var, thresh, arr, t1, arr, t2
        ))
    }
}

fn collect_i64_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(param.name.clone());
        }
    }
    out
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
        assert_eq!(IterInWhenArms.name(), "iter_in_when_arms");
    }

    #[test]
    fn generates_when() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterInWhenArms.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(text.contains(".iter()."), "got: {text}");
    }
}
