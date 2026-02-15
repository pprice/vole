//! Rule: nested when-in-when expression.
//!
//! Generates `when { cond1 => when { cond2 => a, _ => b }, _ => c }`,
//! exercising nested conditional code generation.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedWhen;

impl StmtRule for NestedWhen {
    fn name(&self) -> &'static str {
        "nested_when"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        let name = scope.fresh_name();
        let indent = emit.indent_str();

        let cond1_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let cond1_thresh = emit.gen_i64_range(-10, 10);
        let cond1_op = [">", "<", ">="][emit.gen_range(0..3)];

        let cond2_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let cond2_thresh = emit.gen_i64_range(-10, 10);
        let cond2_op = [">", "<=", "=="][emit.gen_range(0..3)];

        if emit.gen_bool(0.5) {
            // i64 result
            let v0 = emit.gen_i64_range(-20, 20);
            let v1 = emit.gen_i64_range(-20, 20);
            let v2 = emit.gen_i64_range(-20, 20);
            scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
            Some(format!(
                "let {} = when {{\n\
                 {indent}    {} {} {} => when {{ {} {} {} => {}, _ => {} }},\n\
                 {indent}    _ => {}\n\
                 {indent}}}",
                name,
                cond1_var,
                cond1_op,
                cond1_thresh,
                cond2_var,
                cond2_op,
                cond2_thresh,
                v0,
                v1,
                v2,
                indent = indent,
            ))
        } else {
            // string result
            let strs = ["\"big\"", "\"medium\"", "\"small\"", "\"tiny\"", "\"zero\""];
            let s0 = strs[emit.gen_range(0..strs.len())];
            let s1 = strs[emit.gen_range(0..strs.len())];
            let s2 = strs[emit.gen_range(0..strs.len())];
            scope.add_local(
                name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );
            Some(format!(
                "let {} = when {{\n\
                 {indent}    {} {} {} => when {{ {} {} {} => {}, _ => {} }},\n\
                 {indent}    _ => {}\n\
                 {indent}}}",
                name,
                cond1_var,
                cond1_op,
                cond1_thresh,
                cond2_var,
                cond2_op,
                cond2_thresh,
                s0,
                s1,
                s2,
                indent = indent,
            ))
        }
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
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(NestedWhen.name(), "nested_when");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            NestedWhen
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_nested_when() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedWhen.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}
