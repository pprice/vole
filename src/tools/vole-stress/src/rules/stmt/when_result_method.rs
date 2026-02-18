//! Rule: method call on when expression result.
//!
//! Generates `when { x > 0 => "hello", _ => "world" }.length()` and similar,
//! testing method dispatch on temporary when results.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenResultMethod;

impl StmtRule for WhenResultMethod {
    fn name(&self) -> &'static str {
        "when_result_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        let cond_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let thresh = emit.gen_i64_range(-5, 10);
        let name = scope.fresh_name();

        match emit.gen_range(0..3) {
            0 => {
                let s1 = ["hello", "abc", "test"][emit.gen_range(0..3)];
                let s2 = ["world", "xyz", "foo"][emit.gen_range(0..3)];
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!(
                    "let {} = when {{ {} > {} => \"{}\", _ => \"{}\" }}.length()",
                    name, cond_var, thresh, s1, s2
                ))
            }
            1 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = when {{ {} > {} => \"hello\", _ => \"world\" }}.to_upper()",
                    name, cond_var, thresh
                ))
            }
            _ => {
                let v1 = emit.gen_i64_range(0, 100);
                let v2 = emit.gen_i64_range(0, 100);
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = when {{ {} > {} => {}, _ => {} }}.to_string()",
                    name, cond_var, thresh, v1, v2
                ))
            }
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
        assert_eq!(WhenResultMethod.name(), "when_result_method");
    }

    #[test]
    fn generates_when_with_method() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenResultMethod.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}
