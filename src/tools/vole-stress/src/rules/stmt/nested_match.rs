//! Rule: nested match expression.
//!
//! Generates a match inside a match arm:
//! ```vole
//! let r = match x {
//!     0 => match y { 0 => a, _ => b }
//!     _ => c
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedMatch;

impl StmtRule for NestedMatch {
    fn name(&self) -> &'static str {
        "nested_match"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.len() < 2 {
            return None;
        }

        let outer_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let inner_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let name = scope.fresh_name();
        let indent = emit.indent_str();

        let outer_val = emit.random_in(0, 5);
        let inner_val = emit.random_in(0, 5);
        let result_a = emit.gen_i64_range(-10, 10);
        let result_b = emit.gen_i64_range(-10, 10);
        let result_c = emit.gen_i64_range(-10, 10);

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = match {} {{\n\
             {}    {} => match {} {{ {} => {}, _ => {} }}\n\
             {}    _ => {}\n\
             {}}}",
            name,
            outer_var,
            indent,
            outer_val,
            inner_var,
            inner_val,
            result_a,
            result_b,
            indent,
            result_c,
            indent,
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
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(NestedMatch.name(), "nested_match");
    }

    #[test]
    fn returns_none_with_fewer_than_two_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            NestedMatch
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_nested_match() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedMatch.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        // Should have two "match" keywords
        assert!(text.matches("match ").count() >= 2, "got: {text}");
    }
}
