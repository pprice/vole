//! Rule: when with string predicate condition.
//!
//! Generates `when { s.contains("x") => "found", _ => "not found" }`,
//! testing string predicates as when conditions.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenWithContains;

impl StmtRule for WhenWithContains {
    fn name(&self) -> &'static str {
        "when_with_contains"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        if string_vars.is_empty() {
            return None;
        }

        let var = &string_vars[emit.gen_range(0..string_vars.len())];
        let name = scope.fresh_name();

        let method = ["contains", "starts_with", "ends_with"][emit.gen_range(0..3)];
        let needles = ["hello", "test", "a", "str", ""];
        let needle = needles[emit.gen_range(0..needles.len())];

        let results = ["\"found\"", "\"yes\"", "\"match\"", "\"true\""];
        let defaults = ["\"not found\"", "\"no\"", "\"miss\"", "\"false\""];
        let idx = emit.gen_range(0..results.len());

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{\n    {}.{}(\"{}\") => {}\n    _ => {}\n}}",
            name, var, method, needle, results[idx], defaults[idx]
        ))
    }
}

fn collect_string_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
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
        assert_eq!(WhenWithContains.name(), "when_with_contains");
    }

    #[test]
    fn returns_none_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            WhenWithContains
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_when_with_predicate() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenWithContains.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}
