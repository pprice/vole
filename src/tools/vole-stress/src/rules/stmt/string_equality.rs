//! Rule: string equality edge cases.
//!
//! Generates tautological string comparisons:
//! `s == s`, `"" == ""`, `s.length() == s.length()`, `s + "" == s`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringEquality;

impl StmtRule for StringEquality {
    fn name(&self) -> &'static str {
        "string_equality"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        let name = scope.fresh_name();

        let expr = match emit.gen_range(0..5) {
            0 if !string_vars.is_empty() => {
                let var = &string_vars[emit.gen_range(0..string_vars.len())];
                format!("{} == {}", var, var)
            }
            1 => "\"\" == \"\"".to_string(),
            2 if !string_vars.is_empty() => {
                let var = &string_vars[emit.gen_range(0..string_vars.len())];
                format!("{}.length() == {}.length()", var, var)
            }
            3 if !string_vars.is_empty() => {
                let var = &string_vars[emit.gen_range(0..string_vars.len())];
                format!("{} + \"\" == {}", var, var)
            }
            _ => {
                let s = match emit.gen_range(0..3) {
                    0 => "hello",
                    1 => "test",
                    _ => "abc",
                };
                format!("\"{}\" == \"{}\"", s, s)
            }
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
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
        assert_eq!(StringEquality.name(), "string_equality");
    }

    #[test]
    fn generates_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringEquality.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=="), "got: {text}");
    }

    #[test]
    fn generates_with_string_var() {
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

        let result = StringEquality.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=="), "got: {text}");
    }
}
