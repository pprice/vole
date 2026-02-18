//! Rule: string predicate let-binding.
//!
//! Generates `s.contains("sub")`, `s.starts_with("hel")`, or `s.ends_with("rld")`
//! as a bool-typed let-binding. Falls back to a string literal receiver when no
//! string variables are in scope.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringPredicate;

impl StmtRule for StringPredicate {
    fn name(&self) -> &'static str {
        "string_predicate"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        let name = scope.fresh_name();

        let method = match emit.gen_range(0..3) {
            0 => "contains",
            1 => "starts_with",
            _ => "ends_with",
        };

        let search_strs = ["hello", "world", "a", "str", "test", "", "xyz", "lo"];
        let search = search_strs[emit.gen_range(0..search_strs.len())];

        let expr = if string_vars.is_empty() {
            let literals = [
                "\"hello world\"",
                "\"testing\"",
                "\"abcdef\"",
                "\"vole lang\"",
            ];
            let lit = literals[emit.gen_range(0..literals.len())];
            format!("{}.{}(\"{}\")", lit, method, search)
        } else {
            let var = &string_vars[emit.gen_range(0..string_vars.len())];
            format!("{}.{}(\"{}\")", var, method, search)
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
        assert_eq!(StringPredicate.name(), "string_predicate");
    }

    #[test]
    fn generates_with_literal_fallback() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringPredicate.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("contains") || text.contains("starts_with") || text.contains("ends_with"),
            "got: {text}"
        );
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

        let result = StringPredicate.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("s."), "got: {text}");
    }
}
