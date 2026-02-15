//! Rule: string replace/replace_all let-binding.
//!
//! Generates `.replace()` or `.replace_all()` calls on string variables or literals.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringReplace;

impl StmtRule for StringReplace {
    fn name(&self) -> &'static str {
        "string_replace"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        let name = scope.fresh_name();
        let method = if emit.gen_bool(0.5) {
            "replace"
        } else {
            "replace_all"
        };

        let expr = if !string_vars.is_empty() && emit.gen_bool(0.5) {
            let var = &string_vars[emit.gen_range(0..string_vars.len())];
            let (old, new) = match emit.gen_range(0..3) {
                0 => ("a", "b"),
                1 => ("hello", "hi"),
                _ => (" ", "_"),
            };
            format!("{}.{}(\"{}\", \"{}\")", var, method, old, new)
        } else {
            let (src, old, new) = match emit.gen_range(0..3) {
                0 => ("hello world", "world", "there"),
                1 => ("aabaa", "a", "x"),
                _ => ("foo bar baz", " ", "-"),
            };
            format!("\"{}\".{}(\"{}\", \"{}\")", src, method, old, new)
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringReplace.name(), "string_replace");
    }

    #[test]
    fn generates_replace() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringReplace.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("replace") || text.contains("replace_all"),
            "got: {text}"
        );
    }
}
