//! Rule: .substring() on strings.
//!
//! Generates `"hello world".substring(0, 5)` and similar,
//! testing substring extraction with known-safe indices.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SubstringLet;

impl StmtRule for SubstringLet {
    fn name(&self) -> &'static str {
        "substring_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        let name = scope.fresh_name();

        let (receiver, max_len) = if !string_vars.is_empty() && emit.gen_bool(0.4) {
            (
                string_vars[emit.gen_range(0..string_vars.len())].clone(),
                3usize,
            )
        } else {
            let literals = [
                ("\"hello world\"", 11usize),
                ("\"testing\"", 7),
                ("\"abcdefghij\"", 10),
                ("\"vole lang\"", 9),
            ];
            let (lit, len) = literals[emit.gen_range(0..literals.len())];
            (lit.to_string(), len)
        };

        let start = emit.gen_range(0..max_len.min(4));
        let end = emit.gen_range(start..max_len + 1);

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = {}.substring({}, {})",
            name, receiver, start, end
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
        assert_eq!(SubstringLet.name(), "substring_let");
    }

    #[test]
    fn generates_substring() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SubstringLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".substring("), "got: {text}");
    }
}
