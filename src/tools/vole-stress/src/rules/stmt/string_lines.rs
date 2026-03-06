//! Rule: `str.lines()` method — produces iterators over string lines.
//!
//! Generates patterns like:
//! - `let parts = s.lines().collect()` → `[string]`
//! - `let count = s.lines().count()` → `i64`
//! - `let first = s.lines().take(N).collect()` → `[string]`
//!
//! Uses string literals containing `\n` or string variables from scope.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringLines;

impl StmtRule for StringLines {
    fn name(&self) -> &'static str {
        "string_lines"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let string_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(n, _, _)| n.clone())
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        // Build a receiver: either a variable or a literal with newlines
        let receiver = if !string_vars.is_empty() && emit.gen_bool(0.4) {
            string_vars[emit.gen_range(0..string_vars.len())].clone()
        } else {
            let lines = emit.random_in(2, 5);
            let words = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta"];
            let parts: Vec<&str> = (0..lines)
                .map(|_| words[emit.gen_range(0..words.len())])
                .collect();
            format!("\"{}\"", parts.join("\\n"))
        };

        match emit.gen_range(0..4) {
            0 => {
                // .lines().collect() → [string]
                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!("let {} = {}.lines().collect()", name, receiver))
            }
            1 => {
                // .lines().count() → i64
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = {}.lines().count()", name, receiver))
            }
            2 => {
                // .lines().take(N).collect() → [string]
                let n = emit.random_in(1, 3);
                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}.lines().take({}).collect()",
                    name, receiver, n
                ))
            }
            _ => {
                // .lines().filter(...).collect() → [string]
                scope.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}.lines().filter((line) => line.length() > 0).collect()",
                    name, receiver
                ))
            }
        }
    }
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
        assert_eq!(StringLines.name(), "string_lines");
    }

    #[test]
    fn generates_with_literal() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringLines.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".lines()"), "got: {text}");
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

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringLines.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".lines()"), "got: {text}");
    }

    #[test]
    fn all_variants_contain_lines() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = StringLines.generate(&mut scope, &mut emit, &params) {
                assert!(text.contains(".lines()"), "seed {seed}: got: {text}");
            }
        }
    }
}
