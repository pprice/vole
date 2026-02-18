//! Rules: string split operations.
//!
//! Two rules covering string splitting:
//! - `StringSplitLet`: `let parts = "a,b,c".split(",").collect()` with optional
//!   chained iterator operations (`.count()`, `.first()`).
//! - `StringSplitFor`: split-then-iterate pattern that builds a string by
//!   concatenating all parts in a for loop.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

// ---------------------------------------------------------------------------
// StringSplitLet
// ---------------------------------------------------------------------------

pub struct StringSplitLet;

impl StmtRule for StringSplitLet {
    fn name(&self) -> &'static str {
        "string_split_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let words: &[&str] = &[
            "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta",
        ];
        let delimiters = [",", ";", "::", "-", "_"];
        let delim = delimiters[emit.gen_range(0..delimiters.len())];

        // Pick 2-4 words
        let word_count = emit.random_in(2, 4);
        let mut selected: Vec<&str> = Vec::new();
        for _ in 0..word_count {
            selected.push(words[emit.gen_range(0..words.len())]);
        }
        let joined = selected.join(delim);

        let name = scope.fresh_name();

        // 70% collect to [string], 15% count (i64), 15% first (string?)
        let choice = emit.gen_range(0..20);
        if choice < 14 {
            // Collect to [string]
            scope.add_local(
                name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );
            Some(format!(
                "let {} = \"{}\".split(\"{}\").collect()",
                name, joined, delim
            ))
        } else if choice < 17 {
            // Count -> i64
            scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
            Some(format!(
                "let {} = \"{}\".split(\"{}\").count()",
                name, joined, delim
            ))
        } else {
            // First -> string? (use ?? to unwrap to string)
            scope.add_local(
                name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );
            Some(format!(
                "let {} = \"{}\".split(\"{}\").first() ?? \"\"",
                name, joined, delim
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// StringSplitFor
// ---------------------------------------------------------------------------

pub struct StringSplitFor;

impl StmtRule for StringSplitFor {
    fn name(&self) -> &'static str {
        "string_split_for"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let parts_name = scope.fresh_name();
        let acc_name = scope.fresh_name();
        let iter_name = scope.fresh_name();

        let strings = [
            ("\"alpha,beta,gamma\"", "\",\""),
            ("\"hello world foo\"", "\" \""),
            ("\"a-b-c-d\"", "\"-\""),
            ("\"one;two;three\"", "\";\""),
        ];
        let choice = emit.gen_range(0..strings.len());
        let (s, delim) = strings[choice];

        // Protect accumulator
        scope.protected_vars.push(acc_name.clone());

        scope.add_local(
            parts_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );
        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "let {} = {}.split({}).collect()\n\
             let mut {} = \"\"\n\
             for {} in {}.iter() {{\n\
             {} = {} + {}\n\
             }}",
            parts_name, s, delim, acc_name, iter_name, parts_name, acc_name, acc_name, iter_name,
        ))
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
    fn split_let_generates_split_collect() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringSplitLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".split("));
    }

    #[test]
    fn split_let_adds_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        StringSplitLet.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
    }

    #[test]
    fn split_for_generates_for_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringSplitFor.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".split("));
        assert!(text.contains("for "));
        assert!(text.contains(".iter()"));
    }

    #[test]
    fn split_for_protects_accumulator() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        StringSplitFor.generate(&mut scope, &mut emit, &params);
        assert!(!scope.protected_vars.is_empty());
    }

    #[test]
    fn names_are_correct() {
        assert_eq!(StringSplitLet.name(), "string_split_let");
        assert_eq!(StringSplitFor.name(), "string_split_for");
    }
}
