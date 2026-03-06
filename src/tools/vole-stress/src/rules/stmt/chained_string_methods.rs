//! Rule: deeply chained string method calls.
//!
//! Generates chains like `"hello world".trim().to_lower().replace("hello", "hi").to_upper().trim()`
//! to stress method resolution and RC management for intermediate string temporaries.
//! All methods in the chain return strings, so the result is always `string`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ChainedStringMethods;

/// Short replacement pairs for `.replace()` calls.
const REPLACE_PAIRS: &[(&str, &str)] = &[
    ("a", "b"),
    ("x", "y"),
    ("o", "0"),
    ("e", "i"),
    ("h", "H"),
    ("l", "L"),
];

impl StmtRule for ChainedStringMethods {
    fn name(&self) -> &'static str {
        "chained_string_methods"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Either pick an existing string variable or fall back to a literal.
        let string_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .into_iter()
            .map(|v| v.name)
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let base = if string_vars.is_empty() || emit.gen_range(0..3) == 0 {
            "\"hello world\"".to_string()
        } else {
            string_vars[emit.gen_range(0..string_vars.len())].clone()
        };

        // Chain 4-6 string->string methods.
        let chain_len = emit.random_in(4, 6);
        let mut chain = String::new();
        for _ in 0..chain_len {
            match emit.gen_range(0..6) {
                0 => chain.push_str(".trim()"),
                1 => chain.push_str(".to_lower()"),
                2 => chain.push_str(".to_upper()"),
                3 => chain.push_str(".trim_start()"),
                4 => chain.push_str(".trim_end()"),
                _ => {
                    let pair = REPLACE_PAIRS[emit.gen_range(0..REPLACE_PAIRS.len())];
                    chain.push_str(&format!(".replace(\"{}\", \"{}\")", pair.0, pair.1));
                }
            }
        }

        let result_name = scope.fresh_name();
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}{}", result_name, base, chain))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(ChainedStringMethods.name(), "chained_string_methods");
    }

    #[test]
    fn generates_deep_chain_with_literal() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ChainedStringMethods.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
        // Must contain at least 4 method calls (chain_len 4-6).
        let dot_count = text.matches('.').count();
        // The literal "hello world" has no dots, so all dots are method calls.
        // With a variable base there's still no dots in names.
        assert!(dot_count >= 4, "expected >= 4 chained calls, got: {text}");
    }

    #[test]
    fn generates_chain_from_existing_var() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "s".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ChainedStringMethods.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".to_upper()")
                || text.contains(".to_lower()")
                || text.contains(".trim()")
                || text.contains(".replace("),
            "got: {text}"
        );
    }

    #[test]
    fn result_type_is_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ChainedStringMethods.generate(&mut scope, &mut emit, &params);

        // The freshly added local should be a string.
        let vars = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        assert!(!vars.is_empty(), "expected a string local in scope");
    }
}
