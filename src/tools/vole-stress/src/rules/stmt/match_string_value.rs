//! Rule: match on string value with string literal patterns.
//!
//! Finds a string variable in scope and generates a match against string
//! literal arms:
//! ```vole
//! let result = match color {
//!     "red" => 1
//!     "green" => 2
//!     "blue" => 3
//!     _ => 0
//! }
//! ```
//! Two variants: arms return i64 literals, or arms return string literals.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

/// Pool of common string literals used as match patterns.
const PATTERN_POOL: &[&str] = &[
    "red", "green", "blue", "hello", "world", "foo", "bar", "alpha", "beta", "gamma", "yes", "no",
    "on", "off", "left", "right",
];

/// String results for string → string variant.
const STRING_RESULTS: &[&str] = &[
    "primary",
    "secondary",
    "unknown",
    "found",
    "missing",
    "warm",
    "cool",
    "neutral",
];

pub struct MatchStringValue;

impl StmtRule for MatchStringValue {
    fn name(&self) -> &'static str {
        "match_string_value"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        if string_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..string_vars.len());
        let var = &string_vars[idx].clone();
        let name = scope.fresh_name();
        let indent = emit.indent_str();

        // Choose variant: 0 = string → i64, 1 = string → string
        let variant = emit.gen_range(0..2);

        let num_arms = emit.random_in(3, 5);

        // Pick distinct patterns from the pool
        let mut used_indices = Vec::new();
        let mut arms = Vec::new();
        for _ in 0..num_arms {
            let mut pat_idx = emit.gen_range(0..PATTERN_POOL.len());
            while used_indices.contains(&pat_idx) {
                pat_idx = (pat_idx + 1) % PATTERN_POOL.len();
            }
            used_indices.push(pat_idx);
            let pattern = PATTERN_POOL[pat_idx];

            let arm_expr = match variant {
                0 => {
                    let n = emit.random_in(0, 99) as i64;
                    format!("{}", n)
                }
                _ => {
                    let str_idx = emit.gen_range(0..STRING_RESULTS.len());
                    format!("\"{}\"", STRING_RESULTS[str_idx])
                }
            };

            arms.push(format!("{}    \"{}\" => {}", indent, pattern, arm_expr));
        }

        // Wildcard arm
        let default_expr = match variant {
            0 => "0".to_string(),
            _ => "\"unknown\"".to_string(),
        };
        arms.push(format!("{}    _ => {}", indent, default_expr));

        let result_type = match variant {
            0 => TypeInfo::Primitive(PrimitiveType::I64),
            _ => TypeInfo::Primitive(PrimitiveType::String),
        };

        scope.add_local(name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            name,
            var,
            arms.join("\n"),
            indent,
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchStringValue.name(), "match_string_value");
    }

    #[test]
    fn returns_none_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            MatchStringValue
                .generate(&mut scope, &mut emit, &test_params())
                .is_none()
        );
    }

    #[test]
    fn generates_with_string_variable() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "color".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchStringValue.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match color"), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
        // Should have at least 3 quoted pattern arms
        let quote_count = text.matches('"').count();
        // Each arm has 2 quotes for the pattern; wildcard has none.
        // For string→string variant, arm results also have quotes.
        assert!(
            quote_count >= 6,
            "expected at least 3 pattern arms, got: {text}"
        );
    }

    #[test]
    fn adds_one_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MatchStringValue.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn result_type_is_i64_or_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "fruit".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MatchStringValue.generate(&mut scope, &mut emit, &test_params());

        // The added local should be either i64 or string
        let (_, ref ty, _) = scope.locals[1]; // index 1 because index 0 is "fruit"
        assert!(
            matches!(
                ty,
                TypeInfo::Primitive(PrimitiveType::I64)
                    | TypeInfo::Primitive(PrimitiveType::String)
            ),
            "expected i64 or string, got: {:?}",
            ty
        );
    }

    #[test]
    fn uses_param_from_scope() {
        let table = SymbolTable::new();
        let params_list = [crate::symbols::ParamInfo {
            name: "input".into(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
            has_default: false,
        }];
        let mut scope = Scope::new(&params_list, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchStringValue.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match input"), "got: {text}");
    }
}
