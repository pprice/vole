//! Rule: iterator factory method calls producing `[i64]` arrays.
//!
//! Generates let-bindings using bare iterator factory functions:
//! ```vole
//! let local0 = repeat(7).take(3).collect()   // [7, 7, 7]
//! let local1 = once(12).collect()             // [12]
//! let local2 = empty().collect()              // []
//! ```
//!
//! Stresses iterator factory codegen, method chaining, and collect-to-array.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterFactoryLet;

/// The three iterator factory variants we can generate.
enum Variant {
    /// `repeat(N).take(M).collect()` -- infinite iterator of N, take M elements.
    Repeat { value: usize, take: usize },
    /// `once(N).collect()` -- single-element iterator.
    Once { value: usize },
    /// `empty().collect()` -- empty iterator producing `[i64]`.
    Empty,
}

impl StmtRule for IterFactoryLet {
    fn name(&self) -> &'static str {
        "iter_factory_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if !scope.can_recurse() {
            return None;
        }

        let variant_choice = emit.gen_range(0..3);
        let variant = match variant_choice {
            0 => Variant::Repeat {
                value: emit.gen_range(0..21),
                take: emit.gen_range(1..6),
            },
            1 => Variant::Once {
                value: emit.gen_range(0..21),
            },
            _ => Variant::Empty,
        };

        let var_name = scope.fresh_name();
        let indent = emit.indent_str();

        let expr = match &variant {
            Variant::Repeat { value, take } => {
                format!("repeat({}).take({}).collect()", value, take)
            }
            Variant::Once { value } => {
                format!("once({}).collect()", value)
            }
            Variant::Empty => "empty().collect()".to_string(),
        };

        // Register the local for repeat/once variants (non-empty arrays).
        // Do NOT register empty() results -- array_index rule assumes 2+ elements.
        if !matches!(variant, Variant::Empty) {
            let array_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
            scope.add_local(var_name.clone(), array_type, false);
        }

        Some(format!("{}let {} = {}", indent, var_name, expr))
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
        assert_eq!(IterFactoryLet.name(), "iter_factory_let");
    }

    #[test]
    fn generates_valid_output() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterFactoryLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();

        // Must contain `let` and `.collect()`
        assert!(text.contains("let "), "expected let binding, got: {text}");
        assert!(
            text.contains(".collect()"),
            "expected .collect(), got: {text}"
        );
    }

    #[test]
    fn all_three_variants_appear() {
        let mut has_repeat = false;
        let mut has_once = false;
        let mut has_empty = false;

        for seed in 0..200u64 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let text = IterFactoryLet
                .generate(&mut scope, &mut emit, &rule_params)
                .unwrap();

            if text.contains("repeat(") {
                has_repeat = true;
            }
            if text.contains("once(") {
                has_once = true;
            }
            if text.contains("empty()") {
                has_empty = true;
            }
        }

        assert!(has_repeat, "repeat variant never appeared in 200 seeds");
        assert!(has_once, "once variant never appeared in 200 seeds");
        assert!(has_empty, "empty variant never appeared in 200 seeds");
    }

    #[test]
    fn empty_variant_does_not_register_local() {
        // Run seeds until we get an empty() variant and verify no local was added.
        for seed in 0..200u64 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let text = IterFactoryLet
                .generate(&mut scope, &mut emit, &rule_params)
                .unwrap();

            if text.contains("empty()") {
                assert!(
                    scope.locals.is_empty(),
                    "seed {seed}: empty() variant should not register a local, but found: {:?}",
                    scope.locals
                );
                return;
            }
        }
        panic!("empty variant never appeared in 200 seeds");
    }
}
