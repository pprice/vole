//! Rule: type-level static method calls on built-in types.
//!
//! Exercises the static dispatch path in the compiler by calling built-in
//! static methods on primitive types:
//! ```vole
//! let result0 = i64.min_value()
//! let result1 = (42 > i64.default_value())
//! let result2 = f64.infinity()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StaticMethodCall;

impl StmtRule for StaticMethodCall {
    fn name(&self) -> &'static str {
        "static_method_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let variant = emit.gen_range(0..3);
        match variant {
            0 => {
                // i64 static call: i64.default_value(), i64.min_value(), i64.max_value()
                // Also includes i32 and bool/string variants
                let call = match emit.gen_range(0..8) {
                    0 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::I64),
                            false,
                        );
                        "i64.default_value()".to_string()
                    }
                    1 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::I64),
                            false,
                        );
                        "i64.min_value()".to_string()
                    }
                    2 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::I64),
                            false,
                        );
                        "i64.max_value()".to_string()
                    }
                    3 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::I32),
                            false,
                        );
                        "i32.default_value()".to_string()
                    }
                    4 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::I32),
                            false,
                        );
                        "i32.min_value()".to_string()
                    }
                    5 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::I32),
                            false,
                        );
                        "i32.max_value()".to_string()
                    }
                    6 => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::Bool),
                            false,
                        );
                        "bool.default_value()".to_string()
                    }
                    _ => {
                        scope.add_local(
                            name.clone(),
                            TypeInfo::Primitive(PrimitiveType::String),
                            false,
                        );
                        "string.default_value()".to_string()
                    }
                };
                Some(format!("let {} = {}", name, call))
            }
            1 => {
                // Comparison with static value: (literal > Type.default_value())
                let (lhs, static_call) = match emit.gen_range(0..3) {
                    0 => (format!("{}", emit.random_in(0, 100)), "i64.default_value()"),
                    1 => (format!("{}", emit.random_in(0, 100)), "i32.default_value()"),
                    _ => (format!("{}", emit.random_in(0, 50)), "i64.default_value()"),
                };
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!("let {} = ({} > {})", name, lhs, static_call))
            }
            _ => {
                // f64 special values: f64.infinity(), f64.neg_infinity(), f64.epsilon()
                let call = match emit.gen_range(0..4) {
                    0 => "f64.infinity()",
                    1 => "f64.neg_infinity()",
                    2 => "f64.epsilon()",
                    _ => "f64.default_value()",
                };
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                Some(format!("let {} = {}", name, call))
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
        assert_eq!(StaticMethodCall.name(), "static_method_call");
    }

    #[test]
    fn generates_static_method_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StaticMethodCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
    }

    #[test]
    fn adds_one_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        StaticMethodCall.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
    }

    #[test]
    fn all_variants_produce_valid_output() {
        let table = SymbolTable::new();
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // Run with many seeds to exercise all variants
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let result = StaticMethodCall.generate(&mut scope, &mut emit, &params);
            assert!(result.is_some(), "seed {seed} returned None");
            let text = result.unwrap();
            assert!(text.starts_with("let "), "seed {seed} got: {text}");

            // Each call should contain a static method pattern
            let has_static = text.contains("i64.")
                || text.contains("i32.")
                || text.contains("f64.")
                || text.contains("bool.")
                || text.contains("string.");
            assert!(has_static, "seed {seed} missing static call: {text}");
        }
    }
}
