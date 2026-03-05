//! Rule: static type method calls.
//!
//! Generates expressions like `i64.default_value()`, `i64.min_value()`,
//! `string.default_value()`, etc.  These stress static method resolution
//! and type-level dispatch in the compiler.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StaticTypeMethod;

impl ExprRule for StaticTypeMethod {
    fn name(&self) -> &'static str {
        "static_type_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(
        &self,
        _scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let methods: &[&str] = match expected_type {
            TypeInfo::Primitive(PrimitiveType::I64) => {
                &["i64.default_value()", "i64.min_value()", "i64.max_value()"]
            }
            TypeInfo::Primitive(PrimitiveType::I32) => {
                &["i32.default_value()", "i32.min_value()", "i32.max_value()"]
            }
            TypeInfo::Primitive(PrimitiveType::String) => &["string.default_value()"],
            TypeInfo::Primitive(PrimitiveType::Bool) => &["bool.default_value()"],
            _ => return None,
        };

        let idx = emit.gen_range(0..methods.len());
        Some(methods[idx].to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
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

    fn default_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StaticTypeMethod.name(), "static_type_method");
    }

    #[test]
    fn returns_none_for_unsupported_type() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        assert!(
            StaticTypeMethod
                .generate(
                    &scope,
                    &mut emit,
                    &params,
                    &TypeInfo::Primitive(PrimitiveType::F64),
                )
                .is_none()
        );

        assert!(
            StaticTypeMethod
                .generate(&scope, &mut emit, &params, &TypeInfo::Void)
                .is_none()
        );
    }

    #[test]
    fn generates_i64_static_method() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        let result = StaticTypeMethod
            .generate(
                &scope,
                &mut emit,
                &params,
                &TypeInfo::Primitive(PrimitiveType::I64),
            )
            .unwrap();

        let valid = ["i64.default_value()", "i64.min_value()", "i64.max_value()"];
        assert!(
            valid.contains(&result.as_str()),
            "unexpected result: {result}"
        );
    }

    #[test]
    fn generates_string_default_value() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        let result = StaticTypeMethod
            .generate(
                &scope,
                &mut emit,
                &params,
                &TypeInfo::Primitive(PrimitiveType::String),
            )
            .unwrap();

        assert_eq!(result, "string.default_value()");
    }

    #[test]
    fn generates_bool_default_value() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        let result = StaticTypeMethod
            .generate(
                &scope,
                &mut emit,
                &params,
                &TypeInfo::Primitive(PrimitiveType::Bool),
            )
            .unwrap();

        assert_eq!(result, "bool.default_value()");
    }
}
