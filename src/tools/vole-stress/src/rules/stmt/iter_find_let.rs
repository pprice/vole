//! Rule: `.iter().find(predicate)` on i64 arrays.
//!
//! Produces `i64?` (Optional i64) — the first element matching the predicate,
//! or `nil` if none match.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterFindLet;

impl StmtRule for IterFindLet {
    fn name(&self) -> &'static str {
        "iter_find_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Only i64 arrays.
        let i64_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem)| matches!(elem, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _)| name)
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..i64_arrays.len());
        let arr_name = &i64_arrays[idx];
        let name = scope.fresh_name();

        // Pick a comparison operator and a suitable operand.
        let predicate = match emit.gen_range(0..3) {
            0 => {
                // x > N, N in 0..=10
                let n = emit.random_in(0, 10);
                format!("(x) => x > {}", n)
            }
            1 => {
                // x == N, N in 0..=2
                let n = emit.random_in(0, 2);
                format!("(x) => x == {}", n)
            }
            _ => {
                // x < N, N in 0..=10
                let n = emit.random_in(0, 10);
                format!("(x) => x < {}", n)
            }
        };

        let result_type = TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
        scope.add_local(name.clone(), result_type, false);

        Some(format!(
            "let {} = {}.iter().find({})",
            name, arr_name, predicate
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, PrimitiveType, SymbolTable};
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
        assert_eq!(IterFindLet.name(), "iter_find_let");
    }

    #[test]
    fn generates_find_on_i64_array() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterFindLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".iter().find("),
            "expected .iter().find(...), got: {text}"
        );
        assert!(
            text.contains("(x) => x > ")
                || text.contains("(x) => x == ")
                || text.contains("(x) => x < "),
            "expected a comparison predicate, got: {text}"
        );
    }

    #[test]
    fn returns_none_for_string_array() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "names".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterFindLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none(), "string arrays should not produce find");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "x".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterFindLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn registers_optional_i64_type() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterFindLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());

        // The local added to scope should be Optional(i64).
        let locals = &scope.locals;
        assert_eq!(locals.len(), 1);
        let (_, ty, _) = &locals[0];
        assert_eq!(
            *ty,
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64)))
        );
    }
}
