//! Rule: wildcard-only match expression.
//!
//! Picks a variable in scope and generates a match with a single wildcard arm:
//! ```vole
//! let result = match var {
//!     _ => <expr>
//! }
//! ```
//! This exercises the degenerate match codepath where only the default arm exists.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

// Re-used by other match rules in this directory.
pub(super) fn collect_matchable_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if is_matchable(ty) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if is_matchable(&param.param_type) {
            out.push(param.name.clone());
        }
    }
    out
}

fn is_matchable(ty: &TypeInfo) -> bool {
    matches!(
        ty,
        TypeInfo::Primitive(
            PrimitiveType::I64
                | PrimitiveType::I32
                | PrimitiveType::String
                | PrimitiveType::Bool
                | PrimitiveType::F64
        )
    )
}

pub struct WildcardMatch;

impl StmtRule for WildcardMatch {
    fn name(&self) -> &'static str {
        "wildcard_match"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = collect_matchable_vars(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let scrutinee = &candidates[idx];

        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();
        let value_expr = emit.literal(&result_type);

        let indent = emit.indent_str();

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}    _ => {}\n{}}}",
            result_name, scrutinee, indent, value_expr, indent
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
    fn name_is_correct() {
        assert_eq!(WildcardMatch.name(), "wildcard_match");
    }

    #[test]
    fn returns_none_without_variables() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            WildcardMatch
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_i64_variable() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WildcardMatch.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match x"), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }

    #[test]
    fn adds_result_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "v".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let initial_len = scope.locals.len();
        WildcardMatch.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), initial_len + 1);
    }
}
