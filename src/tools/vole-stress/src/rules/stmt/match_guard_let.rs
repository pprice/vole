//! Rule: match expression with guard conditions using `_ if cond => value`.
//!
//! Finds an i64-typed variable in scope and generates:
//! ```vole
//! let result = match var {
//!     _ if var > 10 => "big"
//!     _ if var > 0 => "small"
//!     _ => "zero_or_neg"
//! }
//! ```
//! Or for numeric results:
//! ```vole
//! let result = match var {
//!     _ if var > 0 => var * 2
//!     _ if var == 0 => 0
//!     _ => var * -1
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchGuardLet;

impl StmtRule for MatchGuardLet {
    fn name(&self) -> &'static str {
        "match_guard_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = collect_i64_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var_name = &candidates[idx];

        let use_string_result = emit.gen_bool(0.5);
        let arm_count = emit.random_in(2, 4);
        let indent = emit.indent_str();
        let result_name = scope.fresh_name();

        let mut arms = Vec::new();

        if use_string_result {
            generate_string_arms(emit, var_name, arm_count, &indent, &mut arms);
        } else {
            generate_i64_arms(emit, var_name, arm_count, &indent, &mut arms);
        }

        // Always end with a bare wildcard arm for exhaustiveness
        let default_expr = if use_string_result {
            emit.literal(&TypeInfo::Primitive(PrimitiveType::String))
        } else {
            emit.literal(&TypeInfo::Primitive(PrimitiveType::I64))
        };
        arms.push(format!("{}    _ => {}", indent, default_expr));

        let result_type = if use_string_result {
            TypeInfo::Primitive(PrimitiveType::String)
        } else {
            TypeInfo::Primitive(PrimitiveType::I64)
        };

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            result_name,
            var_name,
            arms.join("\n"),
            indent,
        ))
    }
}

/// Collect all i64 variables from scope (locals and params).
fn collect_i64_candidates(scope: &Scope) -> Vec<String> {
    let mut candidates = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
            candidates.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(&param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            candidates.push(param.name.clone());
        }
    }
    candidates
}

/// Generate guarded arms with string result values.
fn generate_string_arms(
    emit: &mut Emit,
    var_name: &str,
    count: usize,
    indent: &str,
    arms: &mut Vec<String>,
) {
    let string_type = TypeInfo::Primitive(PrimitiveType::String);
    for _ in 0..count {
        let cond = random_guard_condition(emit, var_name);
        let value = emit.literal(&string_type);
        arms.push(format!("{}    _ if {} => {}", indent, cond, value));
    }
}

/// Generate guarded arms with i64 result values.
fn generate_i64_arms(
    emit: &mut Emit,
    var_name: &str,
    count: usize,
    indent: &str,
    arms: &mut Vec<String>,
) {
    let i64_type = TypeInfo::Primitive(PrimitiveType::I64);
    for _ in 0..count {
        let cond = random_guard_condition(emit, var_name);
        let value = if emit.gen_bool(0.4) {
            // Sometimes use the matched variable in an expression
            let ops = ["*", "+", "-"];
            let op = ops[emit.gen_range(0..ops.len())];
            let lit = emit.gen_i64_range(1, 10);
            format!("{} {} {}", var_name, op, lit)
        } else {
            emit.literal(&i64_type)
        };
        arms.push(format!("{}    _ if {} => {}", indent, cond, value));
    }
}

/// Generate a random guard condition comparing `var_name` against a literal.
fn random_guard_condition(emit: &mut Emit, var_name: &str) -> String {
    let ops = [">", "<", "==", ">=", "<=", "!="];
    let op = ops[emit.gen_range(0..ops.len())];
    let literal = emit.gen_i64_range(-10, 20);
    format!("{} {} {}", var_name, op, literal)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue, StmtRule};
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
        assert_eq!(MatchGuardLet.name(), "match_guard_let");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            MatchGuardLet
                .generate(&mut scope, &mut emit, &test_params())
                .is_none()
        );
    }

    #[test]
    fn returns_none_with_only_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            MatchGuardLet
                .generate(&mut scope, &mut emit, &test_params())
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

        let result = MatchGuardLet.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match x"), "got: {text}");
        assert!(
            text.contains("_ if"),
            "should have guarded arms, got: {text}"
        );
        assert!(
            text.contains("_ =>"),
            "should have bare wildcard, got: {text}"
        );
    }

    #[test]
    fn adds_one_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MatchGuardLet.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn bare_wildcard_is_last_arm() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchGuardLet
            .generate(&mut scope, &mut emit, &test_params())
            .unwrap();
        let lines: Vec<&str> = result.lines().collect();
        // The second-to-last line (before the closing `}`) should be the bare `_ =>`
        let last_arm = lines[lines.len() - 2].trim();
        assert!(
            last_arm.starts_with("_ =>") && !last_arm.contains("_ if"),
            "last arm should be bare wildcard, got: {last_arm}"
        );
    }

    #[test]
    fn generates_multiple_seeds_without_panic() {
        for seed in 0..50 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);
            scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let result = MatchGuardLet
                .generate(&mut scope, &mut emit, &test_params())
                .unwrap();
            assert!(result.contains("match x"), "seed {seed}: {result}");
            assert!(result.contains("_ if"), "seed {seed}: missing guard");
            assert!(
                result.contains("_ =>"),
                "seed {seed}: missing bare wildcard"
            );
        }
    }
}
