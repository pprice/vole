//! Rule: closure whose body contains a `match` expression with guard conditions.
//!
//! Generates a closure that takes an i64 parameter and uses `match` with guard
//! conditions inside a block body, then calls the closure and binds the result.
//! Exercises closure compilation, match guards inside closures, and RC handling
//! across those boundaries.
//!
//! **Variant A -- string result:**
//! ```vole
//! let classify = (n: i64) => {
//!     return match n {
//!         _ if n > 10 => "big"
//!         _ if n > 0 => "small"
//!         _ => "non-positive"
//!     }
//! }
//! let result = classify(some_var)
//! ```
//!
//! **Variant B -- i64 result (optionally captures a variable):**
//! ```vole
//! let scale = 2
//! let compute = (n: i64) => {
//!     return match n {
//!         _ if n > 0 => n * scale
//!         _ if n == 0 => 0
//!         _ => n * -1
//!     }
//! }
//! let result = compute(some_var)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureMatchGuard;

impl StmtRule for ClosureMatchGuard {
    fn name(&self) -> &'static str {
        "closure_match_guard"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = collect_i64_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        // Pick an i64 variable to pass to the closure
        let idx = emit.gen_range(0..candidates.len());
        let arg_var = candidates[idx].clone();

        let use_string_result = emit.gen_bool(0.5);
        let arm_count = emit.random_in(2, 4);
        let indent = emit.indent_str();

        // Fresh names for the closure param, closure binding, and result
        let param_name = scope.fresh_name();
        let closure_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        // For i64 variant, ~30% chance to capture an existing i64 variable
        let capture_var = if !use_string_result && emit.gen_bool(0.3) {
            // Pick a different i64 var from scope to capture (if available)
            let other_candidates: Vec<&String> =
                candidates.iter().filter(|n| *n != &arg_var).collect();
            if !other_candidates.is_empty() {
                let cap_idx = emit.gen_range(0..other_candidates.len());
                Some(other_candidates[cap_idx].clone())
            } else {
                None
            }
        } else {
            None
        };

        let mut arms = Vec::new();

        if use_string_result {
            generate_string_arms(emit, &param_name, arm_count, &indent, &mut arms);
        } else {
            generate_i64_arms(
                emit,
                &param_name,
                arm_count,
                &indent,
                &capture_var,
                &mut arms,
            );
        }

        // Always end with a bare wildcard arm for exhaustiveness
        let default_expr = if use_string_result {
            emit.literal(&TypeInfo::Primitive(PrimitiveType::String))
        } else {
            emit.literal(&TypeInfo::Primitive(PrimitiveType::I64))
        };
        arms.push(format!("{}        _ => {}", indent, default_expr));

        let result_type = if use_string_result {
            TypeInfo::Primitive(PrimitiveType::String)
        } else {
            TypeInfo::Primitive(PrimitiveType::I64)
        };

        scope.add_local(result_name.clone(), result_type, false);

        // Build the closure body with `return match`
        let closure_body = format!(
            "({}: i64) => {{\n{}    return match {} {{\n{}\n{}    }}\n{}}}",
            param_name,
            indent,
            param_name,
            arms.join("\n"),
            indent,
            indent,
        );

        // Assemble multi-line output
        Some(format!(
            "let {} = {}\n{}let {} = {}({})",
            closure_name, closure_body, indent, result_name, closure_name, arg_var,
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
    param_name: &str,
    count: usize,
    indent: &str,
    arms: &mut Vec<String>,
) {
    let string_type = TypeInfo::Primitive(PrimitiveType::String);
    for _ in 0..count {
        let cond = random_guard_condition(emit, param_name);
        let value = emit.literal(&string_type);
        arms.push(format!("{}        _ if {} => {}", indent, cond, value));
    }
}

/// Generate guarded arms with i64 result values.
fn generate_i64_arms(
    emit: &mut Emit,
    param_name: &str,
    count: usize,
    indent: &str,
    capture_var: &Option<String>,
    arms: &mut Vec<String>,
) {
    let i64_type = TypeInfo::Primitive(PrimitiveType::I64);
    for _ in 0..count {
        let cond = random_guard_condition(emit, param_name);
        let value = if let Some(cap) = capture_var {
            if emit.gen_bool(0.4) {
                // Use captured variable in arm expression
                let ops = ["*", "+", "-"];
                let op = ops[emit.gen_range(0..ops.len())];
                format!("{} {} {}", param_name, op, cap)
            } else {
                i64_arm_value(emit, param_name, &i64_type)
            }
        } else {
            i64_arm_value(emit, param_name, &i64_type)
        };
        arms.push(format!("{}        _ if {} => {}", indent, cond, value));
    }
}

/// Generate an i64 arm value expression.
fn i64_arm_value(emit: &mut Emit, param_name: &str, i64_type: &TypeInfo) -> String {
    if emit.gen_bool(0.4) {
        // Use the param in an expression
        let ops = ["*", "+", "-"];
        let op = ops[emit.gen_range(0..ops.len())];
        let lit = emit.gen_i64_range(1, 10);
        format!("{} {} {}", param_name, op, lit)
    } else {
        emit.literal(i64_type)
    }
}

/// Generate a random guard condition comparing `param_name` against a literal.
fn random_guard_condition(emit: &mut Emit, param_name: &str) -> String {
    let ops = [">", "<", "==", ">=", "<=", "!="];
    let op = ops[emit.gen_range(0..ops.len())];
    let literal = emit.gen_i64_range(-10, 20);
    format!("{} {} {}", param_name, op, literal)
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
        assert_eq!(ClosureMatchGuard.name(), "closure_match_guard");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            ClosureMatchGuard
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

        let result = ClosureMatchGuard.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("=>"),
            "should have closure syntax, got: {text}"
        );
        assert!(
            text.contains("return match"),
            "should have return match, got: {text}"
        );
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
    fn adds_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        ClosureMatchGuard.generate(&mut scope, &mut emit, &test_params());
        // Should add at least 1 local (the result variable)
        assert!(
            scope.locals.len() > initial_len,
            "expected new locals, had {} now {}",
            initial_len,
            scope.locals.len()
        );
    }

    #[test]
    fn generates_multiple_seeds_without_panic() {
        for seed in 0..50 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);
            scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
            scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let result = ClosureMatchGuard
                .generate(&mut scope, &mut emit, &test_params())
                .unwrap();
            assert!(
                result.contains("return match"),
                "seed {seed}: missing return match"
            );
            assert!(result.contains("_ if"), "seed {seed}: missing guard");
            assert!(
                result.contains("_ =>"),
                "seed {seed}: missing bare wildcard"
            );
        }
    }
}
