//! Rule: match on a string-typed variable with literal pattern arms.
//!
//! Finds a string variable in scope and generates:
//! ```vole
//! let resultN = match stringVar {
//!     "alpha" => <expr>
//!     "beta"  => <expr>
//!     _ => <expr>
//! }
//! ```
//!
//! Supports optional unreachable in the wildcard arm (~10%) and optional
//! match guards on the wildcard (~15%).

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

/// Pool of short distinct string patterns for match arms.
const PATTERNS: &[&str] = &[
    "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa",
];

pub struct StringMatchLet;

impl StmtRule for StringMatchLet {
    fn name(&self) -> &'static str {
        "string_match_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.06)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .first()
            .is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let scrutinee = candidates[idx].name.clone();

        let use_unreachable = emit.gen_bool(0.10);
        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();

        let arm_count = emit.random_in(2, 3);
        let indent = emit.indented(|e| e.indent_str());

        if use_unreachable {
            let output =
                gen_unreachable_branch(scope, emit, &result_name, &result_type, arm_count, &indent);
            Some(output)
        } else {
            let output = gen_normal_branch(
                scope,
                emit,
                &result_name,
                &scrutinee,
                &result_type,
                arm_count,
                &indent,
            );
            Some(output)
        }
    }
}

/// Generate a match on a known literal so the wildcard is dead code (unreachable).
fn gen_unreachable_branch(
    scope: &mut Scope,
    emit: &mut Emit,
    result_name: &str,
    result_type: &TypeInfo,
    arm_count: usize,
    indent: &str,
) -> String {
    let known_idx = emit.gen_range(0..PATTERNS.len());
    let known_pattern = PATTERNS[known_idx];

    let mut arms = Vec::new();

    // First arm matches the known literal
    let arm_expr = match_arm_value(emit, result_type);
    arms.push(format!("{}\"{}\" => {}", indent, known_pattern, arm_expr));

    // Additional non-matching arms
    let mut used = std::collections::HashSet::new();
    used.insert(known_idx);
    for _ in 1..arm_count {
        let pi = pick_unused_pattern(emit, &mut used);
        let arm_expr = match_arm_value(emit, result_type);
        arms.push(format!("{}\"{}\" => {}", indent, PATTERNS[pi], arm_expr));
    }

    // Wildcard arm with unreachable
    arms.push(format!("{}_ => unreachable", indent));

    let close_indent = emit.indent_str();
    scope.add_local(result_name.to_string(), result_type.clone(), false);

    format!(
        "let {} = match \"{}\" {{\n{}\n{}}}",
        result_name,
        known_pattern,
        arms.join("\n"),
        close_indent,
    )
}

/// Generate a match on a string variable with literal pattern arms + wildcard.
fn gen_normal_branch(
    scope: &mut Scope,
    emit: &mut Emit,
    result_name: &str,
    scrutinee: &str,
    result_type: &TypeInfo,
    arm_count: usize,
    indent: &str,
) -> String {
    let mut arms = Vec::new();
    let mut used = std::collections::HashSet::new();

    for _ in 0..arm_count {
        let pi = pick_unused_pattern(emit, &mut used);
        let arm_expr = match_arm_value(emit, result_type);
        arms.push(format!("{}\"{}\" => {}", indent, PATTERNS[pi], arm_expr));
    }

    // ~15% chance of a guarded wildcard arm before the bare wildcard
    if emit.gen_bool(0.15) {
        let guard_cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        let guarded_expr = match_arm_value(emit, result_type);
        arms.push(format!("{}_ if {} => {}", indent, guard_cond, guarded_expr));
    }

    // Wildcard arm
    let wildcard_expr = match_arm_value(emit, result_type);
    arms.push(format!("{}_ => {}", indent, wildcard_expr));

    let close_indent = emit.indent_str();
    scope.add_local(result_name.to_string(), result_type.clone(), false);

    format!(
        "let {} = match {} {{\n{}\n{}}}",
        result_name,
        scrutinee,
        arms.join("\n"),
        close_indent,
    )
}

/// Generate a match arm value -- 25% chance of a nested when, otherwise a literal.
fn match_arm_value(emit: &mut Emit, result_type: &TypeInfo) -> String {
    if emit.gen_bool(0.25) {
        // Nested when expression
        let inner_indent = emit.indented(|e| e.indented(|e2| e2.indent_str()));
        let inner_close = emit.indented(|e| e.indent_str());
        let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        let true_val = emit.literal(result_type);
        let false_val = emit.literal(result_type);
        format!(
            "when {{\n{}{} => {}\n{}_ => {}\n{}}}",
            inner_indent, cond, true_val, inner_indent, false_val, inner_close
        )
    } else {
        emit.literal(result_type)
    }
}

/// Pick an unused index from `PATTERNS`.
fn pick_unused_pattern(emit: &mut Emit, used: &mut std::collections::HashSet<usize>) -> usize {
    loop {
        let pi = emit.gen_range(0..PATTERNS.len());
        if used.insert(pi) {
            return pi;
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
        assert_eq!(StringMatchLet.name(), "string_match_let");
    }

    #[test]
    fn returns_none_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringMatchLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_match_with_string_var() {
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
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringMatchLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "got: {text}");
        assert!(text.contains("=>"), "got: {text}");
    }
}
