// src/codegen/match_switch.rs
//
// Switch-based optimization for match expressions with dense integer literal arms.
// Uses Cranelift's `Switch` to emit O(1) jump table dispatch instead of O(n) brif chains.

use std::collections::HashSet;

use vole_frontend::{ExprKind, MatchExpr, PatternKind, UnaryOp};
use vole_sema::type_arena::TypeId;

/// Minimum number of non-default arms required to use the Switch optimization.
const MIN_SWITCH_ARMS: usize = 4;

/// Maximum ratio of (range size / arm count) for the range to be considered dense enough.
/// For example, arms [0, 1, 2, 5] have range 6, count 4, ratio 1.5 which is <= 2.0.
const MAX_DENSITY_RATIO: f64 = 2.0;

/// Result of analyzing match arms for Switch applicability.
pub(crate) struct SwitchAnalysis {
    /// Maps arm index -> integer literal value (excludes wildcard arm)
    pub arm_values: Vec<(usize, i64)>,
    /// Index of the wildcard/default arm, if any
    pub wildcard_idx: Option<usize>,
}

/// Try to extract a constant integer value from a pattern's literal expression.
/// Returns `Some(value)` for `IntLiteral(n)` or `Unary(Neg, IntLiteral(n))`.
fn extract_int_literal(expr: &vole_frontend::Expr) -> Option<i64> {
    match &expr.kind {
        ExprKind::IntLiteral(n, _) => Some(*n),
        ExprKind::Unary(unary) if unary.op == UnaryOp::Neg => {
            if let ExprKind::IntLiteral(n, _) = &unary.operand.kind {
                Some(-n)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Analyze match arms to determine if Switch optimization is applicable.
///
/// Requirements:
/// - Scrutinee is an integer type
/// - All non-wildcard arms have integer literal patterns with no guards
/// - At least `MIN_SWITCH_ARMS` non-wildcard arms
/// - The value range is dense enough (range / count <= MAX_DENSITY_RATIO)
pub(crate) fn analyze_switch(
    match_expr: &MatchExpr,
    scrutinee_type_id: TypeId,
) -> Option<SwitchAnalysis> {
    if !scrutinee_type_id.is_integer() {
        return None;
    }

    let mut arm_values = Vec::new();
    let mut seen_values = HashSet::new();
    let mut wildcard_idx = None;

    for (i, arm) in match_expr.arms.iter().enumerate() {
        // Guards prevent Switch optimization (guard needs per-arm evaluation)
        if arm.guard.is_some() {
            return None;
        }

        match &arm.pattern.kind {
            PatternKind::Wildcard => {
                if wildcard_idx.is_some() {
                    return None; // multiple wildcards - shouldn't happen but bail
                }
                wildcard_idx = Some(i);
            }
            PatternKind::Literal(lit_expr) => {
                let value = extract_int_literal(lit_expr)?;
                // Deduplicate: first-match-wins semantics — skip duplicate values
                if seen_values.insert(value) {
                    arm_values.push((i, value));
                }
            }
            _ => return None, // non-literal, non-wildcard pattern
        }
    }

    if arm_values.len() < MIN_SWITCH_ARMS {
        return None;
    }

    // Check density: range_size / arm_count <= MAX_DENSITY_RATIO
    let min_val = arm_values
        .iter()
        .map(|(_, v)| *v)
        .min()
        .expect("INTERNAL: match switch: arm_values empty after check");
    let max_val = arm_values
        .iter()
        .map(|(_, v)| *v)
        .max()
        .expect("INTERNAL: match switch: arm_values empty after check");
    let range_size = (max_val - min_val + 1) as f64;
    let arm_count = arm_values.len() as f64;

    if range_size / arm_count > MAX_DENSITY_RATIO {
        return None;
    }

    Some(SwitchAnalysis {
        arm_values,
        wildcard_idx,
    })
}
