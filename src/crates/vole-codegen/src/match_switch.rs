// src/codegen/match_switch.rs
//
// Switch-based optimization for match expressions with dense integer literal arms.
// Uses Cranelift's `Switch` to emit O(1) jump table dispatch instead of O(n) brif chains.

use cranelift::frontend::Switch;
use cranelift::prelude::*;
use cranelift_codegen::ir::BlockArg;

use vole_frontend::{ExprKind, MatchExpr, PatternKind, UnaryOp};
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::types::CompiledValue;
use crate::errors::CodegenResult;

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
                arm_values.push((i, value));
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

/// Emit a match expression using Cranelift's Switch for O(1) dispatch.
///
/// Creates a body block for each arm plus a default block, wires up the Switch,
/// then compiles each arm body and merges results.
pub(crate) fn emit_switch_match(
    cg: &mut Cg,
    match_expr: &MatchExpr,
    analysis: SwitchAnalysis,
    scrutinee: CompiledValue,
) -> CodegenResult<CompiledValue> {
    let merge_block = cg.builder.create_block();
    cg.builder.append_block_param(merge_block, types::I64);

    // Create body blocks for each arm
    let body_blocks: Vec<Block> = match_expr
        .arms
        .iter()
        .map(|_| cg.builder.create_block())
        .collect();

    // Default block: wildcard arm or trap
    let default_block = if let Some(wc_idx) = analysis.wildcard_idx {
        body_blocks[wc_idx]
    } else {
        cg.builder.create_block()
    };

    // Build and emit the Switch
    let mut switch = Switch::new();
    for &(arm_idx, value) in &analysis.arm_values {
        // Use two's complement representation so negative i64 values
        // map to the upper half of u64 range (fits within i64 type bounds)
        let entry = value as u64 as u128;
        switch.set_entry(entry, body_blocks[arm_idx]);
    }
    switch.emit(cg.builder, scrutinee.value, default_block);

    // If there's no wildcard, the default block is a trap
    if analysis.wildcard_idx.is_none() {
        cg.switch_and_seal(default_block);
        cg.builder.ins().trap(TrapCode::unwrap_user(1));
    }

    // Compile each arm body
    let mut result_type_id = TypeId::VOID;

    for (i, arm) in match_expr.arms.iter().enumerate() {
        cg.builder.switch_to_block(body_blocks[i]);
        cg.builder.seal_block(body_blocks[i]);

        // For literal arms, no variable bindings needed (scrutinee is just matched)
        // For wildcard arm, no bindings either
        let body_val = cg.expr(&arm.body)?;

        if i == 0 || (result_type_id == TypeId::VOID && body_val.type_id != TypeId::VOID) {
            result_type_id = body_val.type_id;
        }

        let result_val = if body_val.ty != types::I64 {
            match body_val.ty {
                types::I8 => cg.builder.ins().sextend(types::I64, body_val.value),
                types::I32 => cg.builder.ins().sextend(types::I64, body_val.value),
                _ => body_val.value,
            }
        } else {
            body_val.value
        };

        let result_arg = BlockArg::from(result_val);
        cg.builder.ins().jump(merge_block, &[result_arg]);
    }

    cg.switch_and_seal(merge_block);

    let merged_value = cg.builder.block_params(merge_block)[0];
    let target_cty = cg.cranelift_type(result_type_id);
    let (result, result_ty) = if target_cty != types::I64 && target_cty.is_int() {
        (
            cg.builder.ins().ireduce(target_cty, merged_value),
            target_cty,
        )
    } else {
        (merged_value, types::I64)
    };

    Ok(CompiledValue::new(result, result_ty, result_type_id))
}
