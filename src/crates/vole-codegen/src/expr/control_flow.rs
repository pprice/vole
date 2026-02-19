// src/codegen/expr/control_flow.rs
//
// Block, if, when expressions and control flow helpers.

use cranelift::prelude::*;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, RcLifecycle, type_id_to_cranelift};

use vole_frontend::ast::{BlockExpr, IfExpr, WhenExpr};
use vole_frontend::{ExprKind, NodeId};
use vole_sema::IsCheckResult;
use vole_sema::type_arena::TypeId;

use crate::ops::{sextend_const, try_constant_value};

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile an unreachable expression (never type / bottom type)
    /// This emits a panic with file:line info if reached at runtime.
    pub(super) fn unreachable_expr(&mut self, line: u32) -> CodegenResult<CompiledValue> {
        // Emit panic with location - this code should never be reached at runtime
        self.emit_panic_static("unreachable code reached", line)?;

        // Return a dummy value with the never type
        // The actual value doesn't matter since control never reaches here
        Ok(CompiledValue::new(
            self.iconst_cached(types::I64, 0),
            types::I64,
            TypeId::NEVER,
        ))
    }

    /// Compile a block expression: { stmts; trailing_expr }
    pub(super) fn block_expr(&mut self, block: &BlockExpr) -> CodegenResult<CompiledValue> {
        self.push_rc_scope();

        // Compile statements
        for stmt in &block.stmts {
            self.stmt(stmt)?;
        }

        // Compile trailing expression if present, otherwise return void
        let result = if let Some(ref trailing) = block.trailing_expr {
            self.expr(trailing)?
        } else {
            self.void_value()
        };

        // If the trailing expression is a local variable being returned from this
        // scope, skip its cleanup — ownership transfers to the caller.
        let skip_var = if let Some(ref trailing) = block.trailing_expr
            && let ExprKind::Identifier(sym) = &trailing.kind
            && let Some((var, _)) = self.vars.get(sym)
        {
            Some(*var)
        } else {
            None
        };

        self.pop_rc_scope_with_cleanup(skip_var)?;
        Ok(result)
    }

    /// Compile an if expression: if cond { then } else { else }
    ///
    /// Optimization: Uses Cranelift's `select` instruction for simple conditionals
    /// where both branches are pure expressions (no side effects, no control flow).
    /// This avoids creating 4 separate blocks and enables better register allocation.
    pub(super) fn if_expr(
        &mut self,
        if_expr: &IfExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Get the result type from semantic analysis (stored on the if expression itself)
        let result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(self.arena().primitives.void);

        // Check for statically known `is` condition (important for monomorphized generics
        // where sema didn't analyze the body and dead branches may contain invalid code).
        if let ExprKind::Is(is) = &if_expr.condition.kind
            && let Some(static_result) = self.try_static_is_check(is, if_expr.condition.id)
        {
            match static_result {
                IsCheckResult::AlwaysTrue => return self.expr(&if_expr.then_branch),
                IsCheckResult::AlwaysFalse => {
                    return if let Some(ref else_branch) = if_expr.else_branch {
                        self.expr(else_branch)
                    } else {
                        Ok(self.void_value())
                    };
                }
                IsCheckResult::CheckTag(_) | IsCheckResult::CheckUnknown(_) => {
                    // Runtime check needed, fall through
                }
            }
        }

        let is_void = self.arena().is_void(result_type_id);

        // Check if we can use select optimization:
        // - Must have an else branch
        // - Both branches must be selectable (pure expressions)
        // - Result must be non-void (select needs a value)
        // Don't use select for RC types — select evaluates both arms eagerly,
        // so the unused RC arm would leak. Block-based if only evaluates the
        // taken branch.
        let can_use_select = !is_void
            && !self.rc_state(result_type_id).needs_cleanup()
            && if_expr.else_branch.is_some()
            && if_expr.then_branch.is_selectable()
            && if_expr
                .else_branch
                .as_ref()
                .is_some_and(|e| e.is_selectable());

        if can_use_select {
            return self.if_expr_select(if_expr, result_type_id);
        }

        // Fall back to standard block-based compilation
        self.if_expr_blocks(if_expr, result_type_id, is_void)
    }

    /// Compile if expression using select instruction (optimized path).
    ///
    /// Generates code like:
    /// ```clif
    /// v0 = <condition>
    /// v1 = <then_value>
    /// v2 = <else_value>
    /// v3 = select v0, v1, v2
    /// ```
    fn if_expr_select(
        &mut self,
        if_expr: &IfExpr,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Compile condition
        let condition = self.expr(&if_expr.condition)?;

        // Compile both branches (they're pure, so order doesn't matter)
        let then_result = self.expr(&if_expr.then_branch)?;
        let else_result = self.expr(
            if_expr
                .else_branch
                .as_ref()
                .expect("INTERNAL: select-style if: missing else branch"),
        )?;

        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Ensure both values have the same type (may need conversion)
        let then_val = self.convert_for_select(then_result.value, result_cranelift_type);
        let else_val = self.convert_for_select(else_result.value, result_cranelift_type);

        // Extend condition to i8 if needed (select expects i8/i16/i32/i64 condition)
        let cond_val = if condition.ty == types::I8 {
            condition.value
        } else {
            self.builder.ins().ireduce(types::I8, condition.value)
        };

        // Constant-fold: if the condition is a known constant, pick the
        // appropriate branch directly without emitting a select instruction.
        let result = if let Some(c) = try_constant_value(self.builder.func, cond_val) {
            if c != 0 { then_val } else { else_val }
        } else {
            self.builder.ins().select(cond_val, then_val, else_val)
        };

        Ok(CompiledValue::new(
            result,
            result_cranelift_type,
            result_type_id,
        ))
    }

    /// Convert a value for use in select (ensure matching types).
    pub(crate) fn convert_for_select(&mut self, value: Value, to_ty: Type) -> Value {
        // Use the actual Cranelift value type rather than the reported type,
        // since CompiledValue.ty can be stale when values flow through deeply
        // nested when/match block parameters.
        let actual_ty = self.builder.func.dfg.value_type(value);
        if actual_ty == to_ty {
            return value;
        }
        // Handle integer width mismatches
        if actual_ty.is_int() && to_ty.is_int() {
            if to_ty.bits() < actual_ty.bits() {
                return self.builder.ins().ireduce(to_ty, value);
            } else if to_ty.bits() > actual_ty.bits() {
                return sextend_const(self.builder, to_ty, value);
            }
        }
        // Handle float promotions/demotions
        if actual_ty == types::F32 && to_ty == types::F64 {
            return self.builder.ins().fpromote(types::F64, value);
        }
        if actual_ty == types::F64 && to_ty == types::F32 {
            return self.builder.ins().fdemote(types::F32, value);
        }
        // Handle int-to-float bitcast (e.g. iterator loop vars stored as i64
        // but semantically f64)
        if actual_ty.is_int() && to_ty.is_float() {
            if actual_ty.bits() == to_ty.bits() {
                return self.builder.ins().bitcast(to_ty, MemFlags::new(), value);
            } else if actual_ty.bits() > to_ty.bits() {
                let narrowed = self.builder.ins().ireduce(
                    Type::int(to_ty.bits() as u16).expect("valid integer type for narrowing"),
                    value,
                );
                return self.builder.ins().bitcast(to_ty, MemFlags::new(), narrowed);
            }
        }
        // For same-size types or unknown conversions, return as-is
        value
    }

    /// Jump to a merge block with a non-void result, ensuring RC ownership for borrowed values.
    pub(crate) fn jump_with_owned_result(
        &mut self,
        val: CompiledValue,
        type_id: TypeId,
        cranelift_type: Type,
        needs_rc: bool,
        merge_block: Block,
    ) -> Result<(), CodegenError> {
        if needs_rc && val.is_borrowed() {
            self.emit_rc_inc_for_type(val.value, type_id)?;
        }
        let converted = self.convert_for_select(val.value, cranelift_type);
        self.builder.ins().jump(merge_block, &[converted.into()]);
        Ok(())
    }

    /// Retrieve the merged result from a multi-arm block (match/if/when).
    ///
    /// For non-void expressions, reads the block parameter from the merge block,
    /// wraps it as a CompiledValue, and marks it as Owned if the type needs RC
    /// cleanup. For void expressions, emits a zero-valued void placeholder.
    pub(crate) fn merge_block_result(
        &mut self,
        merge_block: Block,
        cranelift_type: Type,
        type_id: TypeId,
        is_void: bool,
    ) -> CodegenResult<CompiledValue> {
        if is_void {
            return Ok(self.void_value());
        }
        let result = self.builder.block_params(merge_block)[0];
        let mut cv = CompiledValue::new(result, cranelift_type, type_id);
        if self.rc_state(type_id).needs_cleanup() {
            cv.rc_lifecycle = RcLifecycle::Owned;
        }
        Ok(cv)
    }

    /// Compile if expression using blocks (standard path).
    fn if_expr_blocks(
        &mut self,
        if_expr: &IfExpr,
        result_type_id: TypeId,
        is_void: bool,
    ) -> CodegenResult<CompiledValue> {
        let condition = self.expr(&if_expr.condition)?;

        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Create basic blocks
        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add block parameter for the result
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        // Branch based on condition
        self.emit_brif(condition.value, then_block, else_block);

        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile then branch
        self.switch_and_seal(then_block);
        let then_result = self.expr(&if_expr.then_branch)?;
        if then_result.type_id == TypeId::NEVER {
            // Divergent branch (unreachable/panic) — terminate with trap
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
        } else if !is_void {
            self.jump_with_owned_result(
                then_result,
                result_type_id,
                result_cranelift_type,
                result_needs_rc,
                merge_block,
            )?;
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        // Compile else branch
        self.switch_and_seal(else_block);
        let else_result = if let Some(ref else_branch) = if_expr.else_branch {
            self.expr(else_branch)?
        } else {
            // No else branch - result is void/nil
            self.void_value()
        };
        if else_result.type_id == TypeId::NEVER {
            // Divergent branch (unreachable/panic) — terminate with trap
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
        } else if !is_void {
            self.jump_with_owned_result(
                else_result,
                result_type_id,
                result_cranelift_type,
                result_needs_rc,
                merge_block,
            )?;
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        // Continue in merge block
        self.switch_and_seal(merge_block);

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
    }

    /// Compile a when expression (subject-less conditional chain)
    ///
    /// Control flow for `when { cond1 => body1, cond2 => body2, _ => body3 }`:
    /// ```text
    /// entry:
    ///     eval cond1
    ///     brif -> body1, check2
    /// check2:
    ///     eval cond2
    ///     brif -> body2, body3
    /// body1: jump merge(result1)
    /// body2: jump merge(result2)
    /// body3: jump merge(result3)
    /// merge: return block_param
    /// ```
    ///
    /// Optimization: For binary when expressions (one condition + wildcard),
    /// uses Cranelift's `select` instruction if both bodies are selectable.
    pub(super) fn when_expr(
        &mut self,
        when_expr: &WhenExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Get the result type from semantic analysis (stored on the when expression itself)
        let result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(self.arena().primitives.void);

        let is_void = self.arena().is_void(result_type_id);

        // Check if we can use select optimization for binary when:
        // - Exactly 2 arms
        // - First arm has a condition, second is wildcard
        // - Both bodies are selectable (pure expressions)
        // - Result is non-void
        // - Result is not RC-managed (select evaluates both arms, so an unused
        //   RC arm would leak; block-based when only evaluates the taken branch)
        let can_use_select = !is_void
            && !self.rc_state(result_type_id).needs_cleanup()
            && when_expr.arms.len() == 2
            && when_expr.arms[0].condition.is_some()
            && when_expr.arms[1].condition.is_none()
            && when_expr.arms[0].body.is_selectable()
            && when_expr.arms[1].body.is_selectable();

        if can_use_select {
            return self.when_expr_select(when_expr, result_type_id);
        }

        // Fall back to standard block-based compilation
        self.when_expr_blocks(when_expr, result_type_id, is_void)
    }

    /// Compile binary when expression using select instruction (optimized path).
    ///
    /// For `when { cond => then, _ => else }`, generates:
    /// ```clif
    /// v0 = <cond>
    /// v1 = <then_value>
    /// v2 = <else_value>
    /// v3 = select v0, v1, v2
    /// ```
    fn when_expr_select(
        &mut self,
        when_expr: &WhenExpr,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Compile condition (first arm)
        let condition = self.expr(
            when_expr.arms[0]
                .condition
                .as_ref()
                .expect("INTERNAL: when expr: first arm has no condition"),
        )?;

        // Compile both bodies (they're pure, so order doesn't matter)
        let then_result = self.expr(&when_expr.arms[0].body)?;
        let else_result = self.expr(&when_expr.arms[1].body)?;

        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Ensure both values have the same type (may need conversion)
        let then_val = self.convert_for_select(then_result.value, result_cranelift_type);
        let else_val = self.convert_for_select(else_result.value, result_cranelift_type);

        // Extend condition to i8 if needed
        let cond_val = if condition.ty == types::I8 {
            condition.value
        } else {
            self.builder.ins().ireduce(types::I8, condition.value)
        };

        // Constant-fold: if the condition is a known constant, pick the
        // appropriate branch directly without emitting a select instruction.
        let result = if let Some(c) = try_constant_value(self.builder.func, cond_val) {
            if c != 0 { then_val } else { else_val }
        } else {
            self.builder.ins().select(cond_val, then_val, else_val)
        };

        Ok(CompiledValue::new(
            result,
            result_cranelift_type,
            result_type_id,
        ))
    }

    /// Compile when expression using blocks (standard path).
    fn when_expr_blocks(
        &mut self,
        when_expr: &WhenExpr,
        result_type_id: TypeId,
        is_void: bool,
    ) -> CodegenResult<CompiledValue> {
        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Create merge block
        let merge_block = self.builder.create_block();
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        // Find the wildcard arm index (there must be one - sema ensures this)
        let wildcard_idx = when_expr
            .arms
            .iter()
            .position(|arm| arm.condition.is_none())
            .unwrap_or(when_expr.arms.len() - 1);

        // Create body blocks for each arm
        let body_blocks: Vec<_> = when_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        // Create condition evaluation blocks for arms 1..n-1 (not first, not wildcard)
        // cond_blocks[i] is where we evaluate condition for arm i+1
        let cond_blocks: Vec<_> = (0..when_expr.arms.len().saturating_sub(1))
            .filter(|&i| i + 1 < when_expr.arms.len() && when_expr.arms[i + 1].condition.is_some())
            .map(|_| self.builder.create_block())
            .collect();

        let mut cond_block_idx = 0;

        // Process each conditional arm (skip wildcard - it's reached via brif "else" path)
        for (i, arm) in when_expr.arms.iter().enumerate() {
            if arm.condition.is_none() {
                // Wildcard arm - don't emit jump, brif already routes here
                // The wildcard body will be compiled in the body blocks loop
                break;
            }

            // Evaluate condition in current block
            let cond_result = self.expr(
                arm.condition
                    .as_ref()
                    .expect("INTERNAL: when expr: non-wildcard arm has no condition"),
            )?;

            // Determine "else" target (where to go if condition is false)
            let else_target = if i + 1 < when_expr.arms.len() {
                if when_expr.arms[i + 1].condition.is_none() {
                    // Next is wildcard - go directly to its body
                    body_blocks[i + 1]
                } else {
                    // Next has condition - go to condition evaluation block
                    cond_blocks[cond_block_idx]
                }
            } else {
                // Shouldn't happen (wildcard required), but go to wildcard
                body_blocks[wildcard_idx]
            };

            // Branch to body or next condition
            self.emit_brif(cond_result.value, body_blocks[i], else_target);

            // If next arm has a condition, switch to its evaluation block
            if i + 1 < when_expr.arms.len() && when_expr.arms[i + 1].condition.is_some() {
                self.switch_and_seal(else_target);
                cond_block_idx += 1;
            }
        }

        // Whether the result type needs RC cleanup. When it does, each arm must
        // ensure the value flowing into the merge block is "owned" (has a +1 ref
        // that the consumer will balance). Borrowed arm results (variable reads)
        // get an rc_inc; Owned arm results (fresh allocations) already have +1.
        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile body blocks
        for (i, arm) in when_expr.arms.iter().enumerate() {
            self.switch_and_seal(body_blocks[i]);

            let body_result = self.expr(&arm.body)?;

            // Divergent arms (unreachable, panic) already emitted a trap.
            // The current block is an unreachable continuation — terminate
            // it with a trap instead of a jump with a mistyped dummy value.
            if body_result.type_id == TypeId::NEVER {
                self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
                continue;
            }

            if !is_void {
                // For RC types, ensure each arm contributes an owned +1 ref.
                self.jump_with_owned_result(
                    body_result,
                    result_type_id,
                    result_cranelift_type,
                    result_needs_rc,
                    merge_block,
                )?;
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
        }

        // Continue in merge block
        self.switch_and_seal(merge_block);

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
    }
}
