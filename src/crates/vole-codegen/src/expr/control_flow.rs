// src/codegen/expr/control_flow.rs
//
// Control flow helpers and VIR if/block expressions.

use cranelift::prelude::*;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, RcLifecycle};

use vole_identity::TypeId;

use crate::ops::sextend_const;

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
            self.vir_lookup(TypeId::NEVER),
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
        let mut cv = CompiledValue::new(result, cranelift_type, self.vir_lookup(type_id));
        if self.rc_state(type_id).needs_cleanup() {
            cv.rc_lifecycle = RcLifecycle::Owned;
        }
        Ok(cv)
    }

    // =========================================================================
    // VIR If expression
    // =========================================================================

    /// Compile a VIR `If` expression using block-based control flow.
    ///
    /// Similar to [`if_expr_blocks`] but operates on `VirBody` branches
    /// instead of AST expression nodes.  Used by desugared And/Or operators
    /// and will be used by future VIR-lowered `if` expressions.
    pub(super) fn compile_vir_if(
        &mut self,
        cond: &vole_vir::VirExpr,
        then_body: &vole_vir::VirBody,
        else_body: Option<&vole_vir::VirBody>,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let condition = self.compile_vir_expr(cond)?;
        let is_void = self.vir_query_is_void(result_type_id);
        let result_cranelift_type = self.cranelift_type(result_type_id);

        // Create basic blocks
        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        self.emit_brif(condition.value, then_block, else_block);

        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile then branch
        //
        // `compile_vir_body` returns `(flag, Option<value>)`:
        //   - Expression bodies (trailing != None): always `(true, Some(value))`
        //   - Block bodies (trailing == None): `(terminated, None)`
        //
        // A branch is "terminated" (has a control-flow exit like break/return)
        // when the body returns `(true, None)` — the block body compiled stmts
        // that ended with a terminator, and there's no trailing expression.
        self.switch_and_seal(then_block);
        let (then_flag, then_val) = self.compile_vir_body(then_body)?;
        let then_terminated = then_flag && then_val.is_none();
        if !then_terminated {
            let then_result = then_val.unwrap_or_else(|| self.void_value());
            if self.cv_type_id(&then_result) == TypeId::NEVER {
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
        }

        // Compile else branch
        self.switch_and_seal(else_block);
        let else_terminated = if let Some(else_body) = else_body {
            let (flag, val) = self.compile_vir_body(else_body)?;
            let terminated = flag && val.is_none();
            if !terminated {
                let else_result = val.unwrap_or_else(|| self.void_value());
                if self.cv_type_id(&else_result) == TypeId::NEVER {
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
            }
            terminated
        } else {
            self.builder.ins().jump(merge_block, &[]);
            false
        };

        // Continue in merge block
        self.switch_and_seal(merge_block);

        // If both branches terminated, the merge block is unreachable.
        // Cranelift still requires it to be filled, so emit a trap.
        // Return a NEVER-typed value so callers know this code path
        // is dead (e.g., VirStmt::Expr propagates termination).
        if then_terminated && else_terminated {
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
            let dummy = self.cached_void_val;
            return Ok(CompiledValue::new(
                dummy,
                types::I64,
                self.vir_lookup(TypeId::NEVER),
            ));
        }

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
    }

    // =========================================================================
    // VIR Block expression
    // =========================================================================

    /// Compile a VIR `Block` expression.
    ///
    /// Pushes an RC scope, compiles statements sequentially, then compiles
    /// the trailing expression (if any).  Mirrors [`block_expr`] but operates
    /// on VIR nodes instead of AST nodes.
    pub(super) fn compile_vir_block(
        &mut self,
        stmts: &[vole_vir::VirStmt],
        trailing: Option<&vole_vir::VirExpr>,
    ) -> CodegenResult<CompiledValue> {
        self.push_rc_scope();

        for vir_stmt in stmts {
            self.compile_vir_stmt(vir_stmt)?;
        }

        let result = if let Some(trailing_expr) = trailing {
            self.compile_vir_expr(trailing_expr)?
        } else {
            self.void_value()
        };

        self.pop_rc_scope_with_cleanup(None)?;
        Ok(result)
    }
}
