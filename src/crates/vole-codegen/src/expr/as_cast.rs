// src/codegen/expr/as_cast.rs
//
// Codegen for `as?` (safe cast) and `as!` (unsafe cast) expressions.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, type_id_to_cranelift};
use crate::union_layout;

use vole_frontend::NodeId;
use vole_frontend::ast::{AsCastExpr, AsCastKind};
use vole_sema::IsCheckResult;
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile an `as?` or `as!` cast expression.
    ///
    /// For `as?`: returns `T | nil` — if check passes, extract narrowed value and
    /// wrap in nullable; otherwise nil.
    ///
    /// For `as!`: returns `T` — if check passes, extract narrowed value; otherwise
    /// emits a panic.
    pub(super) fn as_cast_expr(
        &mut self,
        as_cast: &AsCastExpr,
        expr_id: NodeId,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let value = self.expr(&as_cast.value)?;

        // Look up or compute IsCheckResult (same logic as is_expr)
        let is_check_result = self.resolve_as_cast_check(as_cast, expr_id, &value)?;

        match is_check_result {
            IsCheckResult::AlwaysTrue => {
                // Value is already the target type — extract or return as-is
                self.as_cast_extract_value(as_cast.kind, value, as_cast, expr_id)
            }
            IsCheckResult::AlwaysFalse => {
                self.as_cast_always_false(as_cast.kind, as_cast, expr_id, line)
            }
            IsCheckResult::CheckTag(tag_index) => {
                self.as_cast_check_tag(as_cast, expr_id, value, tag_index, line)
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                self.as_cast_check_unknown(as_cast, expr_id, value, tested_type_id, line)
            }
        }
    }

    /// Resolve the IsCheckResult for an as-cast expression.
    fn resolve_as_cast_check(
        &self,
        as_cast: &AsCastExpr,
        expr_id: NodeId,
        value: &CompiledValue,
    ) -> CodegenResult<IsCheckResult> {
        // When substitutions are active, prefer recomputation (same as is_expr)
        if self.substitutions.is_some() {
            if let Some(tested_type_id) = self.resolve_simple_type_expr(&as_cast.type_expr) {
                return Ok(self.compute_is_check_result(value.type_id, tested_type_id));
            }
            if let Some(result) = self.get_is_check_result(expr_id) {
                return Ok(result);
            }
            return Err(CodegenError::internal(
                "as cast in monomorphized generic: cannot resolve tested type",
            ));
        }

        match self.get_is_check_result(expr_id) {
            Some(result) => Ok(result),
            None => {
                let tested_type_id = self
                    .resolve_simple_type_expr(&as_cast.type_expr)
                    .ok_or_else(|| CodegenError::internal("as cast: cannot resolve tested type"))?;
                Ok(self.compute_is_check_result(value.type_id, tested_type_id))
            }
        }
    }

    /// Get the nullable result type for a safe cast (`as?`).
    /// Sema records this as the expression type; fall back to an error if missing.
    fn safe_cast_nullable_type(&self, expr_id: &NodeId) -> CodegenResult<TypeId> {
        self.get_expr_type_substituted(expr_id).ok_or_else(|| {
            CodegenError::internal("as? cast: missing nullable result type from sema")
        })
    }

    /// Extract the narrowed value when the cast always succeeds.
    fn as_cast_extract_value(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        as_cast: &AsCastExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // The value is already the correct type; for as? we wrap in nullable
        let _tested_type_id = self.resolve_tested_type(as_cast, expr_id)?;
        match kind {
            AsCastKind::Safe => {
                // Wrap in T | nil
                let nullable_type_id = self.safe_cast_nullable_type(&expr_id)?;
                self.coerce_to_type(value, nullable_type_id)
            }
            AsCastKind::Unsafe => {
                // Value is already T
                Ok(value)
            }
        }
    }

    /// Handle the always-false case (cast can never succeed).
    fn as_cast_always_false(
        &mut self,
        kind: AsCastKind,
        as_cast: &AsCastExpr,
        expr_id: NodeId,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let _tested_type_id = self.resolve_tested_type(as_cast, expr_id)?;
        match kind {
            AsCastKind::Safe => {
                // Always returns nil
                let nullable_type_id = self.safe_cast_nullable_type(&expr_id)?;
                self.compile_nil_for_optional(nullable_type_id)
            }
            AsCastKind::Unsafe => {
                // Always panics
                self.emit_panic_static("as! cast failed: value is not the expected type", line)?;
                Ok(CompiledValue::new(
                    self.iconst_cached(types::I64, 0),
                    types::I64,
                    TypeId::NEVER,
                ))
            }
        }
    }

    /// Handle union tag check: branch on tag, extract payload or nil/panic.
    fn as_cast_check_tag(
        &mut self,
        as_cast: &AsCastExpr,
        expr_id: NodeId,
        value: CompiledValue,
        tag_index: u32,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let tested_type_id = self.resolve_tested_type(as_cast, expr_id)?;
        let is_match = self.tag_eq(value.value, tag_index as i64);

        match as_cast.kind {
            AsCastKind::Safe => {
                self.as_cast_safe_branch(value, is_match, tested_type_id, expr_id, |cg| {
                    cg.extract_union_payload_typed(value, tested_type_id)
                })
            }
            AsCastKind::Unsafe => {
                self.as_cast_unsafe_branch(value, is_match, tested_type_id, line, |cg| {
                    cg.extract_union_payload_typed(value, tested_type_id)
                })
            }
        }
    }

    /// Handle unknown type check: branch on runtime tag, extract or nil/panic.
    fn as_cast_check_unknown(
        &mut self,
        as_cast: &AsCastExpr,
        expr_id: NodeId,
        value: CompiledValue,
        tested_type_id: TypeId,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        // Check if the unknown value's tag matches
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 0);
        let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
        let expected_val = self.iconst_cached(types::I64, expected_tag as i64);
        let is_match = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);

        match as_cast.kind {
            AsCastKind::Safe => {
                self.as_cast_safe_branch(value, is_match, tested_type_id, expr_id, |cg| {
                    // Extract value from TaggedValue at offset 8
                    let raw_value = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    Ok(cg.extract_unknown_value(raw_value, tested_type_id))
                })
            }
            AsCastKind::Unsafe => {
                self.as_cast_unsafe_branch(value, is_match, tested_type_id, line, |cg| {
                    let raw_value = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    Ok(cg.extract_unknown_value(raw_value, tested_type_id))
                })
            }
        }
    }

    /// Emit safe cast branching: if match -> extract and wrap nullable, else -> nil.
    fn as_cast_safe_branch(
        &mut self,
        _value: CompiledValue,
        is_match: Value,
        _tested_type_id: TypeId,
        expr_id: NodeId,
        extract: impl FnOnce(&mut Self) -> CodegenResult<CompiledValue>,
    ) -> CodegenResult<CompiledValue> {
        let nullable_type_id = self.safe_cast_nullable_type(&expr_id)?;
        let result_cranelift_type = self.cranelift_type(nullable_type_id);
        let result_needs_rc = self.rc_state(nullable_type_id).needs_cleanup();

        let match_block = self.builder.create_block();
        let no_match_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, result_cranelift_type);

        self.emit_brif(is_match, match_block, no_match_block);

        // Match block: extract value, wrap as nullable
        self.switch_and_seal(match_block);
        let extracted = extract(self)?;
        let wrapped = self.coerce_to_type(extracted, nullable_type_id)?;
        if result_needs_rc && wrapped.is_borrowed() {
            self.emit_rc_inc_for_type(wrapped.value, nullable_type_id)?;
        }
        let wrapped_arg = BlockArg::from(wrapped.value);
        self.builder.ins().jump(merge_block, &[wrapped_arg]);

        // No-match block: produce nil
        self.switch_and_seal(no_match_block);
        let nil_val = self.compile_nil_for_optional(nullable_type_id)?;
        let nil_arg = BlockArg::from(nil_val.value);
        self.builder.ins().jump(merge_block, &[nil_arg]);

        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result, result_cranelift_type, nullable_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    /// Emit unsafe cast branching: if match -> extract, else -> panic.
    fn as_cast_unsafe_branch(
        &mut self,
        _value: CompiledValue,
        is_match: Value,
        tested_type_id: TypeId,
        line: u32,
        extract: impl FnOnce(&mut Self) -> CodegenResult<CompiledValue>,
    ) -> CodegenResult<CompiledValue> {
        let result_cranelift_type =
            type_id_to_cranelift(tested_type_id, self.arena(), self.ptr_type());

        let match_block = self.builder.create_block();
        let panic_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, result_cranelift_type);

        self.emit_brif(is_match, match_block, panic_block);

        // Panic block: emit panic and trap
        self.switch_and_seal(panic_block);
        self.emit_panic_static("as! cast failed: value is not the expected type", line)?;
        self.builder.ins().trap(crate::trap_codes::UNREACHABLE);

        // Match block: extract value
        self.switch_and_seal(match_block);
        let extracted = extract(self)?;
        let coerced_value =
            self.coerce_cranelift_value(extracted.value, extracted.ty, result_cranelift_type);
        let value_arg = BlockArg::from(coerced_value);
        self.builder.ins().jump(merge_block, &[value_arg]);

        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue::new(
            result,
            result_cranelift_type,
            tested_type_id,
        ))
    }

    /// Extract a union payload with a known target type.
    fn extract_union_payload_typed(
        &mut self,
        union_value: CompiledValue,
        target_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let payload_ty = type_id_to_cranelift(target_type_id, self.arena(), self.ptr_type());
        let payload = self.load_union_payload(union_value.value, union_value.type_id, payload_ty);
        Ok(CompiledValue::new(payload, payload_ty, target_type_id))
    }

    /// Resolve the tested type for an as-cast expression.
    fn resolve_tested_type(&self, as_cast: &AsCastExpr, _expr_id: NodeId) -> CodegenResult<TypeId> {
        if let Some(tested_type_id) = self.resolve_simple_type_expr(&as_cast.type_expr) {
            Ok(tested_type_id)
        } else {
            Err(CodegenError::internal(
                "as cast: cannot resolve target type",
            ))
        }
    }
}
