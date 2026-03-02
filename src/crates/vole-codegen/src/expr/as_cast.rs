// src/codegen/expr/as_cast.rs
//
// Codegen for `as?` (safe cast) and `as!` (unsafe cast) expressions.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use crate::errors::CodegenResult;
use crate::types::CompiledValue;

use vole_identity::{TypeId, VirTypeId};

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Core safe-branch: if match -> extract and wrap nullable, else -> nil.
    #[allow(dead_code)]
    pub(super) fn as_cast_safe_branch_with_type(
        &mut self,
        is_match: Value,
        nullable_type_id: TypeId,
        extract: impl FnOnce(&mut Self) -> CodegenResult<CompiledValue>,
    ) -> CodegenResult<CompiledValue> {
        self.as_cast_safe_branch_v(
            is_match,
            self.vir_lookup_or_compat(nullable_type_id),
            extract,
        )
    }

    /// VirTypeId-native safe-branch: if match -> extract and wrap nullable, else -> nil.
    pub(super) fn as_cast_safe_branch_v(
        &mut self,
        is_match: Value,
        nullable_vir: VirTypeId,
        extract: impl FnOnce(&mut Self) -> CodegenResult<CompiledValue>,
    ) -> CodegenResult<CompiledValue> {
        let result_cranelift_type = self.cranelift_type_v(nullable_vir);
        let result_needs_rc = self.rc_state_v(nullable_vir).needs_cleanup();

        let match_block = self.builder.create_block();
        let no_match_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, result_cranelift_type);

        self.emit_brif(is_match, match_block, no_match_block);

        // Match block: extract value, wrap as nullable
        self.switch_and_seal(match_block);
        let extracted = extract(self)?;
        let wrapped = self.coerce_to_type(extracted, nullable_vir)?;
        if result_needs_rc && wrapped.is_borrowed() {
            self.emit_rc_inc_for_type_v(wrapped.value, nullable_vir)?;
        }
        let wrapped_arg = BlockArg::from(wrapped.value);
        self.builder.ins().jump(merge_block, &[wrapped_arg]);

        // No-match block: produce nil
        self.switch_and_seal(no_match_block);
        let nil_val = self.compile_nil_for_optional_v(nullable_vir)?;
        let nil_arg = BlockArg::from(nil_val.value);
        self.builder.ins().jump(merge_block, &[nil_arg]);

        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result, result_cranelift_type, nullable_vir);
        Ok(self.mark_rc_owned(cv))
    }

    /// Core unsafe-branch: if match -> extract, else -> panic.
    #[allow(dead_code)]
    pub(super) fn as_cast_unsafe_branch_with_type(
        &mut self,
        is_match: Value,
        tested_type_id: TypeId,
        line: u32,
        extract: impl FnOnce(&mut Self) -> CodegenResult<CompiledValue>,
    ) -> CodegenResult<CompiledValue> {
        self.as_cast_unsafe_branch_v(
            is_match,
            self.vir_lookup_or_compat(tested_type_id),
            line,
            extract,
        )
    }

    /// VirTypeId-native unsafe-branch: if match -> extract, else -> panic.
    pub(super) fn as_cast_unsafe_branch_v(
        &mut self,
        is_match: Value,
        tested_vir: VirTypeId,
        line: u32,
        extract: impl FnOnce(&mut Self) -> CodegenResult<CompiledValue>,
    ) -> CodegenResult<CompiledValue> {
        let result_cranelift_type = self.cranelift_type_v(tested_vir);

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
            tested_vir,
        ))
    }

    /// Extract a union payload with a known target type (VirTypeId-native).
    pub(super) fn extract_union_payload_typed_v(
        &mut self,
        union_value: CompiledValue,
        target_vir: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let payload_ty = self.cranelift_type_v(target_vir);
        let payload = self.load_union_payload_v(union_value.value, union_value.type_id, payload_ty);
        Ok(CompiledValue::new(payload, payload_ty, target_vir))
    }
}
