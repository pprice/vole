// src/codegen/expr/null_ops.rs
//
// Null coalesce, try propagation, and closure capture operations.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{
    CompiledValue, FALLIBLE_SUCCESS_TAG, load_fallible_payload, load_fallible_tag,
    type_id_to_cranelift,
};
use crate::union_layout;

use vole_frontend::Expr;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile a null coalesce expression (??)
    pub(super) fn null_coalesce(
        &mut self,
        nc: &vole_frontend::ast::NullCoalesceExpr,
    ) -> CodegenResult<CompiledValue> {
        let value = self.expr(&nc.value)?;
        let nil_tag = self.find_nil_variant(value.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("null coalesce operator", "optional type", "non-optional")
        })?;

        let is_nil = self.tag_eq(value.value, nil_tag as i64);

        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let inner_type_id = self
            .arena()
            .unwrap_optional(value.type_id)
            .expect("INTERNAL: unwrap expr: expected optional type");
        let cranelift_type = type_id_to_cranelift(inner_type_id, self.arena(), self.ptr_type());
        self.builder.append_block_param(merge_block, cranelift_type);

        let result_needs_rc =
            self.rc_scopes.has_active_scope() && self.rc_state(inner_type_id).needs_cleanup();

        self.emit_brif(is_nil, nil_block, not_nil_block);

        self.switch_and_seal(nil_block);
        let default_val = self.expr(&nc.default)?;
        // RC: inc borrowed default values so the result gets its own reference.
        if result_needs_rc && default_val.is_borrowed() {
            self.emit_rc_inc_for_type(default_val.value, inner_type_id)?;
        }
        let default_coerced = if default_val.ty != cranelift_type {
            if default_val.ty.is_int() && cranelift_type.is_int() {
                if cranelift_type.bytes() < default_val.ty.bytes() {
                    self.builder
                        .ins()
                        .ireduce(cranelift_type, default_val.value)
                } else {
                    self.builder
                        .ins()
                        .sextend(cranelift_type, default_val.value)
                }
            } else {
                default_val.value
            }
        } else {
            default_val.value
        };
        let default_arg = BlockArg::from(default_coerced);
        self.builder.ins().jump(merge_block, &[default_arg]);

        self.switch_and_seal(not_nil_block);
        // Only load payload if union has payload data.
        // Sentinel-only unions have union_size == 8 (tag only), no payload to read.
        let union_size = self.type_size(value.type_id);
        let payload = if union_size > union_layout::TAG_ONLY_SIZE {
            let loaded = self.builder.ins().load(
                cranelift_type,
                MemFlags::new(),
                value.value,
                union_layout::PAYLOAD_OFFSET,
            );
            // RC: if the source optional is borrowed (identifier, array/index read,
            // field access, etc.), the owner will eventually dec the payload, so
            // the coalesce result needs its own ref.
            if result_needs_rc && value.is_borrowed() {
                self.emit_rc_inc_for_type(loaded, inner_type_id)?;
            }
            loaded
        } else {
            self.builder.ins().iconst(cranelift_type, 0)
        };
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.switch_and_seal(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result, cranelift_type, inner_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    /// Compile a try expression (propagation)
    ///
    /// On success: returns unwrapped value
    /// On error: propagates by returning from function with (tag: i64, payload: i64)
    pub(super) fn try_propagate(&mut self, inner: &Expr) -> CodegenResult<CompiledValue> {
        // Compile the inner fallible expression
        let fallible = self.expr(inner)?;

        let success_type_id = {
            let arena = self.arena();
            match arena.unwrap_fallible(fallible.type_id) {
                Some((success_id, _error_id)) => success_id,
                None => {
                    return Err(CodegenError::type_mismatch(
                        "try operator",
                        "fallible type",
                        "non-fallible",
                    ));
                }
            }
        };

        // Load the tag from the fallible (stored at offset 0 in stack slot)
        let tag = load_fallible_tag(self.builder, fallible.value);

        // Check if success (tag == 0)
        let is_success = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

        // Create blocks
        let success_block = self.builder.create_block();
        let error_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Get payload type for success using TypeId
        let payload_ty = self.cranelift_type(success_type_id);
        self.builder.append_block_param(merge_block, payload_ty);

        // Branch based on tag
        self.emit_brif(is_success, success_block, error_block);

        // Error block: propagate by returning (tag, payload) for multi-value return
        // Payload is stored as i64 in the stack slot
        self.switch_and_seal(error_block);
        let error_payload_i64 = load_fallible_payload(self.builder, fallible.value, types::I64);
        self.builder.ins().return_(&[tag, error_payload_i64]);

        // Success block: extract payload and jump to merge
        // The payload is stored as i64 in the stack slot, convert to actual type
        self.switch_and_seal(success_block);
        let payload_i64 = load_fallible_payload(self.builder, fallible.value, types::I64);
        // Convert i64 back to the actual success type
        let payload = self.convert_from_i64_storage(payload_i64, success_type_id);
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        // Merge block: continue with extracted value
        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        Ok(CompiledValue::new(result, payload_ty, success_type_id))
    }

    /// Load a captured variable from closure
    pub(crate) fn load_capture(
        &mut self,
        binding: &super::super::lambda::CaptureBinding,
    ) -> CodegenResult<CompiledValue> {
        let closure_var = self.closure_var().ok_or_else(|| {
            CodegenError::internal("closure variable not available for capture access")
        })?;
        let closure_ptr = self.builder.use_var(closure_var);

        let index_val = self.builder.ins().iconst(types::I64, binding.index as i64);
        let heap_ptr =
            self.call_runtime(RuntimeKey::ClosureGetCapture, &[closure_ptr, index_val])?;

        // Structs are captured by value — the heap slot contains the full struct
        // data (not a pointer to a pointer). Return heap_ptr directly as the
        // struct pointer.
        if self.arena().is_struct(binding.vole_type) {
            let ptr_type = self.ptr_type();
            let cv = CompiledValue::new(heap_ptr, ptr_type, binding.vole_type);
            return Ok(cv);
        }

        let cranelift_ty = self.cranelift_type(binding.vole_type);
        let value = self
            .builder
            .ins()
            .load(cranelift_ty, MemFlags::new(), heap_ptr, 0);

        // Capture loads are borrows — the closure owns the reference via its
        // capture slot.  Marking as Borrowed ensures the return path inc's the
        // value when it leaves the closure body, giving the caller a +1 ref.
        let mut cv = CompiledValue::new(value, cranelift_ty, binding.vole_type);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Store a value to a captured variable in closure
    pub(super) fn store_capture(
        &mut self,
        binding: &super::super::lambda::CaptureBinding,
        mut value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let closure_var = self.closure_var().ok_or_else(|| {
            CodegenError::internal("closure variable not available for capture access")
        })?;
        let closure_ptr = self.builder.use_var(closure_var);

        let index_val = self.builder.ins().iconst(types::I64, binding.index as i64);
        let heap_ptr =
            self.call_runtime(RuntimeKey::ClosureGetCapture, &[closure_ptr, index_val])?;

        // Structs: copy all flat slots from value (stack ptr) to heap slot
        if let Some(flat_count) = self.struct_flat_slot_count(binding.vole_type) {
            for slot in 0..flat_count {
                let offset = (slot as i32) * 8;
                let val = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), value.value, offset);
                self.builder
                    .ins()
                    .store(MemFlags::new(), val, heap_ptr, offset);
            }
            value.mark_consumed();
            value.debug_assert_rc_handled("closure capture assign");
            let ptr_type = self.ptr_type();
            return Ok(CompiledValue::new(heap_ptr, ptr_type, binding.vole_type));
        }

        let cranelift_ty = self.cranelift_type(binding.vole_type);
        self.builder
            .ins()
            .store(MemFlags::new(), value.value, heap_ptr, 0);

        // The value is consumed into the captured variable storage.
        value.mark_consumed();
        value.debug_assert_rc_handled("closure capture assign");
        Ok(CompiledValue::new(
            value.value,
            cranelift_ty,
            binding.vole_type,
        ))
    }
}
