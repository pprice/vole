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

use vole_frontend::{Expr, ExprKind, NodeId};
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile a null coalesce expression (??)
    pub(super) fn null_coalesce(
        &mut self,
        nc: &vole_frontend::ast::NullCoalesceExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let value = self.expr(&nc.value)?;
        let nil_tag = self.find_nil_variant(value.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("null coalesce operator", "optional type", "non-optional")
        })?;

        // The inner type (non-nil result) is stored in the sema node_map as the result
        // type of the ?? expression. For T | nil it's T; for A | B | nil it's A | B.
        let inner_type_id = self.get_expr_type(&expr_id).unwrap_or_else(|| {
            // Fallback for simple T | nil where sema result type equals unwrapped inner type.
            self.arena()
                .unwrap_optional(value.type_id)
                .unwrap_or(TypeId::INVALID)
        });

        let is_multi_variant_inner = self.arena().is_union(inner_type_id);
        if is_multi_variant_inner {
            // Multi-variant optional (A | B | nil): result type A | B is itself a union.
            // The non-nil variants have compatible tag values in the source union (they are
            // sorted the same way), so we can return the source pointer retyped as A | B.
            self.null_coalesce_union_result(nc, value, inner_type_id, nil_tag)
        } else {
            // Simple optional (T | nil): result is scalar T.
            self.null_coalesce_scalar_result(nc, value, inner_type_id, nil_tag)
        }
    }

    /// Compile ?? where the result type is a scalar (non-union) type.
    /// This is the case for `T | nil ?? default` → `T`.
    fn null_coalesce_scalar_result(
        &mut self,
        nc: &vole_frontend::ast::NullCoalesceExpr,
        value: CompiledValue,
        inner_type_id: TypeId,
        nil_tag: usize,
    ) -> CodegenResult<CompiledValue> {
        let cranelift_type = type_id_to_cranelift(inner_type_id, self.arena(), self.ptr_type());

        let is_nil = self.tag_eq(value.value, nil_tag as i64);
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
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
            self.iconst_cached(cranelift_type, 0)
        };
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result, cranelift_type, inner_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    /// Compile ?? where the result type is itself a union (A | B from A | B | nil).
    /// The non-nil variants have compatible tag values between the source union and
    /// the result union (same sort order, same indices), so we can return the source
    /// pointer retyped as the result union type.
    fn null_coalesce_union_result(
        &mut self,
        nc: &vole_frontend::ast::NullCoalesceExpr,
        value: CompiledValue,
        inner_type_id: TypeId,
        nil_tag: usize,
    ) -> CodegenResult<CompiledValue> {
        let ptr_type = self.ptr_type();

        let is_nil = self.tag_eq(value.value, nil_tag as i64);
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        // Both branches pass a pointer (the union pointer or default pointer)
        self.builder.append_block_param(merge_block, ptr_type);

        self.emit_brif(is_nil, nil_block, not_nil_block);

        // Nil branch: evaluate and use the default value (must be A | B type)
        self.switch_and_seal(nil_block);
        let default_val = self.expr(&nc.default)?;
        let default_ptr = if self.arena().is_union(default_val.type_id) {
            // Default is already a union pointer
            default_val.value
        } else {
            // Default is a scalar or non-union; box it into a union slot
            let boxed = self.construct_union_id(default_val, inner_type_id)?;
            boxed.value
        };
        let default_arg = BlockArg::from(default_ptr);
        self.builder.ins().jump(merge_block, &[default_arg]);

        // Not-nil branch: reuse the source pointer (tag/payload are compatible for A | B)
        self.switch_and_seal(not_nil_block);
        let value_ptr_arg = BlockArg::from(value.value);
        self.builder.ins().jump(merge_block, &[value_ptr_arg]);

        self.switch_and_seal(merge_block);
        let result_ptr = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result_ptr, ptr_type, inner_type_id);
        Ok(cv)
    }

    /// Compile an optional chain expression (`?.`).
    ///
    /// For `obj?.field`: compiles scrutinee, branches on nil tag, on not-nil
    /// extracts inner value and does field access, wraps result as optional.
    ///
    /// For `obj?.method(args)`: same pattern, but calls the method on the
    /// inner value. Method resolution is stored at `expr_id` by sema.
    pub(super) fn optional_chain(
        &mut self,
        expr: &Expr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let info = self
            .get_optional_chain(expr_id)
            .cloned()
            .expect("INTERNAL: optional chain must have OptionalChainInfo from sema");

        // Compile the scrutinee (the object before `?.`)
        let scrutinee_expr = match &expr.kind {
            ExprKind::OptionalChain(oc) => &oc.object,
            ExprKind::OptionalMethodCall(omc) => &omc.object,
            _ => unreachable!("optional_chain called on non-optional-chain expr"),
        };
        let scrutinee = self.expr(scrutinee_expr)?;

        // Find nil variant tag in the union
        let nil_tag = self.find_nil_variant(scrutinee.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional chain operator", "optional type", "non-optional")
        })?;

        // Get the overall result type from sema (e.g. string | nil)
        let result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(TypeId::VOID);
        let result_cranelift_type = self.cranelift_type(result_type_id);
        let result_needs_rc = self.rc_state(result_type_id).needs_cleanup();

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, result_cranelift_type);

        // Branch on nil tag
        let is_nil = self.tag_eq(scrutinee.value, nil_tag as i64);
        self.emit_brif(is_nil, nil_block, not_nil_block);

        // --- Nil branch: produce nil wrapped as the result type ---
        self.switch_and_seal(nil_block);
        let nil_val = self.compile_nil_for_optional(result_type_id)?;
        self.jump_with_owned_result(
            nil_val,
            result_type_id,
            result_cranelift_type,
            result_needs_rc,
            merge_block,
        )?;

        // --- Not-nil branch: extract inner, do field/method access ---
        self.switch_and_seal(not_nil_block);

        // Extract inner value from union payload
        let inner_type_id = self.try_substitute_type(info.inner_type);
        let inner_cranelift_type = self.cranelift_type(inner_type_id);
        let union_size = self.type_size(scrutinee.type_id);
        let inner_val = if union_size > union_layout::TAG_ONLY_SIZE {
            let loaded = self.builder.ins().load(
                inner_cranelift_type,
                MemFlags::new(),
                scrutinee.value,
                union_layout::PAYLOAD_OFFSET,
            );
            CompiledValue::new(loaded, inner_cranelift_type, inner_type_id)
        } else {
            // Sentinel-only union (tag only, no payload)
            let zero = self.iconst_cached(inner_cranelift_type, 0);
            CompiledValue::new(zero, inner_cranelift_type, inner_type_id)
        };

        // Compute the body value depending on chain kind
        let body_val = match &info.kind {
            vole_sema::OptionalChainKind::FieldAccess { field } => {
                self.optional_chain_field_access(inner_val, *field)?
            }
            vole_sema::OptionalChainKind::MethodCall => {
                self.optional_chain_method_call(expr, inner_val, expr_id)?
            }
        };

        // Coerce body to the result type (wraps scalar in optional union if needed)
        let body_coerced = self.coerce_to_type(body_val, result_type_id)?;
        self.jump_with_owned_result(
            body_coerced,
            result_type_id,
            result_cranelift_type,
            result_needs_rc,
            merge_block,
        )?;

        // --- Merge ---
        self.switch_and_seal(merge_block);
        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, false)
    }

    /// Compile field access on the unwrapped inner value of an optional chain.
    fn optional_chain_field_access(
        &mut self,
        inner: CompiledValue,
        field: vole_frontend::Symbol,
    ) -> CodegenResult<CompiledValue> {
        let field_name = self.interner().resolve(field);
        let (slot, field_type_id) = super::super::structs::helpers::get_field_slot_and_type_id_cg(
            inner.type_id,
            field_name,
            self,
        )?;
        self.extract_field(inner, slot, field_type_id)
    }

    /// Compile a method call on the unwrapped inner value of an optional chain.
    ///
    /// Temporarily inserts the inner value into vars so `method_call` can compile
    /// the synthetic receiver expression normally.
    fn optional_chain_method_call(
        &mut self,
        expr: &Expr,
        inner: CompiledValue,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let omc = match &expr.kind {
            ExprKind::OptionalMethodCall(omc) => omc,
            _ => unreachable!("optional_chain_method_call called on non-OptionalMethodCall"),
        };

        // Create a Cranelift variable for the inner value
        let inner_var = self.builder.declare_var(inner.ty);
        self.builder.def_var(inner_var, inner.value);

        // Insert into vars under the $oc symbol
        let oc_sym = self.interner().lookup("$oc").expect("$oc must be interned");
        let saved_entry = self.vars.insert(oc_sym, (inner_var, inner.type_id));

        // Build a MethodCallExpr with $oc as receiver
        let mc = vole_frontend::MethodCallExpr {
            object: Expr {
                id: expr_id,
                kind: ExprKind::Identifier(oc_sym),
                span: omc.method_span,
            },
            method: omc.method,
            type_args: omc.type_args.clone(),
            args: omc.args.clone(),
            method_span: omc.method_span,
        };

        let result = self.method_call(&mc, expr_id);

        // Restore vars
        if let Some(old) = saved_entry {
            self.vars.insert(oc_sym, old);
        } else {
            self.vars.remove(&oc_sym);
        }

        result
    }

    /// Produce a nil value wrapped in the given optional result type.
    pub(super) fn compile_nil_for_optional(
        &mut self,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let nil_type_id = self.arena().nil();
        let nil_val = CompiledValue::new(self.iconst_cached(types::I8, 0), types::I8, nil_type_id);
        self.coerce_to_type(nil_val, result_type_id)
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

        let index_val = self.iconst_cached(types::I64, binding.index as i64);
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

        let index_val = self.iconst_cached(types::I64, binding.index as i64);
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
