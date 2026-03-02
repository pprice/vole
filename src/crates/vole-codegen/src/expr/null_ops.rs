// src/codegen/expr/null_ops.rs
//
// Null coalesce, try propagation, and closure capture operations.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, FALLIBLE_SUCCESS_TAG, load_fallible_payload, load_fallible_tag};
use crate::union_layout;

use vole_identity::{NodeId, TypeId, VirTypeId};
use vole_vir::VirExpr;
use vole_vir::expr::VirMethodDispatchMeta;

use super::super::context::Cg;

pub(super) struct VirOptionalMethodCallArgs<'a> {
    pub object_expr: &'a VirExpr,
    pub method: vole_frontend::Symbol,
    pub method_args: &'a [vole_vir::VirRef],
    pub dispatch: &'a VirMethodDispatchMeta,
    pub call_node_id: NodeId,
    pub inner_type_id: VirTypeId,
    pub result_type_id: VirTypeId,
}

impl Cg<'_, '_, '_> {
    /// Compile field access on the unwrapped inner value of an optional chain.
    fn optional_chain_field_access(
        &mut self,
        inner: CompiledValue,
        field: vole_frontend::Symbol,
    ) -> CodegenResult<CompiledValue> {
        let field_name = self.interner().resolve(field);
        let (slot, field_type_id) = self.vir_field_slot_and_type(inner.type_id, field_name)?;
        self.extract_field(inner, slot, field_type_id)
    }

    /// Produce a nil value wrapped in the given optional result type.
    pub(super) fn compile_nil_for_optional(
        &mut self,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let nil_type_id = self.vir_query_nil();
        let zero = self.iconst_cached(types::I8, 0);
        let nil_val = self.compiled_with_ty(zero, types::I8, nil_type_id);
        self.coerce_to_type_id(nil_val, result_type_id)
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
        if self.vir_query_is_struct_v(binding.vole_type) {
            let ptr_type = self.ptr_type();
            let cv = CompiledValue::new(heap_ptr, ptr_type, binding.vole_type);
            return Ok(cv);
        }

        let cranelift_ty = self.cranelift_type_v(binding.vole_type);
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

        // Structs: copy all flat slots from value (stack ptr) to heap slot.
        // Bridge to sema TypeId for struct_flat_slot_count (no compat handling).
        let sema_type_id = self.cv_type_id_from_vir(binding.vole_type);
        if let Some(flat_count) = self.struct_flat_slot_count(sema_type_id) {
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

        let cranelift_ty = self.cranelift_type_v(binding.vole_type);
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

    // =====================================================================
    // VIR null / optional codegen
    // =====================================================================

    /// Compile a VIR `NullCoalesce` expression (`value ?? default`).
    ///
    /// Checks the value for nil; if nil evaluates and returns default,
    /// otherwise unwraps and returns the non-nil payload.  Dispatches to
    /// scalar or union result path based on whether `inner_type` is a union.
    pub(super) fn compile_vir_null_coalesce(
        &mut self,
        value_expr: &VirExpr,
        default_expr: &VirExpr,
        vir_inner_type_id: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let inner_type_id = self.cv_type_id_from_vir(vir_inner_type_id);
        let value = self.compile_vir_expr(value_expr)?;
        let nil_tag = self.find_nil_variant_vir(value.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("null coalesce operator", "optional type", "non-optional")
        })?;

        let is_multi_variant_inner = self.vir_query_is_union(inner_type_id);
        if is_multi_variant_inner {
            self.vir_null_coalesce_union(
                default_expr,
                value,
                inner_type_id,
                vir_inner_type_id,
                nil_tag,
            )
        } else {
            self.vir_null_coalesce_scalar(
                default_expr,
                value,
                inner_type_id,
                vir_inner_type_id,
                nil_tag,
            )
        }
    }

    /// Scalar result path for VIR null coalesce (`T | nil ?? default` -> `T`).
    fn vir_null_coalesce_scalar(
        &mut self,
        default_expr: &VirExpr,
        value: CompiledValue,
        inner_type_id: TypeId,
        vir_inner_type_id: VirTypeId,
        nil_tag: usize,
    ) -> CodegenResult<CompiledValue> {
        let cranelift_type = self.cranelift_type(inner_type_id);

        let is_nil = self.tag_eq(value.value, nil_tag as i64);
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, cranelift_type);

        let result_needs_rc =
            self.rc_scopes.has_active_scope() && self.rc_state_v(vir_inner_type_id).needs_cleanup();

        self.emit_brif(is_nil, nil_block, not_nil_block);

        // Nil branch: evaluate default
        self.switch_and_seal(nil_block);
        let default_val = self.compile_vir_expr(default_expr)?;
        if result_needs_rc && default_val.is_borrowed() {
            self.emit_rc_inc_for_type_v(default_val.value, vir_inner_type_id)?;
        }
        let default_coerced =
            self.coerce_int_type(default_val.value, default_val.ty, cranelift_type);
        let default_arg = BlockArg::from(default_coerced);
        self.builder.ins().jump(merge_block, &[default_arg]);

        // Not-nil branch: extract payload
        self.switch_and_seal(not_nil_block);
        let union_size = self.type_size_v(value.type_id);
        let payload = if union_size > union_layout::TAG_ONLY_SIZE {
            let loaded = self.builder.ins().load(
                cranelift_type,
                MemFlags::new(),
                value.value,
                union_layout::PAYLOAD_OFFSET,
            );
            if result_needs_rc && value.is_borrowed() {
                self.emit_rc_inc_for_type_v(loaded, vir_inner_type_id)?;
            }
            loaded
        } else {
            self.iconst_cached(cranelift_type, 0)
        };
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result, cranelift_type, vir_inner_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    /// Union result path for VIR null coalesce (`A | B | nil ?? default` -> `A | B`).
    fn vir_null_coalesce_union(
        &mut self,
        default_expr: &VirExpr,
        value: CompiledValue,
        inner_type_id: TypeId,
        vir_inner_type_id: VirTypeId,
        nil_tag: usize,
    ) -> CodegenResult<CompiledValue> {
        let ptr_type = self.ptr_type();

        let is_nil = self.tag_eq(value.value, nil_tag as i64);
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, ptr_type);

        self.emit_brif(is_nil, nil_block, not_nil_block);

        // Nil branch: evaluate default, box into union if needed
        self.switch_and_seal(nil_block);
        let default_val = self.compile_vir_expr(default_expr)?;
        let default_ptr = if self.vir_query_is_union_v(default_val.type_id) {
            default_val.value
        } else {
            let boxed = self.construct_union_id(default_val, inner_type_id)?;
            boxed.value
        };
        let default_arg = BlockArg::from(default_ptr);
        self.builder.ins().jump(merge_block, &[default_arg]);

        // Not-nil branch: reuse source pointer (tags are compatible)
        self.switch_and_seal(not_nil_block);
        let value_ptr_arg = BlockArg::from(value.value);
        self.builder.ins().jump(merge_block, &[value_ptr_arg]);

        self.switch_and_seal(merge_block);
        let result_ptr = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result_ptr, ptr_type, vir_inner_type_id);
        Ok(cv)
    }

    /// Compile a VIR `OptionalChain` expression (`obj?.field`).
    ///
    /// Checks the object for nil; if nil produces a nil result, otherwise
    /// extracts the inner value and loads the field.
    pub(super) fn compile_vir_optional_chain(
        &mut self,
        object_expr: &VirExpr,
        field: vole_frontend::Symbol,
        vir_inner_type_id: VirTypeId,
        vir_result_type_id: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let inner_type_id = self.cv_type_id_from_vir(vir_inner_type_id);
        let scrutinee = self.compile_vir_expr(object_expr)?;
        let nil_tag = self
            .find_nil_variant_vir(scrutinee.type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "optional chain operator",
                    "optional type",
                    "non-optional",
                )
            })?;

        let result_type_id = self.cv_type_id_from_vir(vir_result_type_id);
        let result_type_id = self.try_substitute_type(result_type_id);
        let result_vir_ty = self.to_vir_type(result_type_id);
        let result_cranelift_type = self.cranelift_type(result_type_id);
        let result_needs_rc = self.rc_state_v(result_vir_ty).needs_cleanup();

        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, result_cranelift_type);

        let is_nil = self.tag_eq(scrutinee.value, nil_tag as i64);
        self.emit_brif(is_nil, nil_block, not_nil_block);

        // Nil branch: produce nil wrapped as result type
        self.switch_and_seal(nil_block);
        let nil_val = self.compile_nil_for_optional(result_type_id)?;
        self.jump_with_owned_result(
            nil_val,
            result_vir_ty,
            result_cranelift_type,
            result_needs_rc,
            merge_block,
        )?;

        // Not-nil branch: extract inner, do field access
        self.switch_and_seal(not_nil_block);
        let inner = self.extract_optional_inner(scrutinee, inner_type_id);
        let body_val = self.optional_chain_field_access(inner, field)?;
        let body_coerced = self.coerce_to_type(body_val, result_vir_ty)?;
        self.jump_with_owned_result(
            body_coerced,
            result_vir_ty,
            result_cranelift_type,
            result_needs_rc,
            merge_block,
        )?;

        self.switch_and_seal(merge_block);
        self.merge_block_result(merge_block, result_cranelift_type, result_vir_ty, false)
    }

    /// Compile a VIR `OptionalMethodCall` expression (`obj?.method(args)`).
    ///
    /// Checks the object for nil; if nil produces a nil result, otherwise
    /// extracts the inner value and dispatches the method call.  The VIR
    /// fields carry the pre-lowered receiver, method name, args, and the
    /// original NodeId for sema method dispatch lookups.
    pub(super) fn compile_vir_optional_method_call(
        &mut self,
        args: VirOptionalMethodCallArgs<'_>,
    ) -> CodegenResult<CompiledValue> {
        let VirOptionalMethodCallArgs {
            object_expr,
            method,
            method_args,
            dispatch,
            call_node_id,
            inner_type_id: vir_inner_type_id,
            result_type_id: vir_result_type_id,
        } = args;

        let inner_type_id = self.cv_type_id_from_vir(vir_inner_type_id);
        let scrutinee = self.compile_vir_expr(object_expr)?;
        let nil_tag = self
            .find_nil_variant_vir(scrutinee.type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "optional chain operator",
                    "optional type",
                    "non-optional",
                )
            })?;

        let result_type_id = self.try_substitute_type(self.cv_type_id_from_vir(vir_result_type_id));
        let result_vir_ty = self.to_vir_type(result_type_id);
        let result_cranelift_type = self.cranelift_type(result_type_id);
        let result_needs_rc = self.rc_state_v(result_vir_ty).needs_cleanup();

        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, result_cranelift_type);

        let is_nil = self.tag_eq(scrutinee.value, nil_tag as i64);
        self.emit_brif(is_nil, nil_block, not_nil_block);

        // Nil branch
        self.switch_and_seal(nil_block);
        let nil_val = self.compile_nil_for_optional(result_type_id)?;
        self.jump_with_owned_result(
            nil_val,
            result_vir_ty,
            result_cranelift_type,
            result_needs_rc,
            merge_block,
        )?;

        // Not-nil branch: extract inner, call method via VIR method_call path
        self.switch_and_seal(not_nil_block);
        let inner = self.extract_optional_inner(scrutinee, inner_type_id);
        let body_val = self.vir_optional_chain_method_call(
            inner,
            method,
            method_args,
            dispatch,
            call_node_id,
        )?;
        let body_coerced = self.coerce_to_type(body_val, result_vir_ty)?;
        self.jump_with_owned_result(
            body_coerced,
            result_vir_ty,
            result_cranelift_type,
            result_needs_rc,
            merge_block,
        )?;

        self.switch_and_seal(merge_block);
        self.merge_block_result(merge_block, result_cranelift_type, result_vir_ty, false)
    }

    /// Compile a method call on the unwrapped inner value of a VIR optional chain.
    ///
    /// Temporarily inserts the inner value into vars under `$oc` so that
    /// `method_call()` can compile the receiver via `LocalLoad`.
    fn vir_optional_chain_method_call(
        &mut self,
        inner: CompiledValue,
        method: vole_frontend::Symbol,
        method_args: &[vole_vir::VirRef],
        dispatch: &VirMethodDispatchMeta,
        call_node_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Create a Cranelift variable for the inner value
        let inner_var = self.builder.declare_var(inner.ty);
        self.builder.def_var(inner_var, inner.value);

        // Insert into vars under the $oc symbol
        let oc_sym = self.interner().lookup("$oc").expect("$oc must be interned");
        let saved_entry = self.vars.insert(oc_sym, (inner_var, inner.type_id));

        // Build a VIR-native MethodCallSource with $oc as the receiver.
        let inner_vir_ty = inner.type_id;
        let receiver_vir = VirExpr::LocalLoad {
            name: oc_sym,
            ty: inner_vir_ty,
            vir_ty: inner_vir_ty,
        };
        use crate::structs::methods::MethodCallSource;
        let src = MethodCallSource {
            receiver: &receiver_vir,
            method,
            args: method_args,
        };
        let result = self.method_call(&src, call_node_id, dispatch);

        // Restore vars
        if let Some(old) = saved_entry {
            self.vars.insert(oc_sym, old);
        } else {
            self.vars.remove(&oc_sym);
        }

        result
    }

    /// Compile a VIR `Try` expression (`expr?`).
    ///
    /// On success: unwraps and returns the success payload.
    /// On error: propagates by returning from function with (tag, payload).
    pub(super) fn compile_vir_try(
        &mut self,
        value_expr: &VirExpr,
        vir_success_type_id: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let success_type_id = self.cv_type_id_from_vir(vir_success_type_id);
        let fallible = self.compile_vir_expr(value_expr)?;

        // Load tag from fallible (offset 0)
        let tag = load_fallible_tag(self.builder, fallible.value);

        let is_success = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

        let success_block = self.builder.create_block();
        let error_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let payload_ty = self.cranelift_type(success_type_id);
        self.builder.append_block_param(merge_block, payload_ty);

        self.emit_brif(is_success, success_block, error_block);

        // Error block: propagate by returning (tag, payload)
        self.switch_and_seal(error_block);
        let error_payload_i64 = load_fallible_payload(self.builder, fallible.value, types::I64);
        self.builder.ins().return_(&[tag, error_payload_i64]);

        // Success block: extract payload
        self.switch_and_seal(success_block);
        let payload_i64 = load_fallible_payload(self.builder, fallible.value, types::I64);
        let payload = self.convert_from_i64_storage(payload_i64, success_type_id);
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue::new(result, payload_ty, vir_success_type_id))
    }

    /// Extract the inner (non-nil) value from an optional union.
    ///
    /// Reads the payload from the union's data area.  Used by both optional
    /// chain field access and optional chain method call.
    fn extract_optional_inner(
        &mut self,
        scrutinee: CompiledValue,
        inner_type_id: TypeId,
    ) -> CompiledValue {
        let inner_type_id = self.try_substitute_type(inner_type_id);
        let inner_cranelift_type = self.cranelift_type(inner_type_id);
        let union_size = self.type_size_v(scrutinee.type_id);
        if union_size > union_layout::TAG_ONLY_SIZE {
            let loaded = self.builder.ins().load(
                inner_cranelift_type,
                MemFlags::new(),
                scrutinee.value,
                union_layout::PAYLOAD_OFFSET,
            );
            self.compiled_with_ty(loaded, inner_cranelift_type, inner_type_id)
        } else {
            let zero = self.iconst_cached(inner_cranelift_type, 0);
            self.compiled_with_ty(zero, inner_cranelift_type, inner_type_id)
        }
    }

    /// Coerce an integer value to match the target Cranelift type (sextend/ireduce).
    fn coerce_int_type(&mut self, val: Value, from: Type, to: Type) -> Value {
        if from == to {
            val
        } else if from.is_int() && to.is_int() {
            if to.bytes() < from.bytes() {
                self.builder.ins().ireduce(to, val)
            } else {
                self.builder.ins().sextend(to, val)
            }
        } else {
            val
        }
    }
}
