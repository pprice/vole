// src/codegen/structs/literals.rs

use super::helpers::{convert_to_i64_for_storage, split_i128_for_storage};
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use crate::union_layout;
use cranelift::prelude::*;
use cranelift_codegen::ir::StackSlot;
use vole_identity::{TypeId, VirTypeId};

impl Cg<'_, '_, '_> {
    /// Coerce a value to match a field's declared type (VirTypeId variant).
    ///
    /// Coerces a value to match a field's declared type using VirTypeId
    /// throughout, with no sema TypeId dependency.
    pub(crate) fn coerce_field_value_v(
        &mut self,
        value: CompiledValue,
        field_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let field_is_union = self.vir_query_is_union_v(field_vir_ty);
        let field_is_interface = self.vir_query_is_interface_v(field_vir_ty);
        let field_is_unknown = self.vir_query_is_unknown_v(field_vir_ty);
        let value_is_union = self.vir_query_is_union_v(value.type_id);
        let value_is_unknown = self.vir_query_is_unknown_v(value.type_id);

        if field_is_unknown && !value_is_unknown {
            self.box_to_unknown_no_inc(value)
        } else if field_is_unknown && value_is_unknown {
            self.copy_tagged_value_to_heap(value)
        } else if field_is_union && !value_is_union {
            self.construct_union_heap_id_v(value, field_vir_ty)
        } else if field_is_union && value_is_union {
            self.copy_union_to_heap(value)
        } else if field_is_interface && self.vir_query_is_interface_v(value.type_id) {
            self.copy_interface_fat_ptr(value)
        } else if field_is_interface {
            self.box_interface_value_v(value, field_vir_ty)
        } else {
            Ok(value)
        }
    }

    /// Coerce a value to match a field's declared type, using a pre-computed
    /// coercion hint.
    ///
    /// The hint fully determines the coercion path with no type queries.
    /// When `hint` is `None` or `Unresolved`, falls back to the full
    /// `coerce_field_value_v()` path.
    pub(crate) fn coerce_field_value_with_hint(
        &mut self,
        value: CompiledValue,
        field_vir_ty: VirTypeId,
        hint: Option<vole_vir::expr::FieldCoercionHint>,
    ) -> CodegenResult<CompiledValue> {
        use vole_vir::expr::FieldCoercionHint;

        match hint {
            Some(FieldCoercionHint::InterfaceBox) => {
                self.box_interface_value_v(value, field_vir_ty)
            }
            Some(FieldCoercionHint::InterfaceCopy) => self.copy_interface_fat_ptr(value),
            Some(FieldCoercionHint::UnknownBox) => self.box_to_unknown_no_inc(value),
            Some(FieldCoercionHint::UnknownCopy) => self.copy_tagged_value_to_heap(value),
            Some(FieldCoercionHint::UnionBox) => {
                self.construct_union_heap_id_v(value, field_vir_ty)
            }
            Some(FieldCoercionHint::UnionCopy) => self.copy_union_to_heap(value),
            Some(FieldCoercionHint::None) => Ok(value),
            Some(FieldCoercionHint::Unresolved) => {
                tracing::warn!(
                    "FieldCoercionHint::Unresolved reached codegen — \
                     should have been resolved during monomorph rederive"
                );
                self.coerce_field_value_v(value, field_vir_ty)
            }
            None => {
                // No hint available — fall back to full type-query path.
                self.coerce_field_value_v(value, field_vir_ty)
            }
        }
    }

    /// Construct a union value on the heap (for storing in class fields).
    /// Unlike the stack-based construct_union_id, this allocates on the heap so the
    /// union persists beyond the current function's stack frame.
    pub(crate) fn construct_union_heap_id(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let union_vir = self.vir_lookup_or_compat(union_type_id);
        let result = self.construct_union_heap_id_v(value, union_vir)?;
        // Re-wrap with original TypeId to preserve caller semantics.
        Ok(self.compiled_with_ty(result.value, result.ty, union_type_id))
    }

    /// VirTypeId variant of [`construct_union_heap_id`](Self::construct_union_heap_id).
    ///
    /// Allocates a union buffer on the heap and stores the tag, is_rc flag,
    /// and payload.  Works entirely with VirTypeId, no sema TypeId needed.
    pub(crate) fn construct_union_heap_id_v(
        &mut self,
        value: CompiledValue,
        union_vir: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let vir_variants = self.vir_query_unwrap_union_v(union_vir).ok_or_else(|| {
            CodegenError::type_mismatch("union construction", "union type", "non-union")
        })?;

        // If the value is already the same union type, just return it
        if value.type_id == union_vir {
            return Ok(value);
        }

        let (tag, actual_value, actual_vir) =
            self.find_union_variant_tag_with_hint_v(&value, union_vir, &vir_variants, None)?;

        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;

        let ptr_type = self.ptr_type();
        let union_size = self.type_size_v(union_vir);
        let size_val = self.iconst_cached(ptr_type, union_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        let tag_val = self.iconst_cached(types::I8, tag as i64);
        self.builder
            .ins()
            .store(MemFlags::new(), tag_val, heap_ptr, 0);

        let is_rc = self.cached_rc_state_v(actual_vir).needs_cleanup();
        let is_rc_val = self.iconst_cached(types::I8, is_rc as i64);
        self.builder.ins().store(
            MemFlags::new(),
            is_rc_val,
            heap_ptr,
            union_layout::IS_RC_OFFSET,
        );

        if !self.vir_query_is_sentinel_v(actual_vir) {
            self.builder.ins().store(
                MemFlags::new(),
                actual_value,
                heap_ptr,
                union_layout::PAYLOAD_OFFSET,
            );
        }

        Ok(CompiledValue::new(heap_ptr, self.ptr_type(), union_vir))
    }

    /// Copy a union value (possibly stack-allocated) to a heap-allocated buffer.
    ///
    /// Union buffers are 16 bytes: `[tag: i8, is_rc: i8, pad(6), payload: i64]`.
    /// Class fields with FieldTypeTag::UnionHeap expect heap-allocated buffers
    /// that will be freed by `union_heap_cleanup` during instance_drop.
    pub(crate) fn copy_union_to_heap(
        &mut self,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let ptr_type = self.ptr_type();
        let union_size = self.type_size_v(value.type_id);
        let size_val = self.iconst_cached(ptr_type, union_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy tag (offset 0) and is_rc (offset 1) as i16 for one load
        let tag_and_rc = self
            .builder
            .ins()
            .load(types::I16, MemFlags::new(), value.value, 0);
        self.builder
            .ins()
            .store(MemFlags::new(), tag_and_rc, heap_ptr, 0);

        // Copy payload (offset 8)
        let payload = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            value.value,
            union_layout::PAYLOAD_OFFSET,
        );
        self.builder.ins().store(
            MemFlags::new(),
            payload,
            heap_ptr,
            union_layout::PAYLOAD_OFFSET,
        );

        // If the payload is RC-managed, increment its refcount since both the
        // original and the copy will need independent cleanup
        let is_rc = self.builder.ins().load(
            types::I8,
            MemFlags::new(),
            value.value,
            union_layout::IS_RC_OFFSET,
        );
        // `is_rc` is already an i8 boolean (0 or 1), so skip the icmp_imm for it.
        // `payload` is i64, so icmp_imm is needed to produce an i8 boolean for `band`.
        let payload_nonzero = self.builder.ins().icmp_imm(IntCC::NotEqual, payload, 0);
        let needs_inc = self.builder.ins().band(is_rc, payload_nonzero);

        let then_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.emit_brif(needs_inc, then_block, merge_block);

        self.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let rc_inc_ref = self.runtime_func_ref(RuntimeKey::RcInc)?;
        let payload_ptr = self
            .builder
            .ins()
            .bitcast(ptr_type, MemFlags::new(), payload);
        self.builder.ins().call(rc_inc_ref, &[payload_ptr]);
        self.builder.ins().jump(merge_block, &[]);

        self.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(CompiledValue::new(heap_ptr, ptr_type, value.type_id))
    }

    /// Copy an interface fat pointer into a new heap allocation.
    ///
    /// Interface fat pointers are 16-byte heap allocations: `[data_word, vtable_ptr]`.
    /// They have no RcHeader, so they cannot be shared between multiple owners.
    /// When storing an interface value into a class field, we must create an
    /// independent copy so that `instance_drop` can free it without invalidating
    /// the original pointer.
    ///
    /// Note: The caller is responsible for rc_inc'ing the data_word if the value
    /// is borrowed (the standard rc_inc at class literal field init handles this).
    pub(crate) fn copy_interface_fat_ptr(
        &mut self,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let ptr_type = self.ptr_type();
        let word_bytes = ptr_type.bytes() as i64;

        // Allocate 16 bytes for [data_word, vtable_ptr]
        let size_val = self.iconst_cached(ptr_type, word_bytes * 2);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy data_word (offset 0)
        let data_word = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 0);
        self.builder
            .ins()
            .store(MemFlags::new(), data_word, heap_ptr, 0);

        // Copy vtable_ptr (offset 8)
        let vtable_ptr =
            self.builder
                .ins()
                .load(types::I64, MemFlags::new(), value.value, word_bytes as i32);
        self.builder
            .ins()
            .store(MemFlags::new(), vtable_ptr, heap_ptr, word_bytes as i32);

        Ok(CompiledValue::new(heap_ptr, ptr_type, value.type_id))
    }

    /// Copy an unknown-typed TaggedValue to a new heap allocation.
    ///
    /// TaggedValues are 16-byte heap buffers: `[tag: i64, value: i64]`.
    /// Used when an existing unknown value needs an independent copy
    /// (e.g., storing an already-unknown value into a class field).
    ///
    /// If the contained value is RC-managed (e.g. a string), the caller must
    /// have already incremented the refcount at the class literal init site.
    pub(crate) fn copy_tagged_value_to_heap(
        &mut self,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let ptr_type = self.ptr_type();

        // Allocate 16 bytes for [tag: i64, value: i64]
        let size_val = self.iconst_cached(ptr_type, union_layout::STANDARD_SIZE as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy tag (offset 0)
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 0);
        self.builder.ins().store(MemFlags::new(), tag, heap_ptr, 0);

        // Copy value (offset 8)
        let payload = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            value.value,
            union_layout::PAYLOAD_OFFSET,
        );
        self.builder.ins().store(
            MemFlags::new(),
            payload,
            heap_ptr,
            union_layout::PAYLOAD_OFFSET,
        );

        Ok(CompiledValue::new(heap_ptr, ptr_type, VirTypeId::UNKNOWN))
    }

    /// Store a value into a struct field's stack slot, handling nested structs,
    /// inline unions, and i128.
    pub(crate) fn store_struct_field(
        &mut self,
        value: CompiledValue,
        slot: StackSlot,
        offset: i32,
    ) -> CodegenResult<()> {
        let field_flat_slots = self.vir_struct_flat_slot_count(value.type_id);
        if let Some(nested_flat) = field_flat_slots {
            for i in 0..nested_flat {
                let src_off = (i as i32) * 8;
                let dst_off = offset + src_off;
                let val =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, src_off);
                self.builder.ins().stack_store(val, slot, dst_off);
            }
        } else if self.vir_query_is_payload_union_v(value.type_id) {
            // Union values are pointers to 16-byte buffers (tag + payload).
            // Copy both words inline into the struct's slot.
            let word0 = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), value.value, 0);
            self.builder.ins().stack_store(word0, slot, offset);
            let word1 = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                value.value,
                union_layout::PAYLOAD_OFFSET,
            );
            self.builder
                .ins()
                .stack_store(word1, slot, offset + union_layout::PAYLOAD_OFFSET);
        } else if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
            // Wide types need 2 x 8-byte slots: low bits at offset, high bits at offset+8.
            let i128_bits = wide.to_i128_bits(self.builder, value.value);
            let (low, high) = split_i128_for_storage(self.builder, i128_bits);
            self.builder.ins().stack_store(low, slot, offset);
            self.builder.ins().stack_store(high, slot, offset + 8);
        } else {
            let store_value = convert_to_i64_for_storage(self.builder, &value);
            self.builder.ins().stack_store(store_value, slot, offset);
        }
        Ok(())
    }
}
