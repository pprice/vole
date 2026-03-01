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
    /// Coerce a value to match a field's declared type.
    ///
    /// Handles union wrapping (non-union → union, union → heap copy),
    /// interface boxing, unknown boxing, and interface fat pointer copying
    /// for class fields.
    pub(crate) fn coerce_field_value(
        &mut self,
        value: CompiledValue,
        field_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let field_is_union = self.vir_query_is_union(field_type_id);
        let field_is_interface = self.vir_query_is_interface(field_type_id);
        let field_is_unknown = self.vir_query_is_unknown(field_type_id);
        let value_is_union = self.vir_query_is_union_v(value.type_id);
        let value_is_unknown = self.vir_query_is_unknown_v(value.type_id);

        if field_is_unknown && !value_is_unknown {
            // Box the value into a heap-allocated TaggedValue.
            // box_to_unknown() heap-allocates, so no further copy needed.
            // Use _no_inc because the class literal init site already rc_inc'd
            // borrowed values before calling coerce_field_value.
            self.box_to_unknown_no_inc(value)
        } else if field_is_unknown && value_is_unknown {
            // Value is already a TaggedValue pointer. Copy to heap so
            // instance_drop can free it independently.
            self.copy_tagged_value_to_heap(value)
        } else if field_is_union && !value_is_union {
            self.construct_union_heap_id(value, field_type_id)
        } else if field_is_union && value_is_union {
            // Union value stored in class field must be heap-allocated.
            // The value may be stack-allocated (from construct_union_id),
            // so copy the 16-byte buffer to the heap.
            self.copy_union_to_heap(value)
        } else if field_is_interface && self.vir_query_is_interface_v(value.type_id) {
            // Value is already an interface fat pointer. Copy it into a new
            // heap allocation so instance_drop can free it independently.
            self.copy_interface_fat_ptr(value)
        } else if field_is_interface {
            self.box_interface_value(value, field_type_id)
        } else {
            Ok(value)
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
        let variants = self
            .vir_query_unwrap_union_sema(union_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch("union construction", "union type", "non-union")
            })?;

        // If the value is already the same union type, just return it
        if value.type_id == self.vir_lookup(union_type_id) {
            return Ok(value);
        }

        let (tag, actual_value, actual_type_id) =
            self.find_union_variant_tag(&value, union_type_id, &variants)?;

        // Get heap_alloc function ref
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;

        // Allocate union storage on the heap
        let ptr_type = self.ptr_type();
        let union_size = self.type_size(union_type_id);
        let size_val = self.iconst_cached(ptr_type, union_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Store tag at offset 0
        let tag_val = self.iconst_cached(types::I8, tag as i64);
        self.builder
            .ins()
            .store(MemFlags::new(), tag_val, heap_ptr, 0);

        // Store is_rc flag at offset 1: 1 if the variant is RC-managed, 0 otherwise.
        // This flag is used by union_heap_cleanup to know whether to rc_dec the payload.
        let is_rc = self.rc_state(actual_type_id).needs_cleanup();
        let is_rc_val = self.iconst_cached(types::I8, is_rc as i64);
        self.builder.ins().store(
            MemFlags::new(),
            is_rc_val,
            heap_ptr,
            union_layout::IS_RC_OFFSET,
        );

        // Sentinel types (nil, Done, user-defined) have no payload - only the tag matters
        if !self.vir_query_is_sentinel(actual_type_id) {
            self.builder.ins().store(
                MemFlags::new(),
                actual_value,
                heap_ptr,
                union_layout::PAYLOAD_OFFSET,
            );
        }

        Ok(CompiledValue::new(
            heap_ptr,
            self.ptr_type(),
            self.vir_lookup(union_type_id),
        ))
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
