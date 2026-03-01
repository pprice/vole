// src/codegen/structs/access.rs

use super::helpers::reconstruct_i128;
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::CodegenResult;
use crate::types::{CompiledValue, RcLifecycle};
use crate::union_layout;
use cranelift::prelude::*;
use vole_identity::{TypeId, VirTypeId};

impl Cg<'_, '_, '_> {
    /// Convenience wrapper: compute struct field byte offset, panicking on invalid types.
    pub(crate) fn struct_field_byte_offset(&self, type_id: TypeId, slot: usize) -> i32 {
        super::helpers::struct_field_byte_offset(type_id, slot, self.arena(), self.analyzed())
            .expect("INTERNAL: struct field offset must be computable for valid struct type")
    }

    /// Compute total byte size of a struct type (None if type is not a struct).
    pub(crate) fn struct_total_byte_size(&self, type_id: TypeId) -> Option<u32> {
        super::helpers::struct_total_byte_size(type_id, self.arena(), self.analyzed())
    }

    /// Return (byte_offset, cranelift_type) pairs for all flat fields of a struct.
    ///
    /// Returns None if type_id is not a struct. Used for struct equality comparison.
    #[allow(dead_code)] // Bridge method; will be removed by vol-bmeu.
    pub(crate) fn struct_flat_field_cranelift_types(
        &self,
        type_id: TypeId,
    ) -> Option<Vec<(i32, Type)>> {
        super::helpers::struct_flat_field_cranelift_types(type_id, self.arena(), self.analyzed())
    }

    /// VirTypeId-native variant of [`struct_flat_field_cranelift_types`].
    ///
    /// Returns None if `vir_ty` is not a struct. Used for struct equality comparison.
    pub(crate) fn struct_flat_field_cranelift_types_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<Vec<(i32, Type)>> {
        crate::types::vir_struct_helpers::vir_struct_flat_field_cranelift_types(
            vir_ty,
            self.vir_type_table(),
            self.analyzed(),
        )
    }

    /// Extract a field from a container object, handling struct/instance dispatch
    /// and RC cleanup. If the container is an owned RC temporary, the field is
    /// rc_inc'd (if RC) and the container is rc_dec'd so intermediate objects
    /// don't leak.
    pub(crate) fn extract_field(
        &mut self,
        obj: CompiledValue,
        slot: usize,
        field_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Struct types are stack-allocated: load field directly from pointer + offset.
        // Exception: annotation structs used in FieldMeta.annotations are heap-allocated
        // class instances (via InstanceNew), so they must use InstanceGetField.
        let is_struct = self.vir_query_is_struct_v(obj.type_id)
            && !self.is_heap_allocated_annotation_v(obj.type_id);
        if is_struct {
            return self.struct_field_load(
                obj.value,
                slot,
                field_type_id,
                self.cv_type_id_from_vir(obj.type_id),
            );
        }

        // i128 fields use 2 consecutive slots - load both and reconstruct
        let wide = self.vir_query_wide_type(field_type_id);
        let mut cv = if let Some(wide) = wide {
            let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
            let wide_i128 = super::helpers::load_wide_field(self, get_func_ref, obj.value, slot);
            wide.compiled_value_from_i128(self.builder, wide_i128, field_type_id)
        } else {
            let result_raw = self.get_field_cached(obj.value, slot as u32)?;
            self.convert_field_value(result_raw, field_type_id)
        };

        // If the object is an owned RC temporary (e.g., method call result used
        // inline: `obj.method().field`), we must clean it up after extracting
        // the field. If the field itself is RC, we must rc_inc it first so the
        // field value survives the container's rc_dec (which may free the container
        // and cascade to its fields).
        if obj.is_owned() && self.rc_state_v(obj.type_id).needs_cleanup() {
            if self.rc_state(field_type_id).needs_cleanup() {
                self.emit_rc_inc_for_type(cv.value, field_type_id)?;
                // The field is now an owned reference (we inc'd it out of the container)
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            self.emit_rc_dec_for_type_v(obj.value, obj.type_id)?;
        } else {
            self.mark_borrowed_if_rc(&mut cv);
        }

        Ok(cv)
    }

    /// Load a field from a struct pointer at the given slot.
    /// Uses flat layout: nested struct fields are stored inline and
    /// field offsets account for variable-size preceding fields.
    pub fn struct_field_load(
        &mut self,
        struct_ptr: Value,
        slot: usize,
        field_type_id: TypeId,
        parent_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Compute byte offset accounting for nested struct sizes
        let offset = self.struct_field_byte_offset(parent_type_id, slot);

        // If the field is itself a struct, return a pointer into the parent data
        let is_nested_struct = self.vir_query_is_struct(field_type_id);
        if is_nested_struct {
            let ptr_type = self.ptr_type();
            // iadd_imm to compute pointer into the parent struct's inline data
            let field_ptr = if offset == 0 {
                struct_ptr
            } else {
                self.builder.ins().iadd_imm(struct_ptr, offset as i64)
            };
            return Ok(CompiledValue::new(
                field_ptr,
                ptr_type,
                self.vir_lookup(field_type_id),
            ));
        }

        // Payload-carrying union fields are stored inline (16 bytes: tag + payload).
        // Return a pointer into the parent struct, like nested struct fields —
        // union operations expect a pointer to the 16-byte buffer.
        if self.vir_query_is_payload_union(field_type_id) {
            let ptr_type = self.ptr_type();
            let field_ptr = if offset == 0 {
                struct_ptr
            } else {
                self.builder.ins().iadd_imm(struct_ptr, offset as i64)
            };
            return Ok(CompiledValue::new(
                field_ptr,
                ptr_type,
                self.vir_lookup(field_type_id),
            ));
        }

        // i128 fields occupy 2 x 8-byte slots: load low and high halves, reconstruct
        if let Some(wide) = self.vir_query_wide_type(field_type_id) {
            let low = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset);
            let high = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset + 8);
            let wide_i128 = reconstruct_i128(self.builder, low, high);
            return Ok(wide.compiled_value_from_i128(self.builder, wide_i128, field_type_id));
        }

        // Non-struct field: load as i64, then convert to proper type
        let raw_value = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), struct_ptr, offset);
        let mut cv = self.convert_field_value(raw_value, field_type_id);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Assign to a struct's inline union field with proper coercion and RC cleanup.
    ///
    /// 1. RC-dec the old union payload (if any RC variant is active)
    /// 2. Coerce the new value to a union buffer via construct_union_id
    /// 3. Copy the 16-byte buffer inline into the struct
    pub(crate) fn assign_struct_union_field(
        &mut self,
        struct_ptr: Value,
        offset: i32,
        value: CompiledValue,
        field_type_id: TypeId,
    ) -> CodegenResult<()> {
        // RC cleanup of old payload: compute pointer to old inline union,
        // then conditionally rc_dec its payload before overwriting.
        if self.rc_scopes.has_active_scope()
            && let Some(rc_tags) = self.rc_state(field_type_id).union_variants()
        {
            let old_ptr = if offset == 0 {
                struct_ptr
            } else {
                self.builder.ins().iadd_imm(struct_ptr, offset as i64)
            };
            self.emit_union_rc_dec(old_ptr, rc_tags)?;
        }

        // Coerce to union if needed
        let union_val = if !self.vir_query_is_union_v(value.type_id) {
            self.construct_union_id(value, field_type_id)?
        } else {
            value
        };

        // Copy 16-byte union buffer (tag word + payload word) inline
        let word0 = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), union_val.value, 0);
        self.builder
            .ins()
            .store(MemFlags::new(), word0, struct_ptr, offset);
        let word1 = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            union_val.value,
            union_layout::PAYLOAD_OFFSET,
        );
        self.builder.ins().store(
            MemFlags::new(),
            word1,
            struct_ptr,
            offset + union_layout::PAYLOAD_OFFSET,
        );
        Ok(())
    }
}
