// src/codegen/expr/error_patterns.rs
//
// Error pattern matching, fallible scrutinee cleanup, and record field extraction.

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::CodegenResult;
use crate::types::{
    CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, fallible_error_tag_by_id,
    load_fallible_payload, load_fallible_tag,
};

use vole_frontend::Symbol;
use vole_frontend::ast::RecordFieldPattern;
use vole_identity::TypeId;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    // =========================================================================
    // Fallible scrutinee cleanup
    // =========================================================================

    /// Emit rc_dec for the payload inside a fallible scrutinee after a match.
    ///
    /// Fallible returns are stack-allocated `(tag, payload)` structs that are
    /// never RC-tracked.  When a match arm extracts the payload and rc_inc's it
    /// (because the variable read is Borrowed), the original reference inside
    /// the fallible struct must be decremented to avoid a leak.
    ///
    /// If only one variant's payload is RC, we branch on the tag so we only
    /// rc_dec when that variant was active.
    pub(super) fn cleanup_fallible_scrutinee(
        &mut self,
        scrutinee: &CompiledValue,
        scrutinee_type_id: TypeId,
    ) -> CodegenResult<()> {
        let fallible_types = self.vir_query_unwrap_fallible(scrutinee_type_id);
        let Some((success_type_id, error_type_id)) = fallible_types else {
            return Ok(());
        };

        let success_rc = self.rc_state(success_type_id).needs_cleanup();
        // Error types may have RC payloads even though the error struct itself
        // isn't RC-tracked.  Single-field error structs store their field value
        // directly as the payload (no wrapping pointer), so if that field is RC
        // we must rc_dec the payload.
        let error_rc = self.rc_state(error_type_id).needs_cleanup()
            || self.fallible_error_payload_needs_rc(error_type_id);

        if !success_rc && !error_rc {
            return Ok(());
        }

        let payload = load_fallible_payload(self.builder, scrutinee.value, types::I64);

        if success_rc && error_rc {
            // Both variants need cleanup — unconditional rc_dec
            self.emit_rc_dec(payload)?;
        } else {
            // Only one variant needs cleanup — branch on tag
            let tag = load_fallible_tag(self.builder, scrutinee.value);
            let is_success = self
                .builder
                .ins()
                .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

            let dec_block = self.builder.create_block();
            let cont_block = self.builder.create_block();

            if success_rc {
                // rc_dec only on success path
                self.emit_brif(is_success, dec_block, cont_block);
            } else {
                // rc_dec only on error path
                self.emit_brif(is_success, cont_block, dec_block);
            }

            self.switch_to_block(dec_block);
            self.builder.seal_block(dec_block);
            self.emit_rc_dec(payload)?;
            self.builder.ins().jump(cont_block, &[]);

            self.switch_to_block(cont_block);
            self.builder.seal_block(cont_block);
        }

        Ok(())
    }

    /// Check whether the payload stored for an error variant is an RC value
    /// and is safe to unconditionally rc_dec.
    ///
    /// Single-field error structs (e.g. `NotFound { path: string }`) store the
    /// field value directly as the fallible payload.  If that single field is
    /// RC-managed the payload pointer must be rc_dec'd.
    ///
    /// For union error types, this returns true only when ALL variants are safe
    /// to rc_dec: either 0 fields (payload=null, rc_dec is no-op) or 1 RC field.
    /// Mixed unions (some RC, some non-RC single-field) are NOT safe and we skip
    /// cleanup to avoid calling rc_dec on non-pointer values.
    fn fallible_error_payload_needs_rc(&self, error_type_id: TypeId) -> bool {
        if self.error_type_single_field_is_rc(error_type_id) {
            return true;
        }
        if let Some(variants) = self.vir_query_unwrap_union(error_type_id) {
            // All variants must be safe for unconditional rc_dec:
            // - 0 fields: payload is null (rc_dec is no-op)
            // - 1 RC field: payload is an RC pointer (rc_dec works)
            // If ANY variant has 1 non-RC field or 2+ fields, we can't safely rc_dec.
            let any_rc = variants
                .iter()
                .any(|&tid| self.error_type_single_field_is_rc(tid));
            let all_safe = any_rc
                && variants
                    .iter()
                    .all(|&tid| self.error_variant_safe_for_rc_dec(tid));
            return all_safe;
        }
        false
    }

    /// Check if an error variant is safe for unconditional rc_dec.
    /// True for: 0 fields (null payload) or 1 RC field.
    fn error_variant_safe_for_rc_dec(&self, type_id: TypeId) -> bool {
        let Some(type_def_id) = self.vir_query_unwrap_error_or_struct_def(type_id) else {
            return false;
        };
        let fields: Vec<_> = self.analyzed().fields_on_type(type_def_id).collect();
        match fields.len() {
            0 => true, // null payload, rc_dec is no-op
            1 => {
                let field = self.analyzed().field_def(fields[0]);
                self.rc_state(field.sema_type_id).needs_cleanup()
            }
            _ => false, // 2+ fields = stack pointer, NOT safe for rc_dec
        }
    }

    /// Check if an error/struct type has exactly one field and that field is RC.
    fn error_type_single_field_is_rc(&self, type_id: TypeId) -> bool {
        let Some(type_def_id) = self.vir_query_unwrap_error_or_struct_def(type_id) else {
            return false;
        };
        let fields: Vec<_> = self.analyzed().fields_on_type(type_def_id).collect();
        if fields.len() != 1 {
            return false;
        }
        let field = self.analyzed().field_def(fields[0]);
        self.rc_state(field.sema_type_id).needs_cleanup()
    }

    // =========================================================================
    // Record field extraction helpers
    // =========================================================================

    /// Look up the numeric error tag for a named error type within a fallible error union.
    ///
    /// Thin wrapper around `fallible_error_tag_by_id` that pulls all context
    /// arguments from `self`.
    pub(crate) fn error_tag_for(&self, error_type_id: TypeId, error_name: Symbol) -> Option<i64> {
        fallible_error_tag_by_id(
            error_type_id,
            error_name,
            self.arena(),
            self.interner(),
            self.name_table(),
            self.analyzed(),
        )
    }

    /// Extract field bindings from an error record pattern. Loads fields from the
    /// error payload according to their layout (inline single field, wide i128, or
    /// pointer-based multi-field).
    pub(super) fn extract_error_field_bindings(
        &mut self,
        error_type_def_id: vole_identity::TypeDefId,
        scrutinee_value: Value,
        fields: &[RecordFieldPattern],
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<()> {
        // Get fields from EntityRegistry
        let error_fields: Vec<_> = self
            .analyzed()
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.analyzed().field_def(field_id).clone())
            .collect();

        // Fallible layout (consistent with external functions in runtime):
        // - Offset 0: tag (i64)
        // - Offset 8: payload (i64)
        //   - For 0 fields: 0
        //   - For 1 non-wide field: the field value directly (inline)
        //   - For 1 wide (i128) field or 2+ fields: pointer to field data
        //
        // Load the payload from the fallible
        let payload = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            scrutinee_value,
            FALLIBLE_PAYLOAD_OFFSET,
        );

        // For single non-wide field errors, the payload IS the field value
        // For single wide (i128) field or multi-field errors, payload is a pointer to field data
        let has_any_wide = error_fields
            .iter()
            .any(|f| crate::types::is_wide_type(f.sema_type_id, self.arena()));
        let inline_single_field = error_fields.len() == 1 && !has_any_wide;

        // Precompute field byte offsets (i128 fields use 16 bytes, others 8)
        let field_byte_offsets: Vec<i32> = {
            let arena = self.arena();
            let mut offset = 0i32;
            error_fields
                .iter()
                .map(|f| {
                    let current = offset;
                    offset += crate::types::field_byte_size(f.sema_type_id, arena) as i32;
                    current
                })
                .collect()
        };

        for field_pattern in fields {
            let field_name = self.interner().resolve(field_pattern.field_name);

            // Find the field index and type in the error type
            let Some((field_idx, field_def)) = error_fields.iter().enumerate().find(|(_, f)| {
                self.name_table().last_segment_str(f.name_id).as_deref() == Some(field_name)
            }) else {
                continue;
            };

            let field_ty_id = field_def.sema_type_id;
            let is_wide = crate::types::is_wide_type(field_ty_id, self.arena());

            // Load the field value
            if inline_single_field {
                // For single non-wide field errors, the payload is the value directly
                let converted = self.convert_field_value(payload, field_ty_id);
                let var = self.builder.declare_var(converted.ty);
                self.builder.def_var(var, converted.value);
                arm_variables.insert(field_pattern.binding, (var, field_ty_id));
            } else if is_wide {
                // Wide (i128/f128) field in multi-field or single-wide-field error.
                let field_offset = field_byte_offsets[field_idx];
                let low =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), payload, field_offset);
                let high =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), payload, field_offset + 8);
                let wide_i128 = super::super::structs::reconstruct_i128(self.builder, low, high);
                // `is_wide` guard above guarantees this is Some.
                let wide =
                    crate::types::wide_ops::WideType::from_type_id(field_ty_id, self.arena())
                        .unwrap();
                let wide_val = wide.reinterpret_i128(self.builder, wide_i128);
                let wide_ty = wide.cranelift_type();
                let var = self.builder.declare_var(wide_ty);
                self.builder.def_var(var, wide_val);
                arm_variables.insert(field_pattern.binding, (var, field_ty_id));
            } else {
                // Non-wide field in multi-field error, payload is a pointer to field data
                let field_offset = field_byte_offsets[field_idx];
                let raw_value =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), payload, field_offset);
                let converted = self.convert_field_value(raw_value, field_ty_id);
                let var = self.builder.declare_var(converted.ty);
                self.builder.def_var(var, converted.value);
                arm_variables.insert(field_pattern.binding, (var, field_ty_id));
            }
        }

        Ok(())
    }
}
