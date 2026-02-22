// src/codegen/expr/error_patterns.rs
//
// Error pattern matching, fallible scrutinee cleanup, and record field extraction.

use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::CodegenResult;
use crate::types::{
    CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, fallible_error_tag_by_id,
    load_fallible_payload, load_fallible_tag, type_id_to_cranelift,
};

use vole_frontend::ast::RecordFieldPattern;
use vole_frontend::{Pattern, PatternKind, Symbol};
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;
use super::super::structs::get_field_slot_and_type_id_cg;

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
        let fallible_types = self.arena().unwrap_fallible(scrutinee_type_id);
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
        let arena = self.arena();
        if let Some(variants) = arena.unwrap_union(error_type_id) {
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
        let Some(type_def_id) = self.arena().unwrap_error_or_struct_def(type_id) else {
            return false;
        };
        let fields: Vec<_> = self.query().fields_on_type(type_def_id).collect();
        match fields.len() {
            0 => true, // null payload, rc_dec is no-op
            1 => {
                let field = self.query().get_field(fields[0]);
                self.rc_state(field.ty).needs_cleanup()
            }
            _ => false, // 2+ fields = stack pointer, NOT safe for rc_dec
        }
    }

    /// Check if an error/struct type has exactly one field and that field is RC.
    fn error_type_single_field_is_rc(&self, type_id: TypeId) -> bool {
        let Some(type_def_id) = self.arena().unwrap_error_or_struct_def(type_id) else {
            return false;
        };
        let fields: Vec<_> = self.query().fields_on_type(type_def_id).collect();
        if fields.len() != 1 {
            return false;
        }
        let field = self.query().get_field(fields[0]);
        self.rc_state(field.ty).needs_cleanup()
    }

    // =========================================================================
    // Error pattern helpers
    // =========================================================================

    /// Compile an error pattern match, returning the condition value.
    pub(super) fn compile_error_pattern(
        &mut self,
        inner: &Option<Box<Pattern>>,
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let Some(inner_pat) = inner else {
            // Bare error pattern: error => ...
            let is_error = self
                .builder
                .ins()
                .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
            return Ok(Some(is_error));
        };

        match &inner_pat.kind {
            PatternKind::Identifier { name } => {
                self.compile_error_identifier_pattern(*name, scrutinee, tag, arm_variables)
            }
            PatternKind::Record {
                type_name: Some(type_expr),
                fields,
            } => {
                if let Some(name) = Self::type_expr_terminal_symbol(type_expr) {
                    self.compile_error_record_pattern(name, fields, scrutinee, tag, arm_variables)
                } else {
                    let is_error =
                        self.builder
                            .ins()
                            .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                    Ok(Some(is_error))
                }
            }
            _ => {
                // Catch-all for other patterns (like wildcard)
                let is_error =
                    self.builder
                        .ins()
                        .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                Ok(Some(is_error))
            }
        }
    }

    /// Compile an identifier pattern inside an error pattern.
    /// Handles both specific error types (error DivByZero) and catch-all bindings (error e).
    fn compile_error_identifier_pattern(
        &mut self,
        name: Symbol,
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        // Check if this is an error type name by looking in the fallible's error union.
        // This handles error types from imported modules that aren't in the consumer's scope.
        let is_error_type = self
            .resolve_type(name)
            .is_some_and(|type_id| self.query().is_error_type(type_id))
            || {
                // Fallback: check if name matches an error type in the fallible's error union
                self.arena()
                    .unwrap_fallible(scrutinee.type_id)
                    .and_then(|(_, error_type_id)| self.error_tag_for(error_type_id, name))
                    .is_some()
            };

        if is_error_type {
            return self.compile_specific_error_type_pattern(name, scrutinee, tag);
        }

        // Catch-all error binding: error e => ...
        let is_error = self
            .builder
            .ins()
            .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);

        // Extract error type and bind
        // Get types before using builder to avoid borrow conflict
        let error_type_opt = self.arena().unwrap_fallible(scrutinee.type_id);
        if let Some((_, error_type_id)) = error_type_opt {
            let ptr_type = self.ptr_type();
            let payload_ty = {
                let arena = self.arena();
                type_id_to_cranelift(error_type_id, arena, ptr_type)
            };
            let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);
            let var = self.builder.declare_var(payload_ty);
            self.builder.def_var(var, payload);
            arm_variables.insert(name, (var, error_type_id));
        }

        Ok(Some(is_error))
    }

    /// Compile a specific error type pattern (e.g., error DivByZero).
    fn compile_specific_error_type_pattern(
        &mut self,
        name: Symbol,
        scrutinee: &CompiledValue,
        tag: Value,
    ) -> CodegenResult<Option<Value>> {
        let Some((_success_type_id, error_type_id)) =
            self.arena().unwrap_fallible(scrutinee.type_id)
        else {
            // Not matching on a fallible type
            return Ok(Some(self.iconst_cached(types::I8, 0)));
        };

        let Some(error_tag) = self.error_tag_for(error_type_id, name) else {
            // Error type not found in fallible - will never match
            return Ok(Some(self.iconst_cached(types::I8, 0)));
        };

        let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, error_tag);
        Ok(Some(is_this_error))
    }

    // =========================================================================
    // Record field extraction helpers
    // =========================================================================

    /// Look up the numeric error tag for a named error type within a fallible error union.
    ///
    /// Thin wrapper around `fallible_error_tag_by_id` that pulls all context
    /// arguments from `self`, keeping call sites free of `self.registry()` passes.
    pub(crate) fn error_tag_for(&self, error_type_id: TypeId, error_name: Symbol) -> Option<i64> {
        fallible_error_tag_by_id(
            error_type_id,
            error_name,
            self.arena(),
            self.interner(),
            self.name_table(),
            self.registry(),
        )
    }

    /// Extract and bind fields from a destructure pattern source.
    ///
    /// For class/instance types, uses `InstanceGetField` runtime call.
    /// For struct types (auto-boxed in unions), uses `struct_field_load` since the
    /// source pointer is a raw heap pointer, not an `RcInstance`.
    pub(super) fn extract_record_fields(
        &mut self,
        fields: &[RecordFieldPattern],
        field_source: Value,
        field_source_type_id: TypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<()> {
        let is_struct = self.arena().is_struct(field_source_type_id);
        for field_pattern in fields {
            let field_name = self.interner().resolve(field_pattern.field_name);
            let (slot, field_type_id) =
                get_field_slot_and_type_id_cg(field_source_type_id, field_name, self)?;

            let converted = if is_struct {
                // Struct was auto-boxed: field_source is a raw heap pointer
                // with fields at flat offsets, same layout as stack structs
                self.struct_field_load(field_source, slot, field_type_id, field_source_type_id)?
            } else {
                // Class/instance: use runtime InstanceGetField
                self.get_instance_field(field_source, slot, field_type_id)?
            };
            let var = self.builder.declare_var(converted.ty);
            self.builder.def_var(var, converted.value);
            arm_variables.insert(field_pattern.binding, (var, field_type_id));
        }
        Ok(())
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
            .query()
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.query().get_field(field_id).clone())
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
            .any(|f| crate::types::is_wide_type(f.ty, self.arena()));
        let inline_single_field = error_fields.len() == 1 && !has_any_wide;

        // Precompute field byte offsets (i128 fields use 16 bytes, others 8)
        let field_byte_offsets: Vec<i32> = {
            let arena = self.arena();
            let mut offset = 0i32;
            error_fields
                .iter()
                .map(|f| {
                    let current = offset;
                    offset += crate::types::field_byte_size(f.ty, arena) as i32;
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

            let field_ty_id = field_def.ty;
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

    /// Compile a destructure pattern inside an error pattern (e.g., error Overflow { value, max }).
    pub(super) fn compile_error_record_pattern(
        &mut self,
        name: Symbol,
        fields: &[RecordFieldPattern],
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        // Look up error type_def_id via EntityRegistry, with fallback to
        // searching the fallible's error union for imported module error types
        let error_type_id = self
            .resolve_type(name)
            .and_then(|type_id| {
                if self.query().is_error_type_with_info(type_id) {
                    Some(type_id)
                } else {
                    None
                }
            })
            .or_else(|| {
                // Fallback: search error types in the fallible's error union by name
                let name_str = self.interner().resolve(name);
                let arena = self.arena();
                let (_, error_union_id) = arena.unwrap_fallible(scrutinee.type_id)?;
                self.find_error_type_in_union(error_union_id, name_str)
            });

        let Some(error_type_def_id) = error_type_id else {
            // Unknown error type
            return Ok(Some(self.iconst_cached(types::I8, 0)));
        };

        let Some((_success_type_id, fallible_error_type_id)) =
            self.arena().unwrap_fallible(scrutinee.type_id)
        else {
            return Ok(Some(self.iconst_cached(types::I8, 0)));
        };

        let Some(error_tag) = self.error_tag_for(fallible_error_type_id, name) else {
            // Error type not found in fallible
            return Ok(Some(self.iconst_cached(types::I8, 0)));
        };

        let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, error_tag);

        self.extract_error_field_bindings(
            error_type_def_id,
            scrutinee.value,
            fields,
            arm_variables,
        )?;

        Ok(Some(is_this_error))
    }
}
