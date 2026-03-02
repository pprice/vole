// src/codegen/structs/vir_literals.rs
//
// VIR struct literal and class instance codegen.
// Mirrors the AST-based paths in `literals.rs` but compiles field
// values from VIR expressions.

use std::collections::{HashMap, HashSet};

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use rustc_hash::FxHashMap;

use super::helpers::store_field_value;
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use vole_frontend::Symbol;
use vole_identity::{TypeId, VirTypeId};
use vole_runtime::value::RuntimeTypeId;

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Compile a VIR struct literal (stack-allocated value type).
    ///
    /// Mirrors `struct_value_literal()` but compiles field values from VIR
    /// expressions instead of AST nodes. Omitted default fields are compiled
    /// from pre-lowered VIR defaults keyed by semantic `FieldId`.
    pub(crate) fn compile_vir_struct_literal(
        &mut self,
        type_def_id: vole_identity::TypeDefId,
        fields: &[(Symbol, vole_vir::VirRef)],
        vir_result_type_id: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let table = self.vir_type_table();
        let result_type_id = table
            .lookup_vir_type_id(vir_result_type_id)
            .unwrap_or_else(|| vir_result_type_id.to_type_id_lossy());
        // Sentinels are zero-field structs represented as i8(0).
        if self.analyzed().is_sentinel_type(type_def_id) {
            let value = self.iconst_cached(types::I8, 0);
            return Ok(self.compiled_with_ty(value, types::I8, result_type_id));
        }

        let metadata = self.type_metadata().get(&type_def_id).ok_or_else(|| {
            CodegenError::not_found("type in type_metadata", format!("{type_def_id:?}"))
        })?;
        let field_slots = metadata.field_slots.clone();

        // Prefer the VIR-provided result type, but fall back to metadata type_id
        // when VIR->sema mapping degraded to UNKNOWN during migration.
        // TEMP(N279-C): remove fallback once struct literals are VirTypeId-native.
        let preferred_type_id = self.try_substitute_type(result_type_id);
        let layout_type_id = if self.struct_total_byte_size(preferred_type_id).is_some() {
            preferred_type_id
        } else {
            let fallback = self
                .analyzed()
                .type_def(type_def_id)
                .base_type_id
                .map(|ty| self.try_substitute_type(ty))
                .unwrap_or(TypeId::UNKNOWN);
            if self.struct_total_byte_size(fallback).is_some() {
                fallback
            } else {
                return Err(CodegenError::internal_with_context(
                    "struct literal layout type unavailable",
                    format!(
                        "type_def_id={type_def_id:?}, preferred={preferred_type_id:?}, fallback={fallback:?}"
                    ),
                ));
            }
        };
        let total_size = self.struct_total_byte_size(layout_type_id).ok_or_else(|| {
            CodegenError::internal_with_context(
                "struct literal size lookup failed",
                format!("type_id={layout_type_id:?}, type_def_id={type_def_id:?}"),
            )
        })?;
        let slot = self.alloc_stack(total_size);

        let field_types = self.collect_field_types(type_def_id);

        // Compile and store each explicitly provided field.
        for (name, value_expr) in fields {
            let init_name = self.interner().resolve(*name);
            let field_slot = *field_slots.get(init_name).ok_or_else(|| {
                CodegenError::not_found("field", format!("{init_name} in struct"))
            })?;
            let offset = self.struct_field_byte_offset(layout_type_id, field_slot);
            let mut value = if let Some(&(field_sema_ty, _)) = field_types.get(init_name) {
                self.compile_vir_expr_with_expected_type(value_expr, field_sema_ty)?
            } else {
                self.compile_vir_expr(value_expr)?
            };
            self.coerce_struct_field(&field_types, init_name, &mut value)?;
            self.store_struct_field(value, slot, offset)?;
            value.mark_consumed();
            value.debug_assert_rc_handled("struct literal field");
        }

        // Handle omitted fields with default values.
        self.compile_struct_defaults(
            type_def_id,
            fields,
            &field_slots,
            &field_types,
            layout_type_id,
            slot,
        )?;

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(self.compiled_with_ty(ptr, ptr_type, layout_type_id))
    }

    /// Compile a VIR class instance (heap-allocated reference type).
    ///
    /// Mirrors the class path of `struct_literal()` but compiles field values
    /// from VIR expressions.  Default fields are compiled from AST.
    pub(crate) fn compile_vir_class_instance(
        &mut self,
        type_def_id: vole_identity::TypeDefId,
        fields: &[(Symbol, vole_vir::VirRef)],
        vir_result_type_id: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let table = self.vir_type_table();
        let result_type_id = table
            .lookup_vir_type_id(vir_result_type_id)
            .unwrap_or_else(|| vir_result_type_id.to_type_id_lossy());
        // Sentinels are zero-field structs represented as i8(0).
        if self.analyzed().is_sentinel_type(type_def_id) {
            let value = self.iconst_cached(types::I8, 0);
            return Ok(self.compiled_with_ty(value, types::I8, result_type_id));
        }

        let metadata = self.type_metadata().get(&type_def_id).ok_or_else(|| {
            CodegenError::not_found("type in type_metadata", format!("{type_def_id:?}"))
        })?;
        let base_type_id = metadata.type_id;
        let field_count = metadata.physical_slot_count as u32;
        let field_slots = metadata.field_slots.clone();

        // Substitute type for monomorphized generic instances.
        let result_type_id = self.try_substitute_type(result_type_id);
        let type_id = self.resolve_class_mono_type_id(type_def_id, base_type_id, result_type_id);

        // Allocate instance on the heap.
        let instance_ptr = self.allocate_class_instance(type_id, field_count)?;

        let set_func_ref = self.runtime_func_ref(RuntimeKey::InstanceSetField)?;
        let field_types = self.collect_field_types(type_def_id);

        // Compile and store each explicitly provided field.
        for (name, value_expr) in fields {
            self.compile_class_field_vir(
                *name,
                value_expr,
                &field_slots,
                &field_types,
                set_func_ref,
                instance_ptr,
            )?;
        }

        // Handle omitted fields with default values.
        self.compile_class_defaults(
            type_def_id,
            fields,
            &field_slots,
            &field_types,
            set_func_ref,
            instance_ptr,
        )?;

        Ok(self.compiled_with_ty(instance_ptr, self.ptr_type(), result_type_id))
    }

    /// Collect field name -> (TypeId, VirTypeId) mapping for a type definition.
    ///
    /// Returns both sema `TypeId` (for downstream arena-based operations like
    /// `construct_union_id`) and `VirTypeId` (for VIR-native queries like
    /// `vir_query_is_union_v`).  The sema TypeId comes from the field's
    /// `sema_type_id` (set during VIR lowering) with monomorphization
    /// substitution applied.  The VirTypeId is substituted in the VIR domain.
    ///
    /// We use the sema TypeId from entity metadata rather than converting
    /// from VirTypeId because entity metadata VirTypeIds for generic type
    /// parameters may be out of sync with the codegen type table (they are
    /// interned in a separate cloned table during lowering).
    fn collect_field_types(
        &self,
        type_def_id: vole_identity::TypeDefId,
    ) -> HashMap<String, (TypeId, VirTypeId)> {
        self.analyzed()
            .fields_on_type(type_def_id)
            .map(|field_id| {
                let field = self.analyzed().field_def(field_id);
                let vir_ty = self.try_substitute_type_v(field.vir_ty);
                let sema_ty =
                    self.try_substitute_type(self.analyzed().entity_field_sema_type(field_id));
                let name = self
                    .name_table()
                    .last_segment_str(field.name_id)
                    .unwrap_or_default();
                (name, (sema_ty, vir_ty))
            })
            .collect()
    }

    /// Coerce a struct field value: RC inc borrowed values, box to unknown,
    /// and wrap non-union values into union fields.
    fn coerce_struct_field(
        &mut self,
        field_types: &HashMap<String, (TypeId, VirTypeId)>,
        field_name: &str,
        value: &mut CompiledValue,
    ) -> CodegenResult<()> {
        // RC: inc borrowed field values so the struct gets its own reference.
        if self.rc_scopes.has_active_scope()
            && self.rc_state_v(value.type_id).needs_cleanup()
            && value.is_borrowed()
        {
            self.emit_rc_inc_for_type_v(value.value, value.type_id)?;
        }
        // Coerce to unknown when the field type is unknown.
        if let Some(&(_, field_vir_ty)) = field_types.get(field_name)
            && self.vir_query_is_unknown_v(field_vir_ty)
            && !self.vir_query_is_unknown_v(value.type_id)
        {
            *value = self.box_to_unknown_no_inc(*value)?;
        }
        // Coerce non-union to union for payload-carrying union fields.
        if let Some(&(field_sema_ty, field_vir_ty)) = field_types.get(field_name)
            && self.vir_query_is_payload_union_v(field_vir_ty)
            && !self.vir_query_is_union_v(value.type_id)
        {
            *value = self.construct_union_id(*value, field_sema_ty)?;
        }
        Ok(())
    }

    /// Compile default field values for a VIR struct literal.
    fn compile_struct_defaults(
        &mut self,
        type_def_id: vole_identity::TypeDefId,
        provided: &[(Symbol, vole_vir::VirRef)],
        field_slots: &FxHashMap<String, usize>,
        field_types: &HashMap<String, (TypeId, VirTypeId)>,
        result_type_id: TypeId,
        slot: cranelift_codegen::ir::StackSlot,
    ) -> CodegenResult<()> {
        let provided_fields: HashSet<String> = provided
            .iter()
            .map(|(name, _)| self.interner().resolve(*name).to_string())
            .collect();
        let field_ids: Vec<_> = self.analyzed().fields_on_type(type_def_id).collect();
        for field_id in field_ids {
            let field = self.analyzed().field_def(field_id);
            let Some(field_name) = self.name_table().last_segment_str(field.name_id) else {
                continue;
            };
            if provided_fields.contains(&field_name) {
                continue;
            }
            let Some(default_expr) = self.field_default_vir_init(field_id).cloned() else {
                continue;
            };
            let field_slot = *field_slots.get(&field_name).ok_or_else(|| {
                CodegenError::not_found("field", format!("{field_name} in struct"))
            })?;
            let offset = self.struct_field_byte_offset(result_type_id, field_slot);
            let mut value = if let Some(&(field_sema_ty, _)) = field_types.get(&field_name) {
                self.compile_vir_expr_with_expected_type(&default_expr, field_sema_ty)?
            } else {
                self.compile_vir_expr(&default_expr)?
            };
            // Coerce concrete defaults to unknown.
            if let Some(&(_, field_vir_ty)) = field_types.get(&field_name)
                && self.vir_query_is_unknown_v(field_vir_ty)
                && !self.vir_query_is_unknown_v(value.type_id)
            {
                value = self.box_to_unknown(value)?;
            }
            // Coerce non-union defaults to union.
            if let Some(&(field_sema_ty, field_vir_ty)) = field_types.get(&field_name)
                && self.vir_query_is_payload_union_v(field_vir_ty)
                && !self.vir_query_is_union_v(value.type_id)
            {
                value = self.construct_union_id(value, field_sema_ty)?;
            }
            self.store_struct_field(value, slot, offset)?;
        }
        Ok(())
    }

    /// Resolve the monomorphized type_id for a class instance.
    ///
    /// In monomorphized contexts, computes the correct concrete type args
    /// by looking up each class type parameter in the current function's
    /// substitution map.
    fn resolve_class_mono_type_id(
        &self,
        type_def_id: vole_identity::TypeDefId,
        base_type_id: u32,
        result_type_id: TypeId,
    ) -> u32 {
        if let Some(subs) = self.substitutions {
            let type_def = self.analyzed().type_def(type_def_id);
            if type_def.is_generic && !type_def.type_params.is_empty() {
                let table = self.vir_type_table();
                let concrete_args: Vec<TypeId> = type_def
                    .type_params
                    .iter()
                    .filter_map(|&tp| {
                        subs.get(&tp).copied().map(|v| {
                            table
                                .lookup_vir_type_id(v)
                                .unwrap_or_else(|| v.to_type_id_lossy())
                        })
                    })
                    .collect();
                if concrete_args.len() == type_def.type_params.len() {
                    self.mono_instance_type_id_with_args(base_type_id, type_def_id, concrete_args)
                } else {
                    let result_type_id = self.substitute_type(result_type_id);
                    self.mono_instance_type_id(base_type_id, result_type_id)
                }
            } else {
                base_type_id
            }
        } else {
            self.mono_instance_type_id(base_type_id, result_type_id)
        }
    }

    /// Allocate a class instance on the heap via the runtime.
    fn allocate_class_instance(&mut self, type_id: u32, field_count: u32) -> CodegenResult<Value> {
        let type_id_val = self.iconst_cached(types::I32, type_id as i64);
        let field_count_val = self.iconst_cached(types::I32, field_count as i64);
        let runtime_type = self.iconst_cached(types::I32, RuntimeTypeId::Instance as i64);
        self.call_runtime(
            RuntimeKey::InstanceNew,
            &[type_id_val, field_count_val, runtime_type],
        )
    }

    /// Compile and store a single class field from a VIR expression.
    fn compile_class_field_vir(
        &mut self,
        name: Symbol,
        value_expr: &vole_vir::VirExpr,
        field_slots: &FxHashMap<String, usize>,
        field_types: &HashMap<String, (TypeId, VirTypeId)>,
        set_func_ref: FuncRef,
        instance_ptr: Value,
    ) -> CodegenResult<()> {
        let init_name = self.interner().resolve(name);
        let slot = *field_slots
            .get(init_name)
            .ok_or_else(|| CodegenError::not_found("field", format!("{init_name} in class")))?;
        let field_tys = field_types.get(init_name).copied();
        let mut value = if let Some((field_sema_ty, _)) = field_tys {
            self.compile_vir_expr_with_expected_type(value_expr, field_sema_ty)?
        } else {
            self.compile_vir_expr(value_expr)?
        };

        // RC: inc borrowed field values (skip unions -- handled by coercion).
        if self.rc_scopes.has_active_scope()
            && self.rc_state_v(value.type_id).needs_cleanup()
            && value.is_borrowed()
            && !self.vir_query_is_union_v(value.type_id)
        {
            self.emit_rc_inc_for_type_v(value.value, value.type_id)?;
        }
        value.mark_consumed();

        let final_value = if let Some((field_sema_ty, _field_vir_ty)) = field_tys {
            self.coerce_field_value(value, field_sema_ty)?
        } else {
            value
        };

        store_field_value(self, set_func_ref, instance_ptr, slot, &final_value);
        Ok(())
    }

    /// Compile default field values for a VIR class instance.
    fn compile_class_defaults(
        &mut self,
        type_def_id: vole_identity::TypeDefId,
        provided: &[(Symbol, vole_vir::VirRef)],
        field_slots: &FxHashMap<String, usize>,
        field_types: &HashMap<String, (TypeId, VirTypeId)>,
        set_func_ref: FuncRef,
        instance_ptr: Value,
    ) -> CodegenResult<()> {
        let provided_fields: HashSet<String> = provided
            .iter()
            .map(|(name, _)| self.interner().resolve(*name).to_string())
            .collect();
        let field_ids: Vec<_> = self.analyzed().fields_on_type(type_def_id).collect();
        for field_id in field_ids {
            let field = self.analyzed().field_def(field_id);
            let Some(field_name) = self.name_table().last_segment_str(field.name_id) else {
                continue;
            };
            if provided_fields.contains(&field_name) {
                continue;
            }
            let Some(default_expr) = self.field_default_vir_init(field_id).cloned() else {
                continue;
            };
            let slot = *field_slots.get(&field_name).ok_or_else(|| {
                CodegenError::not_found("field", format!("{field_name} in class"))
            })?;
            let field_tys = field_types.get(&field_name).copied();
            let value = if let Some((field_sema_ty, _)) = field_tys {
                self.compile_vir_expr_with_expected_type(&default_expr, field_sema_ty)?
            } else {
                self.compile_vir_expr(&default_expr)?
            };
            let final_value = if let Some((field_sema_ty, _)) = field_tys {
                self.coerce_field_value(value, field_sema_ty)?
            } else {
                value
            };
            store_field_value(self, set_func_ref, instance_ptr, slot, &final_value);
        }
        Ok(())
    }
}
