// src/codegen/expr/field_ops.rs
//
// VIR FieldLoad / FieldStore codegen.
//
// Compiles field access and field assignment for structs (stack-allocated,
// inline layout) and classes (heap-allocated, runtime instance API).
// Module field access (constants, exports) is also handled here when the
// object expression resolves to a module type.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::structs::helpers::{
    convert_to_i64_for_storage, get_field_slot_and_type_id_cg, store_field_value,
};
use crate::types::{CompiledValue, module_name_id};

use vole_frontend::Symbol;
use vole_identity::{ConstantValue, TypeId, VirTypeId};
use vole_vir::VirExpr;
use vole_vir::expr::FieldStorage;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile a VIR `FieldLoad` expression.
    ///
    /// When `storage` is resolved (`Direct` or `Heap`), uses the
    /// pre-resolved slot and dispatch kind from sema lowering.
    /// Falls back to the full arena lookup when `storage` is `ByName`
    /// (module fields).
    pub(crate) fn compile_vir_field_load(
        &mut self,
        object: &VirExpr,
        field: Symbol,
        storage: FieldStorage,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.compile_vir_expr(object)?;

        // Resolved storage: use pre-resolved slot, only look up field type.
        if let FieldStorage::Direct { slot } | FieldStorage::Heap { slot } = storage {
            let field_name = self.interner().resolve(field);
            let (_, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;
            return self.extract_field(obj, slot as usize, field_type_id);
        }

        // ByName fallback: module field access or full arena lookup.
        if let Some(cv) = self.try_module_field_load(obj, field)? {
            return Ok(cv);
        }
        let field_name = self.interner().resolve(field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;
        self.extract_field(obj, slot, field_type_id)
    }

    /// Compile a VIR `FieldStore` expression.
    ///
    /// When `storage` is resolved (`Direct` or `Heap`), uses the
    /// pre-resolved slot and dispatch kind from sema lowering.
    /// Falls back to the full arena lookup when `storage` is `ByName`.
    pub(crate) fn compile_vir_field_store(
        &mut self,
        object: &VirExpr,
        field: Symbol,
        storage: FieldStorage,
        value_expr: &VirExpr,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.compile_vir_expr(object)?;
        let value = self.compile_vir_expr(value_expr)?;

        match storage {
            FieldStorage::Direct { slot } => {
                let field_name = self.interner().resolve(field);
                let (_, field_type_id) =
                    get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;
                self.vir_struct_field_store(obj, slot as usize, field_type_id, value)
            }
            FieldStorage::Heap { slot } => {
                let field_name = self.interner().resolve(field);
                let (_, field_type_id) =
                    get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;
                self.vir_class_field_store(obj, slot as usize, field_type_id, value)
            }
            FieldStorage::ByName => {
                let field_name = self.interner().resolve(field);
                let (slot, field_type_id) =
                    get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;
                let is_struct = self.vir_query_is_struct(obj.type_id);
                if is_struct {
                    self.vir_struct_field_store(obj, slot, field_type_id, value)
                } else {
                    self.vir_class_field_store(obj, slot, field_type_id, value)
                }
            }
        }
    }

    /// Try to resolve a module field access.
    ///
    /// Returns `Some(value)` if the object is a module type and the field
    /// is a constant or sentinel export. Returns `None` if the object is
    /// not a module, allowing the caller to fall through to struct/class.
    fn try_module_field_load(
        &mut self,
        obj: CompiledValue,
        field: Symbol,
    ) -> CodegenResult<Option<CompiledValue>> {
        let Some((module_id, exports)) = self.vir_query_unwrap_module(obj.type_id) else {
            return Ok(None);
        };

        let field_name = self.interner().resolve(field);
        let module_path = self.name_table().module_path(module_id).to_string();
        let name_id = module_name_id(self.analyzed(), module_id, field_name);

        // Constant value lookup
        let const_val = name_id.and_then(|nid| self.vir_query_module_constant(module_id, nid));
        if let Some(const_val) = const_val {
            let cv = self.compile_constant_value(const_val)?;
            return Ok(Some(cv));
        }

        // Export check (function, sentinel, or unsupported)
        let export_type_id =
            name_id.and_then(|nid| exports.iter().find(|(n, _)| *n == nid).map(|(_, tid)| *tid));
        if let Some(export_type_id) = export_type_id {
            if self.vir_query_is_function(export_type_id) {
                return Err(CodegenError::unsupported_with_context(
                    "function as field value",
                    format!("use {}() to call the function", field_name),
                ));
            }
            if self.vir_query_is_sentinel(export_type_id) {
                let value = self.iconst_cached(types::I8, 0);
                return Ok(Some(CompiledValue::new(
                    value,
                    types::I8,
                    export_type_id,
                    self.vir_lookup(export_type_id),
                )));
            }
            return Err(CodegenError::unsupported_with_context(
                "non-constant module export",
                format!("{} cannot be accessed at compile time", field_name),
            ));
        }

        Err(CodegenError::not_found(
            "module export",
            format!("{}.{}", module_path, field_name),
        ))
    }

    /// Compile a `ConstantValue` to a `CompiledValue`.
    fn compile_constant_value(&mut self, const_val: ConstantValue) -> CodegenResult<CompiledValue> {
        let prims = self.vir_query_primitives();
        match const_val {
            ConstantValue::F64(v) => {
                let val = self.builder.ins().f64const(v);
                Ok(CompiledValue::new(
                    val,
                    types::F64,
                    prims.f64,
                    VirTypeId::F64,
                ))
            }
            ConstantValue::I64(v) => {
                let val = self.iconst_cached(types::I64, v);
                Ok(CompiledValue::new(
                    val,
                    types::I64,
                    prims.i64,
                    VirTypeId::I64,
                ))
            }
            ConstantValue::Bool(v) => {
                let val = self.iconst_cached(types::I8, if v { 1 } else { 0 });
                Ok(CompiledValue::new(
                    val,
                    types::I8,
                    prims.bool,
                    VirTypeId::BOOL,
                ))
            }
            ConstantValue::String(s) => self.string_literal(&s),
        }
    }

    /// Store a value into a struct field (stack-allocated, inline layout).
    ///
    /// Handles nested struct copy, union field assignment, wide types (i128),
    /// and RC bookkeeping for field overwrites.
    fn vir_struct_field_store(
        &mut self,
        obj: CompiledValue,
        slot: usize,
        field_type_id: TypeId,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let offset = self.struct_field_byte_offset(obj.type_id, slot);

        // Nested struct: copy all flat slots inline.
        if let Some(nested_flat) = self.struct_flat_slot_count(value.type_id) {
            for i in 0..nested_flat {
                let src_off = (i as i32) * 8;
                let dst_off = offset + src_off;
                let val =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, src_off);
                self.builder
                    .ins()
                    .store(MemFlags::new(), val, obj.value, dst_off);
            }
        } else if self.vir_query_is_payload_union(field_type_id) {
            self.assign_struct_union_field(obj.value, offset, value, field_type_id)?;
        } else {
            self.vir_struct_scalar_store(obj.value, offset, field_type_id, &value)?;
        }

        let mut value = value;
        value.mark_consumed();
        value.debug_assert_rc_handled("struct field assign (stack)");
        Ok(value)
    }

    /// Store a scalar value into a struct field with RC bookkeeping.
    fn vir_struct_scalar_store(
        &mut self,
        struct_ptr: Value,
        offset: i32,
        field_type_id: TypeId,
        value: &CompiledValue,
    ) -> CodegenResult<()> {
        // RC bookkeeping: load old, inc new if borrowed, store, dec old.
        let rc_old =
            if self.rc_scopes.has_active_scope() && self.rc_state(field_type_id).needs_cleanup() {
                Some(
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), struct_ptr, offset),
                )
            } else {
                None
            };
        if rc_old.is_some() && value.is_borrowed() {
            self.emit_rc_inc_for_type(value.value, field_type_id)?;
        }
        if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
            let i128_bits = wide.to_i128_bits(self.builder, value.value);
            let (low, high) =
                crate::structs::helpers::split_i128_for_storage(self.builder, i128_bits);
            self.builder
                .ins()
                .store(MemFlags::new(), low, struct_ptr, offset);
            self.builder
                .ins()
                .store(MemFlags::new(), high, struct_ptr, offset + 8);
        } else {
            let store_value = convert_to_i64_for_storage(self.builder, value);
            self.builder
                .ins()
                .store(MemFlags::new(), store_value, struct_ptr, offset);
        }
        if let Some(old_val) = rc_old {
            self.emit_rc_dec_for_type(old_val, field_type_id)?;
        }
        Ok(())
    }

    /// Store a value into a class instance field (heap-allocated).
    ///
    /// Handles unknown boxing, interface boxing, RC bookkeeping for
    /// field overwrites, and wide type storage.
    fn vir_class_field_store(
        &mut self,
        obj: CompiledValue,
        slot: usize,
        field_type_id: TypeId,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        // Box/coerce value if field type requires it.
        let value = self.coerce_value_for_field(value, field_type_id)?;

        // RC bookkeeping: load old field, inc new if borrowed, store, dec old.
        let (old_field, needs_rc, needs_unknown) =
            self.load_old_field_for_cleanup(obj.value, slot, field_type_id)?;

        if needs_rc && old_field.is_some() && value.is_borrowed() {
            self.emit_rc_inc_for_type(value.value, field_type_id)?;
        }

        // Store field value (handles wide types via 2-slot storage).
        let set_func_ref = self.runtime_func_ref(RuntimeKey::InstanceSetField)?;
        store_field_value(self, set_func_ref, obj.value, slot, &value);

        // Clean up old value.
        if let Some(old_val) = old_field {
            if needs_unknown {
                self.call_runtime_void(RuntimeKey::UnknownHeapCleanup, &[old_val])?;
            } else {
                self.emit_rc_dec_for_type(old_val, field_type_id)?;
            }
        }

        let mut value = value;
        value.mark_consumed();
        value.debug_assert_rc_handled("instance field assign");
        Ok(value)
    }

    /// Coerce a value for assignment to a field, handling unknown boxing,
    /// unknown-to-unknown heap copy, and interface boxing.
    fn coerce_value_for_field(
        &mut self,
        value: CompiledValue,
        field_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        if field_type_id.is_unknown() && !value.type_id.is_unknown() {
            self.box_to_unknown(value)
        } else if field_type_id.is_unknown() && value.type_id.is_unknown() {
            self.copy_tagged_value_to_heap(value)
        } else if self.vir_query_is_interface(field_type_id) {
            self.box_interface_value(value, field_type_id)
        } else {
            Ok(value)
        }
    }

    /// Load the old field value for RC cleanup before a store.
    ///
    /// Returns `(old_value, needs_rc_cleanup, needs_unknown_cleanup)`.
    fn load_old_field_for_cleanup(
        &mut self,
        instance_ptr: Value,
        slot: usize,
        field_type_id: TypeId,
    ) -> CodegenResult<(Option<Value>, bool, bool)> {
        let field_is_unknown = field_type_id.is_unknown();
        let needs_rc =
            self.rc_scopes.has_active_scope() && self.rc_state(field_type_id).needs_cleanup();
        let needs_unknown = self.rc_scopes.has_active_scope() && field_is_unknown;

        let old_field = if needs_rc || needs_unknown {
            let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
            let slot_val = self.iconst_cached(types::I32, slot as i64);
            let call = self
                .builder
                .ins()
                .call(get_func_ref, &[instance_ptr, slot_val]);
            Some(self.builder.inst_results(call)[0])
        } else {
            None
        };

        Ok((old_field, needs_rc, needs_unknown))
    }
}
