// src/codegen/expr/indexing.rs
//
// Index read and index assignment compilation.
//
// Contains both legacy AST-based paths and VIR-based paths.
// The VIR methods (`compile_vir_index`, `compile_vir_index_store`)
// are called from `compile_vir_expr` in expr/mod.rs.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;

use vole_identity::{TypeId, UnionStorageKind, VirTypeId};
use vole_vir::VirExpr;

use super::super::context::Cg;
use super::super::structs::{reconstruct_i128, split_i128_for_storage};

impl Cg<'_, '_, '_> {
    // =========================================================================
    // VIR index codegen
    // =========================================================================

    /// Compile a VIR `Index` expression (index read).
    ///
    /// Dispatches on the object type: tuple, fixed array, or dynamic array.
    pub(crate) fn compile_vir_index(
        &mut self,
        object: &VirExpr,
        index: &VirExpr,
        vir_ty: VirTypeId,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.compile_vir_expr(object)?;

        if let Some(elem_type_ids) = self.vir_query_unwrap_tuple_v(obj.type_id) {
            return self.vir_index_tuple(obj, index, &elem_type_ids);
        }
        if let Some((element_id, size)) = self.vir_query_unwrap_fixed_array_v(obj.type_id) {
            return self.vir_index_fixed_array(obj, index, element_id, size);
        }
        if let Some(element_id) = self.vir_query_unwrap_array_v(obj.type_id) {
            return self.vir_index_dynamic_array(obj, index, element_id, vir_ty, union_storage);
        }

        // Codegen should not reach this — sema validates indexable types.
        let type_name = self.vir_query_display_basic_v(obj.type_id);
        Err(CodegenError::type_mismatch(
            "index expression",
            "array or tuple",
            type_name,
        ))
    }

    /// Compile a VIR `IndexStore` expression (index write).
    pub(crate) fn compile_vir_index_store(
        &mut self,
        object: &VirExpr,
        index: &VirExpr,
        value_expr: &VirExpr,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let arr = self.compile_vir_expr(object)?;
        let val = self.compile_vir_expr(value_expr)?;

        let fixed_array_info = self.vir_query_unwrap_fixed_array_v(arr.type_id);
        let is_dynamic_array = self.vir_query_is_array_v(arr.type_id);

        if let Some((elem_type_id, size)) = fixed_array_info {
            self.vir_index_assign_fixed_array(arr.value, index, val, elem_type_id, size)
        } else if is_dynamic_array {
            let idx = self.compile_vir_expr(index)?;
            self.index_assign_dynamic_array_inner(arr, idx, val, union_storage)
        } else {
            let type_name = self.vir_query_display_basic_v(arr.type_id);
            Err(CodegenError::type_mismatch(
                "index assignment",
                "array",
                type_name,
            ))
        }
    }

    /// Index a tuple via a VIR constant index.
    fn vir_index_tuple(
        &mut self,
        obj: CompiledValue,
        index: &VirExpr,
        elem_type_ids: &[VirTypeId],
    ) -> CodegenResult<CompiledValue> {
        if let VirExpr::IntLiteral { value, .. } = index {
            let i = *value as usize;
            let (_, offsets) = self.tuple_layout_v(elem_type_ids);
            let offset = offsets[i];
            let elem_vir_ty = elem_type_ids[i];
            let elem_cr_type = self.cranelift_type_v(elem_vir_ty);

            let value = self
                .builder
                .ins()
                .load(elem_cr_type, MemFlags::new(), obj.value, offset);

            let mut cv = CompiledValue::new(value, elem_cr_type, elem_vir_ty);
            self.mark_borrowed_if_rc(&mut cv);
            Ok(cv)
        } else {
            Err(CodegenError::unsupported("non-constant tuple index"))
        }
    }

    /// Index a fixed-size array via a VIR index expression.
    fn vir_index_fixed_array(
        &mut self,
        obj: CompiledValue,
        index: &VirExpr,
        element_id: VirTypeId,
        size: usize,
    ) -> CodegenResult<CompiledValue> {
        let elem_size = self.vir_query_field_byte_size_v(element_id) as i32;
        let elem_cr_type = self.cranelift_type_v(element_id);

        let offset = if let VirExpr::IntLiteral { value, .. } = index {
            let i = *value as usize;
            if i >= size {
                return Err(CodegenError::internal_with_context(
                    "array index out of bounds",
                    format!("index {} for array of size {}", i, size),
                ));
            }
            self.iconst_cached(types::I64, (i as i64) * (elem_size as i64))
        } else {
            let idx = self.compile_vir_expr(index)?;
            let size_val = self.iconst_cached(types::I64, size as i64);
            let in_bounds = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, idx.value, size_val);
            self.builder
                .ins()
                .trapz(in_bounds, crate::trap_codes::BOUNDS_CHECK);
            let elem_size_val = self.iconst_cached(types::I64, elem_size as i64);
            self.builder.ins().imul(idx.value, elem_size_val)
        };

        let elem_ptr = self.builder.ins().iadd(obj.value, offset);
        let value = if let Some(wide) =
            crate::types::wide_ops::WideType::from_cranelift_type(elem_cr_type)
        {
            let low = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), elem_ptr, 0);
            let high = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), elem_ptr, 8);
            let wide_i128 = reconstruct_i128(self.builder, low, high);
            wide.reinterpret_i128(self.builder, wide_i128)
        } else {
            self.builder
                .ins()
                .load(elem_cr_type, MemFlags::new(), elem_ptr, 0)
        };

        let mut cv = CompiledValue::new(value, elem_cr_type, element_id);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Index a dynamic array via a VIR index expression.
    fn vir_index_dynamic_array(
        &mut self,
        obj: CompiledValue,
        index: &VirExpr,
        element_id: VirTypeId,
        expected_element_vir: VirTypeId,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let idx = self.compile_vir_expr(index)?;
        let raw_value = self.call_runtime(RuntimeKey::ArrayGetValue, &[obj.value, idx.value])?;
        let expected_vir = self.try_substitute_type_v(expected_element_vir);
        let mut resolved_vir = self.try_substitute_type_v(element_id);
        let resolved_is_abstract = resolved_vir == VirTypeId::UNKNOWN
            || self.vir_query_contains_type_param_v(resolved_vir);
        if resolved_is_abstract && expected_vir != VirTypeId::UNKNOWN {
            resolved_vir = expected_vir;
        }

        if let Some(storage) = union_storage {
            let cv = match storage {
                UnionStorageKind::Inline => {
                    let raw_tag =
                        self.call_runtime(RuntimeKey::ArrayGetTag, &[obj.value, idx.value])?;
                    self.decode_dynamic_array_union_element_v(raw_tag, raw_value, resolved_vir)
                }
                UnionStorageKind::Heap => self.copy_union_heap_to_stack_v(raw_value, resolved_vir),
            };
            return Ok(cv);
        }
        if let Some(wide) = self.vir_query_wide_type_v(resolved_vir) {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_value])?;
            // TypeId parameter is unused by compiled_value_from_i128 — pass UNKNOWN.
            return Ok(wide.compiled_value_from_i128(self.builder, wide_bits, TypeId::UNKNOWN));
        }
        let mut cv = self.convert_field_value_v(raw_value, resolved_vir);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Assign a value to a fixed array element (VIR path).
    fn vir_index_assign_fixed_array(
        &mut self,
        arr_value: Value,
        index: &VirExpr,
        val: CompiledValue,
        elem_vir_ty: VirTypeId,
        size: usize,
    ) -> CodegenResult<CompiledValue> {
        let val = self.coerce_to_type(val, elem_vir_ty)?;
        let elem_size = self.vir_query_field_byte_size_v(elem_vir_ty) as i32;

        let offset = if let VirExpr::IntLiteral { value, .. } = index {
            let i = *value as usize;
            if i >= size {
                return Err(CodegenError::internal_with_context(
                    "array index out of bounds",
                    format!("index {} for array of size {}", i, size),
                ));
            }
            self.iconst_cached(types::I64, (i as i64) * (elem_size as i64))
        } else {
            let idx = self.compile_vir_expr(index)?;
            let size_val = self.iconst_cached(types::I64, size as i64);
            let in_bounds = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, idx.value, size_val);
            self.builder
                .ins()
                .trapz(in_bounds, crate::trap_codes::BOUNDS_CHECK);
            let elem_size_val = self.iconst_cached(types::I64, elem_size as i64);
            self.builder.ins().imul(idx.value, elem_size_val)
        };

        let elem_ptr = self.builder.ins().iadd(arr_value, offset);

        // RC bookkeeping for fixed array element overwrite
        let rc_old = if self.rc_scopes.has_active_scope()
            && self.cached_rc_state_v(elem_vir_ty).needs_cleanup()
        {
            Some(
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), elem_ptr, 0),
            )
        } else {
            None
        };
        if rc_old.is_some() && val.is_borrowed() {
            self.emit_rc_inc_for_type_v(val.value, elem_vir_ty)?;
        }
        if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(val.ty) {
            let i128_bits = wide.to_i128_bits(self.builder, val.value);
            let (low, high) = split_i128_for_storage(self.builder, i128_bits);
            self.builder.ins().store(MemFlags::new(), low, elem_ptr, 0);
            self.builder.ins().store(MemFlags::new(), high, elem_ptr, 8);
        } else {
            self.builder
                .ins()
                .store(MemFlags::new(), val.value, elem_ptr, 0);
        }
        if let Some(old_val) = rc_old {
            self.emit_rc_dec_for_type_v(old_val, elem_vir_ty)?;
        }

        let mut val = val;
        val.mark_consumed();
        val.debug_assert_rc_handled("fixed array index assign (VIR)");
        Ok(val)
    }

    /// Shared dynamic array assignment logic for both AST and VIR paths.
    fn index_assign_dynamic_array_inner(
        &mut self,
        arr: CompiledValue,
        idx: CompiledValue,
        val: CompiledValue,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let elem_vir_ty = self
            .vir_query_unwrap_array_v(arr.type_id)
            .expect("index assign target must have known array element type");
        let (tag_val, value_bits, val) =
            self.prepare_dynamic_array_store_with_hint_v(val, elem_vir_ty, union_storage)?;

        self.rc_inc_borrowed_for_container(&val)?;

        let set_value_ref = self.runtime_func_ref(RuntimeKey::ArraySet)?;
        self.emit_call(set_value_ref, &[arr.value, idx.value, tag_val, value_bits]);

        let mut val = val;
        val.mark_consumed();
        val.debug_assert_rc_handled("dynamic array index assign");
        Ok(val)
    }
}
