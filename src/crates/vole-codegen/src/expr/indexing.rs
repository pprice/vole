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

use vole_identity::{TypeId, UnionStorageKind};
use vole_vir::VirExpr;
use vole_vir::types::VirType;

use super::super::context::Cg;
use super::super::structs::{reconstruct_i128, split_i128_for_storage};

type VirIndexDispatch = (Option<Vec<TypeId>>, Option<(TypeId, usize)>, Option<TypeId>);

impl Cg<'_, '_, '_> {
    /// Recover index dispatch information from VIR type metadata.
    ///
    /// TEMP(N279-C): bridge for cases where sema `TypeId` degrades to
    /// `TypeId::UNKNOWN` during migration.
    fn vir_index_dispatch(&self, object: &VirExpr) -> Option<VirIndexDispatch> {
        let vir_ty = Self::vir_expr_type_id(object)?;
        match self.vir_type_table().get(vir_ty) {
            VirType::Tuple { elems } => Some((
                Some(elems.iter().map(|&t| self.sema_type_from_vir(t)).collect()),
                None,
                None,
            )),
            VirType::FixedArray { elem, len } => Some((
                None,
                Some((self.sema_type_from_vir(*elem), *len as usize)),
                None,
            )),
            VirType::Array { elem } => Some((None, None, Some(self.sema_type_from_vir(*elem)))),
            _ => None,
        }
    }

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
        ty: TypeId,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.compile_vir_expr(object)?;

        if let Some(elem_type_ids) = self.vir_query_unwrap_tuple(self.cv_type_id(&obj)) {
            return self.vir_index_tuple(obj, index, &elem_type_ids);
        }
        if let Some((element_id, size)) = self.vir_query_unwrap_fixed_array(self.cv_type_id(&obj)) {
            return self.vir_index_fixed_array(obj, index, element_id, size);
        }
        if let Some(element_id) = self.vir_query_unwrap_array(self.cv_type_id(&obj)) {
            return self.vir_index_dynamic_array(obj, index, element_id, ty, union_storage);
        }
        if let Some((tuple_elems, fixed_array, dyn_array)) = self.vir_index_dispatch(object) {
            if let Some(elem_type_ids) = tuple_elems {
                return self.vir_index_tuple(obj, index, &elem_type_ids);
            }
            if let Some((element_id, size)) = fixed_array {
                return self.vir_index_fixed_array(obj, index, element_id, size);
            }
            if let Some(element_id) = dyn_array {
                return self.vir_index_dynamic_array(obj, index, element_id, ty, union_storage);
            }
        }

        // Codegen should not reach this — sema validates indexable types.
        let type_name = self.vir_query_display_basic(self.cv_type_id(&obj));
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
        _union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let arr = self.compile_vir_expr(object)?;
        let val = self.compile_vir_expr(value_expr)?;

        let fixed_array_info = self.vir_query_unwrap_fixed_array(self.cv_type_id(&arr));
        let is_dynamic_array = self.vir_query_is_array(self.cv_type_id(&arr));

        if let Some((elem_type_id, size)) = fixed_array_info {
            self.vir_index_assign_fixed_array(arr.value, index, val, elem_type_id, size)
        } else if is_dynamic_array {
            let idx = self.compile_vir_expr(index)?;
            self.index_assign_dynamic_array_inner(arr, idx, val)
        } else if let Some((_, fixed_array, dyn_array)) = self.vir_index_dispatch(object) {
            if let Some((elem_type_id, size)) = fixed_array {
                self.vir_index_assign_fixed_array(arr.value, index, val, elem_type_id, size)
            } else if dyn_array.is_some() {
                let idx = self.compile_vir_expr(index)?;
                self.index_assign_dynamic_array_inner(arr, idx, val)
            } else {
                let type_name = self.vir_query_display_basic(self.cv_type_id(&arr));
                Err(CodegenError::type_mismatch(
                    "index assignment",
                    "array",
                    type_name,
                ))
            }
        } else {
            let type_name = self.vir_query_display_basic(self.cv_type_id(&arr));
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
        elem_type_ids: &[TypeId],
    ) -> CodegenResult<CompiledValue> {
        if let VirExpr::IntLiteral { value, .. } = index {
            let i = *value as usize;
            let (_, offsets) = self.tuple_layout(elem_type_ids);
            let offset = offsets[i];
            let elem_type_id = elem_type_ids[i];
            let elem_cr_type = self.cranelift_type(elem_type_id);

            let value = self
                .builder
                .ins()
                .load(elem_cr_type, MemFlags::new(), obj.value, offset);

            let mut cv = CompiledValue::new(value, elem_cr_type, self.vir_lookup(elem_type_id));
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
        element_id: TypeId,
        size: usize,
    ) -> CodegenResult<CompiledValue> {
        let elem_size = self.vir_query_field_byte_size(element_id) as i32;
        let elem_cr_type = self.cranelift_type(element_id);

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

        let mut cv = CompiledValue::new(value, elem_cr_type, self.vir_lookup(element_id));
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Index a dynamic array via a VIR index expression.
    fn vir_index_dynamic_array(
        &mut self,
        obj: CompiledValue,
        index: &VirExpr,
        element_id: TypeId,
        expected_element_id: TypeId,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<CompiledValue> {
        let idx = self.compile_vir_expr(index)?;
        let raw_value = self.call_runtime(RuntimeKey::ArrayGetValue, &[obj.value, idx.value])?;
        let expected_element_id = self.try_substitute_type(expected_element_id);
        let mut resolved_element_id = self.try_substitute_type(element_id);
        let resolved_is_abstract = resolved_element_id == TypeId::UNKNOWN
            || self.vir_query_contains_type_param(resolved_element_id)
            || self.vir_query_is_self_type(resolved_element_id);
        if resolved_is_abstract && expected_element_id != TypeId::UNKNOWN {
            resolved_element_id = expected_element_id;
        }

        if let Some(storage) = union_storage {
            let cv = match storage {
                UnionStorageKind::Inline => {
                    let raw_tag =
                        self.call_runtime(RuntimeKey::ArrayGetTag, &[obj.value, idx.value])?;
                    self.decode_dynamic_array_union_element(raw_tag, raw_value, resolved_element_id)
                }
                UnionStorageKind::Heap => {
                    self.copy_union_heap_to_stack(raw_value, resolved_element_id)
                }
            };
            return Ok(cv);
        }
        if let Some(wide) = self.vir_query_wide_type(resolved_element_id) {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_value])?;
            return Ok(wide.compiled_value_from_i128(self.builder, wide_bits, resolved_element_id));
        }
        let mut cv = self.convert_field_value(raw_value, resolved_element_id);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Assign a value to a fixed array element (VIR path).
    fn vir_index_assign_fixed_array(
        &mut self,
        arr_value: Value,
        index: &VirExpr,
        val: CompiledValue,
        elem_type_id: TypeId,
        size: usize,
    ) -> CodegenResult<CompiledValue> {
        let val = self.coerce_to_type(val, elem_type_id)?;
        let elem_size = self.vir_query_field_byte_size(elem_type_id) as i32;

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
        let rc_old =
            if self.rc_scopes.has_active_scope() && self.rc_state(elem_type_id).needs_cleanup() {
                Some(
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), elem_ptr, 0),
                )
            } else {
                None
            };
        if rc_old.is_some() && val.is_borrowed() {
            self.emit_rc_inc_for_type(val.value, elem_type_id)?;
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
            self.emit_rc_dec_for_type(old_val, elem_type_id)?;
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
    ) -> CodegenResult<CompiledValue> {
        let elem_type = self.vir_query_unwrap_array(self.cv_type_id(&arr));
        let (tag_val, value_bits, val) = if let Some(elem_id) = elem_type {
            self.prepare_dynamic_array_store(val, elem_id)?
        } else {
            self.prepare_dynamic_array_store_untyped(val)?
        };

        self.rc_inc_borrowed_for_container(&val)?;

        let set_value_ref = self.runtime_func_ref(RuntimeKey::ArraySet)?;
        self.emit_call(set_value_ref, &[arr.value, idx.value, tag_val, value_bits]);

        let mut val = val;
        val.mark_consumed();
        val.debug_assert_rc_handled("dynamic array index assign");
        Ok(val)
    }
}
