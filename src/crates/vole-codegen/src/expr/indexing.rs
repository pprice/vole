// src/codegen/expr/indexing.rs
//
// Index read and index assignment compilation.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, array_element_tag_id, field_byte_size, type_id_to_cranelift};

use vole_frontend::{Expr, ExprKind};
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;
use super::super::structs::{convert_to_i64_for_storage, reconstruct_i128, split_i128_for_storage};

impl Cg<'_, '_, '_> {
    /// Compile an index expression
    pub(super) fn index(
        &mut self,
        object: &Expr,
        index: &Expr,
        expr_id: vole_frontend::NodeId,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.expr(object)?;

        let arena = self.arena();

        // Try tuple first
        if let Some(elem_type_ids) = arena.unwrap_tuple(obj.type_id).cloned() {
            return self.index_tuple(obj, index, &elem_type_ids);
        }

        // Try fixed array
        if let Some((element_id, size)) = arena.unwrap_fixed_array(obj.type_id) {
            return self.index_fixed_array(obj, index, element_id, size);
        }

        // Try dynamic array
        if let Some(element_id) = arena.unwrap_array(obj.type_id) {
            return self.index_dynamic_array(obj, index, element_id, expr_id);
        }

        let type_name = self.arena().display_basic(obj.type_id);
        Err(CodegenError::type_mismatch(
            "index expression",
            "array or string",
            type_name,
        ))
    }

    /// Index into a tuple with a constant index.
    fn index_tuple(
        &mut self,
        obj: CompiledValue,
        index: &Expr,
        elem_type_ids: &[TypeId],
    ) -> CodegenResult<CompiledValue> {
        // Tuple indexing - must be constant index (checked in sema)
        if let ExprKind::IntLiteral(i, _) = &index.kind {
            let i = *i as usize;
            let (_, offsets) = self.tuple_layout(elem_type_ids);
            let offset = offsets[i];
            let elem_type_id = elem_type_ids[i];
            let elem_cr_type = type_id_to_cranelift(elem_type_id, self.arena(), self.ptr_type());

            let value = self
                .builder
                .ins()
                .load(elem_cr_type, MemFlags::new(), obj.value, offset);

            let mut cv = CompiledValue::new(value, elem_cr_type, elem_type_id);
            self.mark_borrowed_if_rc(&mut cv);
            Ok(cv)
        } else {
            Err(CodegenError::unsupported("non-constant tuple index"))
        }
    }

    /// Index into a fixed-size array.
    fn index_fixed_array(
        &mut self,
        obj: CompiledValue,
        index: &Expr,
        element_id: TypeId,
        size: usize,
    ) -> CodegenResult<CompiledValue> {
        let elem_size = field_byte_size(element_id, self.arena()) as i32;
        let elem_cr_type = type_id_to_cranelift(element_id, self.arena(), self.ptr_type());

        // Calculate offset: base + (index * elem_size)
        let offset = if let ExprKind::IntLiteral(i, _) = &index.kind {
            // Constant index - bounds check at compile time already done in sema
            let i = *i as usize;
            if i >= size {
                return Err(CodegenError::internal_with_context(
                    "array index out of bounds",
                    format!("index {} for array of size {}", i, size),
                ));
            }
            self.iconst_cached(types::I64, (i as i64) * (elem_size as i64))
        } else {
            // Runtime index - add bounds check
            let idx = self.expr(index)?;
            let size_val = self.iconst_cached(types::I64, size as i64);

            // Check if index < 0 or index >= size
            // We treat index as unsigned, so negative becomes very large
            let in_bounds = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, idx.value, size_val);

            // Trap if out of bounds
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

    /// Index into a dynamic array.
    fn index_dynamic_array(
        &mut self,
        obj: CompiledValue,
        index: &Expr,
        element_id: TypeId,
        expr_id: vole_frontend::NodeId,
    ) -> CodegenResult<CompiledValue> {
        let idx = self.expr(index)?;
        let raw_value = self.call_runtime(RuntimeKey::ArrayGetValue, &[obj.value, idx.value])?;
        let resolved_element_id = self.try_substitute_type(element_id);
        // Use sema's union storage annotation when available.
        if let Some(storage) = self.get_union_storage_kind(expr_id) {
            use vole_sema::UnionStorageKind;
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
        if let Some(wide) =
            crate::types::wide_ops::WideType::from_type_id(resolved_element_id, self.arena())
        {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_value])?;
            return Ok(wide.compiled_value_from_i128(self.builder, wide_bits, resolved_element_id));
        }
        let mut cv = self.convert_field_value(raw_value, resolved_element_id);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Assign a value to a fixed array element at the given index.
    /// Handles compile-time and runtime bounds checking, RC bookkeeping
    /// for element overwrite, and direct store at computed offset.
    fn index_assign_fixed_array(
        &mut self,
        arr_value: Value,
        index: &Expr,
        val: CompiledValue,
        elem_type_id: TypeId,
        size: usize,
    ) -> CodegenResult<CompiledValue> {
        let val = self.coerce_to_type(val, elem_type_id)?;
        let elem_size = field_byte_size(elem_type_id, self.arena()) as i32;

        // Calculate offset
        let offset = if let ExprKind::IntLiteral(i, _) = &index.kind {
            let i = *i as usize;
            if i >= size {
                return Err(CodegenError::internal_with_context(
                    "array index out of bounds",
                    format!("index {} for array of size {}", i, size),
                ));
            }
            self.iconst_cached(types::I64, (i as i64) * (elem_size as i64))
        } else {
            // Runtime index - add bounds check
            let idx = self.expr(index)?;
            let size_val = self.iconst_cached(types::I64, size as i64);

            // Check if index < 0 or index >= size
            let in_bounds = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, idx.value, size_val);

            // Trap if out of bounds
            self.builder
                .ins()
                .trapz(in_bounds, crate::trap_codes::BOUNDS_CHECK);

            let elem_size_val = self.iconst_cached(types::I64, elem_size as i64);
            self.builder.ins().imul(idx.value, elem_size_val)
        };

        let elem_ptr = self.builder.ins().iadd(arr_value, offset);

        // RC bookkeeping for fixed array element overwrite:
        // 1. Load old element value
        // 2. rc_inc new if it's a borrow
        // 3. Store new value
        // 4. rc_dec old (after store, in case old == new)
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

        // The assignment consumed the temp — ownership transfers
        // to the array element; the container's cleanup handles the dec.
        let mut val = val;
        val.mark_consumed();
        val.debug_assert_rc_handled("fixed array index assign");
        Ok(val)
    }

    pub(super) fn index_assign(
        &mut self,
        object: &Expr,
        index: &Expr,
        value: &Expr,
    ) -> CodegenResult<CompiledValue> {
        let arr = self.expr(object)?;
        let val = self.expr(value)?;

        let arena = self.arena();
        let fixed_array_info = arena.unwrap_fixed_array(arr.type_id);
        let is_dynamic_array = arena.is_array(arr.type_id);

        if let Some((elem_type_id, size)) = fixed_array_info {
            self.index_assign_fixed_array(arr.value, index, val, elem_type_id, size)
        } else if is_dynamic_array {
            self.index_assign_dynamic_array(arr, index, val)
        } else {
            // Error: not an indexable type
            let type_name = self.arena().display_basic(arr.type_id);
            Err(CodegenError::type_mismatch(
                "index assignment",
                "array",
                type_name,
            ))
        }
    }

    /// Assign a value to a dynamic array element at the given index.
    fn index_assign_dynamic_array(
        &mut self,
        arr: CompiledValue,
        index: &Expr,
        val: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let idx = self.expr(index)?;

        let elem_type = self.arena().unwrap_array(arr.type_id);
        let (tag_val, value_bits, val) = if let Some(elem_id) = elem_type {
            self.prepare_dynamic_array_store(val, elem_id)?
        } else {
            let val = if self.arena().is_struct(val.type_id) {
                self.copy_struct_to_heap(val)?
            } else {
                val
            };
            let tag = {
                let arena = self.arena();
                array_element_tag_id(val.type_id, arena)
            };
            let tag_val = self.iconst_cached(types::I64, tag);
            let value_bits = convert_to_i64_for_storage(self.builder, &val);
            (tag_val, value_bits, val)
        };

        // Container store: borrowed RC values need an extra ref so the array
        // owns its element independently of the source binding.
        self.rc_inc_borrowed_for_container(&val)?;

        let set_value_ref = self.runtime_func_ref(RuntimeKey::ArraySet)?;
        self.emit_call(set_value_ref, &[arr.value, idx.value, tag_val, value_bits]);

        // The assignment consumed the temp — ownership transfers
        // to the dynamic array element.
        let mut val = val;
        val.mark_consumed();
        val.debug_assert_rc_handled("dynamic array index assign");
        Ok(val)
    }
}
