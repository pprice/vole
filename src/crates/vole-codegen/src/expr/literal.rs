// src/codegen/expr/literal.rs
//
// Array, tuple, repeat, and range literal compilation.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::CodegenResult;
use crate::types::{CompiledValue, array_element_tag_id, field_byte_size};

use vole_frontend::ast::RangeExpr;
use vole_frontend::{Expr, ExprKind};
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;
use super::super::structs::{convert_to_i64_for_storage, split_i128_for_storage};

impl Cg<'_, '_, '_> {
    /// Compile an array or tuple literal
    pub(super) fn array_literal(
        &mut self,
        elements: &[Expr],
        expr: &Expr,
    ) -> CodegenResult<CompiledValue> {
        self.array_literal_with_union_hint(elements, expr, None, None)
    }

    pub(crate) fn expr_with_expected_type(
        &mut self,
        expr: &Expr,
        expected_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let forced_union_elem = self
            .arena()
            .unwrap_array(expected_type_id)
            .filter(|&elem_type_id| self.arena().is_union(elem_type_id));
        let expected_array_type = self
            .arena()
            .unwrap_array(expected_type_id)
            .map(|_| expected_type_id);
        if let ExprKind::ArrayLiteral(elements) = &expr.kind {
            let compiled = self.array_literal_with_union_hint(
                elements,
                expr,
                forced_union_elem,
                expected_array_type,
            )?;
            Ok(self.mark_rc_owned(compiled))
        } else {
            self.expr(expr)
        }
    }

    pub(crate) fn array_literal_with_union_hint(
        &mut self,
        elements: &[Expr],
        expr: &Expr,
        forced_union_elem: Option<TypeId>,
        expected_array_type: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        // Check the inferred type from semantic analysis (module-aware)
        let inferred_type_id = self.get_expr_type(&expr.id);

        // If it's a tuple, use stack allocation
        if let Some(type_id) = inferred_type_id {
            let elem_type_ids = self.arena().unwrap_tuple(type_id).cloned();
            if let Some(elem_type_ids) = elem_type_ids {
                return self.tuple_literal(elements, &elem_type_ids, type_id);
            }
        }

        // Otherwise, create a dynamic array
        let arr_ptr = self.call_runtime(RuntimeKey::ArrayNew, &[])?;
        let array_push_ref = self.runtime_func_ref(RuntimeKey::ArrayPush)?;
        let inferred_elem_type =
            inferred_type_id.and_then(|array_type_id| self.arena().unwrap_array(array_type_id));
        let expected_elem_type_from_array =
            expected_array_type.and_then(|array_type_id| self.arena().unwrap_array(array_type_id));
        let expected_elem_type = forced_union_elem
            .or(inferred_elem_type)
            .or(expected_elem_type_from_array);

        for elem in elements {
            let compiled = if let Some(elem_type_id) = expected_elem_type {
                self.expr_with_expected_type(elem, elem_type_id)?
            } else {
                self.expr(elem)?
            };
            let (tag_val, value_bits, mut compiled) = if let Some(elem_type_id) = expected_elem_type
            {
                self.prepare_dynamic_array_store(compiled, elem_type_id)?
            } else {
                let compiled = if self.arena().is_struct(compiled.type_id) {
                    self.copy_struct_to_heap(compiled)?
                } else {
                    compiled
                };
                let tag = {
                    let arena = self.arena();
                    array_element_tag_id(compiled.type_id, arena)
                };
                let tag_val = self.iconst_cached(types::I64, tag);
                let value_bits = convert_to_i64_for_storage(self.builder, &compiled);
                (tag_val, value_bits, compiled)
            };

            // RC: inc borrowed RC elements so the array gets its own reference.
            self.rc_inc_borrowed_for_container(&compiled)?;

            let push_args = self.coerce_call_args(array_push_ref, &[arr_ptr, tag_val, value_bits]);
            self.builder.ins().call(array_push_ref, &push_args);

            // The element value is consumed into the array container.
            compiled.mark_consumed();
        }

        // Use type from ExpressionData - sema always records array/tuple types
        let array_type_id = inferred_type_id.or(expected_array_type).unwrap_or_else(|| {
            unreachable!(
                "array literal at line {} has no type from sema",
                expr.span.line
            )
        });
        Ok(CompiledValue::new(arr_ptr, self.ptr_type(), array_type_id))
    }

    /// Compile a tuple literal to stack-allocated memory
    fn tuple_literal(
        &mut self,
        elements: &[Expr],
        elem_type_ids: &[TypeId],
        tuple_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Calculate layout using TypeId-based function
        let (total_size, offsets) = self.tuple_layout(elem_type_ids);

        // Create stack slot for the tuple
        let slot = self.alloc_stack(total_size);

        // Compile and store each element
        for (i, elem) in elements.iter().enumerate() {
            let mut compiled = self.expr(elem)?;
            let offset = offsets[i];

            // RC: inc borrowed RC elements so the tuple gets its own reference.
            self.rc_inc_borrowed_for_container(&compiled)?;

            // Store the value at its offset in the tuple
            self.builder.ins().stack_store(compiled.value, slot, offset);
            // The element value is consumed into the tuple container.
            compiled.mark_consumed();
            compiled.debug_assert_rc_handled("tuple element");
        }

        // Return pointer to the tuple
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        // Use TypeId from ExpressionData (passed from caller)
        Ok(CompiledValue::new(ptr, ptr_type, tuple_type_id))
    }

    /// Compile a repeat literal [expr; N] to a fixed-size array
    pub(super) fn repeat_literal(
        &mut self,
        element: &Expr,
        count: usize,
        expr: &Expr,
    ) -> CodegenResult<CompiledValue> {
        // Resolve fixed-array element type from sema.
        let type_id = self.get_expr_type(&expr.id).unwrap_or_else(|| {
            unreachable!(
                "repeat literal at line {} has no type from sema",
                expr.span.line
            )
        });
        let (elem_type_id, _) = self.arena().unwrap_fixed_array(type_id).unwrap_or_else(|| {
            unreachable!(
                "repeat literal at line {} is missing fixed array type info",
                expr.span.line
            )
        });

        // Compile the element once.
        let mut elem_value = self.expr(element)?;

        // Fixed arrays use a per-element stride (8 bytes normally, 16 for i128/f128).
        let elem_size = field_byte_size(elem_type_id, self.arena());
        let total_size = elem_size * (count as u32);

        // Create stack slot for the fixed array
        let slot = self.alloc_stack(total_size);

        // Store the element value at each position.
        // For RC elements, each copy needs rc_inc since multiple slots share the
        // same pointer. When the element is borrowed (e.g. a variable reference),
        // ALL copies including the first need rc_inc because the source variable's
        // own cleanup will rc_dec independently of the array's composite cleanup.
        // When the element is owned (e.g. a fresh call result), the first copy
        // takes ownership (no inc) and subsequent copies need inc.
        let needs_rc =
            self.rc_scopes.has_active_scope() && self.rc_state(elem_value.type_id).needs_cleanup();
        let is_borrowed = elem_value.is_borrowed();
        let wide_bits = if elem_value.ty == types::I128 {
            Some(elem_value.value)
        } else if elem_value.ty == types::F128 {
            Some(
                self.builder
                    .ins()
                    .bitcast(types::I128, MemFlags::new(), elem_value.value),
            )
        } else {
            None
        };
        for i in 0..count {
            if needs_rc && (i > 0 || is_borrowed) {
                self.emit_rc_inc_for_type(elem_value.value, elem_value.type_id)?;
            }
            let offset = (i as i32) * (elem_size as i32);
            if let Some(wide_bits) = wide_bits {
                let (low, high) = split_i128_for_storage(self.builder, wide_bits);
                self.builder.ins().stack_store(low, slot, offset);
                self.builder.ins().stack_store(high, slot, offset + 8);
            } else {
                self.builder
                    .ins()
                    .stack_store(elem_value.value, slot, offset);
            }
        }
        // The element value is consumed into the repeat array container.
        elem_value.mark_consumed();
        elem_value.debug_assert_rc_handled("repeat array element");

        // Return pointer to the array
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue::new(ptr, ptr_type, type_id))
    }

    /// Compile a range expression (start..end or start..=end)
    /// Returns a pointer to a stack slot containing (start: i64, end: i64)
    /// For inclusive ranges, we store end + 1 so the iterator uses exclusive end
    pub(super) fn range(&mut self, range: &RangeExpr) -> CodegenResult<CompiledValue> {
        let start = self.expr(&range.start)?;
        let end_val = self.expr(&range.end)?;

        // For inclusive ranges (start..=end), add 1 to end so we can use exclusive end internally
        let end = if range.inclusive {
            self.builder.ins().iadd_imm(end_val.value, 1)
        } else {
            end_val.value
        };

        // Create a stack slot to hold (start, end) - 16 bytes
        let slot = self.alloc_stack(16);

        // Store start at offset 0
        self.builder.ins().stack_store(start.value, slot, 0);
        // Store end at offset 8
        self.builder.ins().stack_store(end, slot, 8);

        // Return pointer to the slot
        let ptr_type = self.ptr_type();
        let range_type_id = self.arena().range();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue::new(ptr, ptr_type, range_type_id))
    }
}
