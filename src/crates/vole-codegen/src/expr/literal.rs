// src/codegen/expr/literal.rs
//
// VIR array, tuple, repeat, and range literal compilation.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::CodegenResult;
use crate::types::CompiledValue;

use vole_identity::{ArrayStoreStrategy, VirTypeId};

use super::super::context::Cg;
use super::super::structs::split_i128_for_storage;

impl Cg<'_, '_, '_> {
    /// Compile a VIR range expression.
    ///
    /// Mirrors [`range()`] but compiles start/end from VIR expressions instead
    /// of AST nodes.
    pub(super) fn compile_vir_range(
        &mut self,
        start: &vole_vir::VirExpr,
        end: &vole_vir::VirExpr,
        inclusive: bool,
    ) -> CodegenResult<CompiledValue> {
        let start_val = self.compile_vir_expr(start)?;
        let end_val = self.compile_vir_expr(end)?;

        // For inclusive ranges (start..=end), add 1 to end
        let end = if inclusive {
            self.builder.ins().iadd_imm(end_val.value, 1)
        } else {
            end_val.value
        };

        // Create a stack slot to hold (start, end) - 16 bytes
        let slot = self.alloc_stack(16);

        self.builder.ins().stack_store(start_val.value, slot, 0);
        self.builder.ins().stack_store(end, slot, 8);

        let ptr_type = self.ptr_type();
        let range_type_id = self.vir_query_range();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(self.compiled_with_ty(ptr, ptr_type, range_type_id))
    }

    /// Compile a VIR array literal.
    ///
    /// Dispatches between tuple (stack) and dynamic array (heap) construction
    /// based on the sema-inferred type.  Mirrors the AST `array_literal_with_union_hint`
    /// but reads element VIR expressions instead of AST nodes.
    pub(crate) fn compile_vir_array_literal(
        &mut self,
        elements: &[vole_vir::VirRef],
        vir_array_type_id: VirTypeId,
        store_strategy: Option<ArrayStoreStrategy>,
    ) -> CodegenResult<CompiledValue> {
        // If sema inferred a tuple type, use stack allocation.
        if let Some(vir_elems) = self.vir_query_unwrap_tuple_v(vir_array_type_id) {
            return self.compile_vir_tuple_literal(elements, &vir_elems, vir_array_type_id);
        }

        // Dynamic array path.
        let arr_ptr = self.call_runtime(RuntimeKey::ArrayNew, &[])?;
        let array_push_ref = self.runtime_func_ref(RuntimeKey::ArrayPush)?;
        let elem_vir = self.vir_query_unwrap_array_v(vir_array_type_id);

        for elem_expr in elements {
            let compiled = if let Some(ev) = elem_vir {
                self.compile_vir_expr_with_expected_type_v(elem_expr, ev)?
            } else {
                self.compile_vir_expr(elem_expr)?
            };
            let (tag_val, value_bits, mut compiled) = if let Some(strategy) = store_strategy {
                let resolved =
                    elem_vir.unwrap_or_else(|| self.try_substitute_type_v(compiled.type_id));
                self.prepare_array_store_by_strategy(compiled, resolved, strategy)?
            } else if let Some(ev) = elem_vir {
                self.prepare_dynamic_array_store_with_hint_v(compiled, ev, None)?
            } else {
                // Element type unknown (e.g. empty array `[]`); derive strategy
                // from the compiled element's own type.
                self.prepare_dynamic_array_store_untyped(compiled)?
            };

            // RC: inc borrowed RC elements so the array gets its own reference.
            self.rc_inc_borrowed_for_container(&compiled)?;

            self.emit_call(array_push_ref, &[arr_ptr, tag_val, value_bits]);

            // The element value is consumed into the array container.
            compiled.mark_consumed();
        }

        let ptr_type = self.ptr_type();
        Ok(CompiledValue::new(arr_ptr, ptr_type, vir_array_type_id))
    }

    /// Compile a VIR repeat literal `[value; count]` to a fixed-size array.
    ///
    /// Mirrors [`repeat_literal()`] but compiles the element from a VIR
    /// expression instead of an AST node.
    pub(crate) fn compile_vir_repeat_literal(
        &mut self,
        element: &vole_vir::VirExpr,
        count: usize,
        vir_type_id: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let mut elem_value = self.compile_vir_expr(element)?;
        let (elem_vir, _len) = self
            .vir_query_unwrap_fixed_array_v(vir_type_id)
            .unwrap_or_else(|| {
                panic!(
                    "repeat literal VirTypeId {:?} is not a FixedArray — VIR metadata incomplete",
                    vir_type_id
                )
            });
        // result type is the same as the input fixed-array type

        let elem_size = self.vir_query_field_byte_size_v(elem_vir);
        let total_size = elem_size * (count as u32);

        let slot = self.alloc_stack(total_size);

        let needs_rc = self.rc_scopes.has_active_scope()
            && self.cached_rc_state_v(elem_value.type_id).needs_cleanup();
        let is_borrowed = elem_value.is_borrowed();
        let wide_bits = crate::types::wide_ops::WideType::from_cranelift_type(elem_value.ty)
            .map(|wide| wide.to_i128_bits(self.builder, elem_value.value));
        for i in 0..count {
            if needs_rc && (i > 0 || is_borrowed) {
                self.emit_rc_inc_for_type_v(elem_value.value, elem_value.type_id)?;
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
        elem_value.mark_consumed();
        elem_value.debug_assert_rc_handled("repeat array element");

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue::new(ptr, ptr_type, vir_type_id))
    }

    /// Compile a VIR tuple literal to stack-allocated memory.
    ///
    /// Mirrors `tuple_literal()` but compiles elements from VIR expressions.
    fn compile_vir_tuple_literal(
        &mut self,
        elements: &[vole_vir::VirRef],
        elem_vir_types: &[VirTypeId],
        tuple_vir_type: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let (total_size, offsets) = self.tuple_layout_v(elem_vir_types);
        let slot = self.alloc_stack(total_size);

        for (i, elem_expr) in elements.iter().enumerate() {
            let mut compiled = self.compile_vir_expr(elem_expr)?;
            let offset = offsets[i];

            // RC: inc borrowed RC elements so the tuple gets its own reference.
            self.rc_inc_borrowed_for_container(&compiled)?;

            self.builder.ins().stack_store(compiled.value, slot, offset);
            compiled.mark_consumed();
            compiled.debug_assert_rc_handled("tuple element");
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(CompiledValue::new(ptr, ptr_type, tuple_vir_type))
    }
}
