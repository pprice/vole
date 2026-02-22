// src/codegen/structs/builtin_methods.rs
//
// Built-in methods on arrays, strings, and ranges (length, iter, push).

use cranelift::prelude::*;

use super::helpers::convert_to_i64_for_storage;
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, array_element_tag_id};
use vole_frontend::MethodCallExpr;
use vole_sema::type_arena::TypeId;

impl Cg<'_, '_, '_> {
    /// Compile range.iter() - creates a range iterator from start..end
    /// `iter_type_hint` is the pre-computed RuntimeIterator type from sema's concrete_return_hint.
    pub(super) fn range_iter(
        &mut self,
        range: &vole_frontend::ast::RangeExpr,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        // Compile start and end expressions
        let start = self.expr(&range.start)?;
        let end_val = self.expr(&range.end)?;

        // For inclusive ranges, add 1 to the end (since our iterator is exclusive-end)
        let end_value = if range.inclusive {
            self.builder.ins().iadd_imm(end_val.value, 1)
        } else {
            end_val.value
        };

        // Call vole_range_iter(start, end) -> RuntimeIterator<i64>
        let result = self.call_runtime(RuntimeKey::RangeIter, &[start.value, end_value])?;

        // Use sema's pre-computed RuntimeIterator type, or look it up from the
        // element type (needed for monomorphized generic functions where sema
        // resolution is skipped).
        let iter_type_id = iter_type_hint.unwrap_or_else(|| {
            self.arena()
                .lookup_runtime_iterator(TypeId::I64)
                .expect("INTERNAL: range iterator: RuntimeIterator<i64> type not pre-created")
        });
        Ok(CompiledValue::owned(result, self.ptr_type(), iter_type_id))
    }

    /// Handle built-in methods on arrays, strings, and ranges.
    /// `iter_type_hint` is the pre-computed RuntimeIterator type from sema's concrete_return_hint.
    pub(crate) fn builtin_method(
        &mut self,
        obj: &CompiledValue,
        method_name: &str,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<Option<CompiledValue>> {
        let arena = self.arena();

        // Array methods
        if let Some(elem_type_id) = arena.unwrap_array(obj.type_id) {
            return match method_name {
                "length" => {
                    let result = self.call_compiler_intrinsic_key_with_line(
                        crate::IntrinsicKey::ArrayLen,
                        &[obj.value],
                        TypeId::I64,
                        0,
                    )?;
                    Ok(Some(result))
                }
                "iter" => {
                    let result = self.call_runtime(RuntimeKey::ArrayIter, &[obj.value])?;
                    // Use sema's pre-computed RuntimeIterator type, or look it up from
                    // the element type (needed for monomorphized generic functions where
                    // sema resolution is skipped).
                    let iter_type_id = iter_type_hint.unwrap_or_else(|| {
                        self.arena().lookup_runtime_iterator(elem_type_id).expect(
                            "INTERNAL: array iterator: RuntimeIterator type not pre-created",
                        )
                    });
                    // Set elem_tag on the array iterator so pipeline operations
                    // can properly manage RC values
                    let tag = crate::types::unknown_type_tag(elem_type_id, self.arena());
                    if tag != 0 {
                        let tag_val = self.iconst_cached(types::I64, tag as i64);
                        self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
                    }
                    Ok(Some(CompiledValue::owned(
                        result,
                        self.ptr_type(),
                        iter_type_id,
                    )))
                }
                _ => Ok(None),
            };
        }

        // String methods
        if arena.is_string(obj.type_id) {
            return match method_name {
                "length" => {
                    let result = self.call_compiler_intrinsic_key_with_line(
                        crate::IntrinsicKey::StringLen,
                        &[obj.value],
                        TypeId::I64,
                        0,
                    )?;
                    Ok(Some(result))
                }
                "iter" => {
                    let result = self.call_runtime(RuntimeKey::StringCharsIter, &[obj.value])?;
                    // Use sema's pre-computed RuntimeIterator type, or look it up
                    // (needed for monomorphized generic functions where sema
                    // resolution is skipped).
                    let iter_type_id = iter_type_hint.unwrap_or_else(|| {
                        self.arena()
                            .lookup_runtime_iterator(TypeId::STRING)
                            .expect(
                                "INTERNAL: string iterator: RuntimeIterator<string> type not pre-created",
                            )
                    });
                    // Set elem_tag to RuntimeTypeId::String so terminal methods can properly
                    // free owned char strings produced by the string chars iterator.
                    let string_tag = crate::types::unknown_type_tag(TypeId::STRING, self.arena());
                    if string_tag != 0 {
                        let tag_val = self.iconst_cached(types::I64, string_tag as i64);
                        self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
                    }
                    Ok(Some(CompiledValue::owned(
                        result,
                        self.ptr_type(),
                        iter_type_id,
                    )))
                }
                _ => Ok(None),
            };
        }

        // Range methods
        if matches!(
            arena.get(obj.type_id),
            vole_sema::type_arena::SemaType::Range
        ) {
            if method_name == "iter" {
                // Load start and end from the range struct (pointer to [start, end])
                let start = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), obj.value, 0);
                let end = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), obj.value, 8);
                let result = self.call_runtime(RuntimeKey::RangeIter, &[start, end])?;
                // Use sema's pre-computed RuntimeIterator type, or look it up from
                // the element type (needed for monomorphized generic functions where
                // sema resolution is skipped).
                let iter_type_id = iter_type_hint.unwrap_or_else(|| {
                    self.arena()
                        .lookup_runtime_iterator(TypeId::I64)
                        .expect("INTERNAL: range.iter(): RuntimeIterator<i64> type not pre-created")
                });
                return Ok(Some(CompiledValue::owned(
                    result,
                    self.ptr_type(),
                    iter_type_id,
                )));
            }
            return Ok(None);
        }

        Ok(None)
    }

    /// Handle array.push(value) - appends value to end of array
    pub(super) fn array_push_call(
        &mut self,
        arr_obj: &CompiledValue,
        mc: &MethodCallExpr,
    ) -> CodegenResult<CompiledValue> {
        // We expect exactly one argument
        if mc.args.len() != 1 {
            return Err(CodegenError::arg_count("array.push", 1, mc.args.len()));
        }

        // Compile the argument
        let value = self.expr(mc.args[0].expr())?;

        let elem_type = self.arena().unwrap_array(arr_obj.type_id);
        let (tag_val, value_bits, _value) = if let Some(elem_id) = elem_type {
            self.prepare_dynamic_array_store(value, elem_id)?
        } else {
            let value = if self.arena().is_struct(value.type_id) {
                self.copy_struct_to_heap(value)?
            } else {
                value
            };
            let tag = {
                let arena = self.arena();
                array_element_tag_id(value.type_id, arena)
            };
            let tag_val = self.iconst_cached(types::I64, tag);
            let value_bits = convert_to_i64_for_storage(self.builder, &value);
            (tag_val, value_bits, value)
        };

        // Get the runtime function reference
        let push_ref = self.runtime_func_ref(RuntimeKey::ArrayPush)?;

        // Call vole_array_push(arr_ptr, tag, value)
        self.emit_call(push_ref, &[arr_obj.value, tag_val, value_bits]);

        // Return void
        let void_type_id = self.arena().void();
        Ok(CompiledValue::new(
            self.iconst_cached(types::I64, 0),
            types::I64,
            void_type_id,
        ))
    }
}
