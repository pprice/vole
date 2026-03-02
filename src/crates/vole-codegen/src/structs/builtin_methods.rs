// src/codegen/structs/builtin_methods.rs
//
// Built-in methods on arrays, strings, and ranges (length, iter, push).

use cranelift::prelude::*;

use super::methods::ArgSource;
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use vole_identity::{TypeId, VirTypeId};

impl Cg<'_, '_, '_> {
    /// VIR path for range.iter() - compiles start/end from VIR expressions.
    /// Mirrors [`range_iter()`] but works from VIR `VirExpr` nodes instead of AST.
    pub(super) fn vir_range_iter(
        &mut self,
        start: &vole_vir::VirExpr,
        end: &vole_vir::VirExpr,
        inclusive: bool,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let start_val = self.compile_vir_expr(start)?;
        let end_val = self.compile_vir_expr(end)?;

        let end_value = if inclusive {
            self.builder.ins().iadd_imm(end_val.value, 1)
        } else {
            end_val.value
        };

        let result = self.call_runtime(RuntimeKey::RangeIter, &[start_val.value, end_value])?;

        let iter_type_id = iter_type_hint.unwrap_or_else(|| {
            self.vir_query_lookup_runtime_iterator(TypeId::I64)
                .expect("INTERNAL: range iterator: RuntimeIterator<i64> type not pre-created")
        });
        Ok(CompiledValue::owned(
            result,
            self.ptr_type(),
            self.vir_lookup(iter_type_id),
        ))
    }

    /// Handle built-in methods on arrays, strings, and ranges.
    /// `iter_type_hint` is the pre-computed RuntimeIterator type from sema's concrete_return_hint.
    pub(crate) fn builtin_method(
        &mut self,
        obj: &CompiledValue,
        method_name: &str,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<Option<CompiledValue>> {
        // Array methods
        if let Some(elem_vir_type_id) = self.vir_query_unwrap_array_v(obj.type_id) {
            let elem_type_id = self.cv_type_id_from_vir(elem_vir_type_id);
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
                        self.vir_query_lookup_runtime_iterator(elem_type_id).expect(
                            "INTERNAL: array iterator: RuntimeIterator type not pre-created",
                        )
                    });
                    // Set elem_tag on the array iterator so pipeline operations
                    // can properly manage RC values
                    let tag = self.vir_query_unknown_type_tag(elem_type_id);
                    if tag != 0 {
                        let tag_val = self.iconst_cached(types::I64, tag as i64);
                        self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
                    }
                    Ok(Some(CompiledValue::owned(
                        result,
                        self.ptr_type(),
                        self.vir_lookup(iter_type_id),
                    )))
                }
                _ => Ok(None),
            };
        }

        // String methods
        if self.vir_query_is_string_v(obj.type_id) {
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
                        self.vir_query_lookup_runtime_iterator(TypeId::STRING)
                            .expect(
                                "INTERNAL: string iterator: RuntimeIterator<string> type not pre-created",
                            )
                    });
                    // Set elem_tag to RuntimeTypeId::String so terminal methods can properly
                    // free owned char strings produced by the string chars iterator.
                    let string_tag = self.vir_query_unknown_type_tag(TypeId::STRING);
                    if string_tag != 0 {
                        let tag_val = self.iconst_cached(types::I64, string_tag as i64);
                        self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
                    }
                    Ok(Some(CompiledValue::owned(
                        result,
                        self.ptr_type(),
                        self.vir_lookup(iter_type_id),
                    )))
                }
                _ => Ok(None),
            };
        }

        // Range methods
        if obj.type_id == VirTypeId::RANGE {
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
                    self.vir_query_lookup_runtime_iterator(TypeId::I64)
                        .expect("INTERNAL: range.iter(): RuntimeIterator<i64> type not pre-created")
                });
                return Ok(Some(CompiledValue::owned(
                    result,
                    self.ptr_type(),
                    self.vir_lookup(iter_type_id),
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
        arg_source: &ArgSource<'_>,
    ) -> CodegenResult<CompiledValue> {
        let arg_count = arg_source.len();
        // We expect exactly one argument
        if arg_count != 1 {
            return Err(CodegenError::arg_count("array.push", 1, arg_count));
        }

        // Compile the argument
        let value = self.compile_arg_from_source(arg_source, 0)?;

        let elem_type = self
            .vir_query_unwrap_array_v(arr_obj.type_id)
            .map(|v| self.cv_type_id_from_vir(v));
        let (tag_val, value_bits, _value) = if let Some(elem_id) = elem_type {
            self.prepare_dynamic_array_store(value, elem_id)?
        } else {
            self.prepare_dynamic_array_store_untyped(value)?
        };

        // Get the runtime function reference
        let push_ref = self.runtime_func_ref(RuntimeKey::ArrayPush)?;

        // Call vole_array_push(arr_ptr, tag, value)
        self.emit_call(push_ref, &[arr_obj.value, tag_val, value_bits]);

        // Return void
        let void_type_id = self.vir_query_void();
        Ok(CompiledValue::new(
            self.iconst_cached(types::I64, 0),
            types::I64,
            self.vir_lookup(void_type_id),
        ))
    }
}
