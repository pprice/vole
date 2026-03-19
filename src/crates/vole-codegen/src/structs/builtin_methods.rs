// src/codegen/structs/builtin_methods.rs
//
// Built-in methods on arrays, strings, and ranges (length, iter, push).

use cranelift::prelude::*;

use super::methods::ArgSource;
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use vole_identity::TypeId;
use vole_vir::BuiltinMethod;

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
            self.vir_query_lookup_iterator_interface(TypeId::I64)
                .expect("INTERNAL: range iterator: Iterator<i64> type not pre-created")
        });
        Ok(self.compiled_owned_with_ty(result, self.ptr_type(), iter_type_id))
    }

    /// Handle built-in methods on arrays, strings, and ranges.
    ///
    /// Dispatches on the pre-resolved `BuiltinMethod` enum from VIR — no
    /// receiver-type re-detection needed.
    /// `iter_type_hint` is the pre-computed Iterator<T> type from sema's concrete_return_hint.
    pub(crate) fn builtin_method(
        &mut self,
        builtin: BuiltinMethod,
        obj: &CompiledValue,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        match builtin {
            BuiltinMethod::ArrayLength => self.array_length(obj),
            BuiltinMethod::ArrayIter => self.array_iter(obj, iter_type_hint),
            BuiltinMethod::ArrayPush => {
                // ArrayPush is handled via VirMethodDispatchKind::ArrayPush, not here.
                Err(CodegenError::internal(
                    "ArrayPush should be dispatched via VirMethodDispatchKind::ArrayPush",
                ))
            }
            BuiltinMethod::StringLength => self.string_length(obj),
            BuiltinMethod::StringIter => self.string_iter(obj, iter_type_hint),
            BuiltinMethod::RangeIter => self.range_iter_from_obj(obj, iter_type_hint),
            other => Err(CodegenError::internal_with_context(
                "unexpected BuiltinMethod in builtin_method dispatch",
                format!("{other:?}"),
            )),
        }
    }

    fn array_length(&mut self, obj: &CompiledValue) -> CodegenResult<CompiledValue> {
        self.call_compiler_intrinsic_key_with_line(
            crate::IntrinsicKey::ArrayLen,
            &[obj.value],
            TypeId::I64,
            0,
        )
    }

    fn array_iter(
        &mut self,
        obj: &CompiledValue,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let elem_vir_type_id = self
            .vir_query_unwrap_array_v(obj.type_id)
            .ok_or_else(|| CodegenError::internal("ArrayIter on non-array type"))?;
        let result = self.call_runtime(RuntimeKey::ArrayIter, &[obj.value])?;

        // When iter_type_hint is unavailable, derive the Iterator<T> type.
        // Try sema-level lookup first, then VIR-level lookup.
        // If the VIR-level lookup succeeds but lacks a sema reverse mapping
        // (common for types created by register_implement_method_monomorphs
        // after the VIR sweep), return the CompiledValue with the VirTypeId
        // directly to preserve correct dispatch.
        if let Some(hint) = iter_type_hint {
            let tag = self.vir_query_unknown_type_tag_v(elem_vir_type_id);
            if tag != 0 {
                let tag_val = self.iconst_cached(types::I64, tag as i64);
                self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
            }
            return Ok(self.compiled_owned_with_ty(result, self.ptr_type(), hint));
        }

        let tag = self.vir_query_unknown_type_tag_v(elem_vir_type_id);
        if tag != 0 {
            let tag_val = self.iconst_cached(types::I64, tag as i64);
            self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
        }

        let table = self.vir_type_table();
        let elem_sema = table.vir_to_type_id(elem_vir_type_id);
        let iter_type_id = self
            .vir_query_lookup_iterator_interface(elem_sema)
            .or_else(|| {
                // Fall back to VIR-level lookup and convert back to sema TypeId.
                let iter_vir = self.vir_query_lookup_iterator_interface_v(elem_vir_type_id)?;
                table.lookup_vir_type_id(iter_vir)
            });

        if let Some(iter_type_id) = iter_type_id {
            Ok(self.compiled_owned_with_ty(result, self.ptr_type(), iter_type_id))
        } else {
            // Sema TypeId not available (type created after VIR sweep without
            // reverse mapping). Use the VirTypeId directly so subsequent
            // method dispatch sees an Iterator<T> interface.
            let iter_vir = self
                .vir_query_lookup_iterator_interface_v(elem_vir_type_id)
                .unwrap_or(elem_vir_type_id);
            Ok(CompiledValue::owned(result, self.ptr_type(), iter_vir))
        }
    }

    fn string_length(&mut self, obj: &CompiledValue) -> CodegenResult<CompiledValue> {
        self.call_compiler_intrinsic_key_with_line(
            crate::IntrinsicKey::StringLen,
            &[obj.value],
            TypeId::I64,
            0,
        )
    }

    fn string_iter(
        &mut self,
        obj: &CompiledValue,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let result = self.call_runtime(RuntimeKey::StringCharsIter, &[obj.value])?;
        let iter_type_id = iter_type_hint.unwrap_or_else(|| {
            self.vir_query_lookup_iterator_interface(TypeId::STRING)
                .expect("INTERNAL: string iterator: Iterator<string> type not pre-created")
        });
        // Set elem_tag to RuntimeTypeId::String so terminal methods can properly
        // free owned char strings produced by the string chars iterator.
        let string_tag = self.vir_query_unknown_type_tag(TypeId::STRING);
        if string_tag != 0 {
            let tag_val = self.iconst_cached(types::I64, string_tag as i64);
            self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result, tag_val])?;
        }
        Ok(self.compiled_owned_with_ty(result, self.ptr_type(), iter_type_id))
    }

    /// Load start/end from a compiled range object and create a range iterator.
    fn range_iter_from_obj(
        &mut self,
        obj: &CompiledValue,
        iter_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let start = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), obj.value, 0);
        let end = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), obj.value, 8);
        let result = self.call_runtime(RuntimeKey::RangeIter, &[start, end])?;
        let iter_type_id = iter_type_hint.unwrap_or_else(|| {
            self.vir_query_lookup_iterator_interface(TypeId::I64)
                .expect("INTERNAL: range.iter(): Iterator<i64> type not pre-created")
        });
        Ok(self.compiled_owned_with_ty(result, self.ptr_type(), iter_type_id))
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

        let elem_vir = self.vir_query_unwrap_array_v(arr_obj.type_id);
        let (tag_val, value_bits, mut value) = if let Some(elem_vir) = elem_vir {
            self.prepare_dynamic_array_store_with_hint_v(value, elem_vir, None)?
        } else {
            self.prepare_dynamic_array_store_untyped(value)?
        };

        // RC: inc borrowed RC elements so the array gets its own reference.
        // Without this, the element's original binding and the array would
        // share a single refcount, causing use-after-free when the binding's
        // scope cleanup rc_dec's the value.
        self.rc_inc_borrowed_for_container(&value)?;

        // Get the runtime function reference
        let push_ref = self.runtime_func_ref(RuntimeKey::ArrayPush)?;

        // Call vole_array_push(arr_ptr, tag, value)
        self.emit_call(push_ref, &[arr_obj.value, tag_val, value_bits]);

        // The element value is consumed into the array container.
        value.mark_consumed();

        // Return void
        Ok(self.void_value())
    }
}
