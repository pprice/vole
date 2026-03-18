// src/codegen/structs/iterator_methods.rs
//
// Iterator<T> method dispatch, Iterator interface resolution,
// and iterator return type conversion.

use cranelift::prelude::*;
use smallvec::{SmallVec, smallvec};

use crate::RuntimeKey;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use crate::context::Cg;
use crate::context::ExternalMethodRef;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, RcLifecycle};
use vole_identity::{NodeId, TypeId};
use vole_vir::{BuiltinMethod, BuiltinReturnKind};

use super::methods::ArgSource;

impl Cg<'_, '_, '_> {
    /// Resolve an Iterator interface method: find the external binding and
    /// compute the return type from sema's `concrete_return_hint`.
    ///
    /// `elem_type_id` and `builtin` provide a fallback for Iterable default
    /// method bodies whose inner expressions lack sema type annotations.
    fn resolve_iterator_method(
        &self,
        method_name: &str,
        builtin: BuiltinMethod,
        elem_type_id: TypeId,
        expr_id: Option<NodeId>,
        return_type_hint: Option<TypeId>,
    ) -> CodegenResult<(ExternalMethodRef, TypeId)> {
        // Look up the Iterator interface via well-known type metadata
        let iter_type_id = self
            .name_table()
            .well_known
            .iterator_type_def
            .ok_or_else(|| CodegenError::not_found("interface", "Iterator"))?;

        let iter_methods = self.analyzed().type_methods(iter_type_id);

        // Find the method by name
        let method_id = iter_methods
            .iter()
            .find(|&&mid| {
                let m = self.analyzed().method_def(mid);
                self.analyzed()
                    .name_table()
                    .last_segment_str(m.name_id)
                    .is_some_and(|n| n == method_name)
            })
            .ok_or_else(|| CodegenError::not_found("Iterator method", method_name))?;

        // Get the external binding for this method
        let external_info = self
            .analyzed()
            .method_external_binding(*method_id)
            .map(ExternalMethodRef::from)
            .ok_or_else(|| CodegenError::not_found("external binding for Iterator", method_name))?;

        // The return_type_hint comes from sema's concrete_return_hint (already
        // Iterator<T>) or from substituted_return_type. When unavailable
        // (e.g. Iterable default bodies), derive from the BuiltinMethod's
        // return kind and the element type.
        let return_type_id = return_type_hint
            .or_else(|| expr_id.and_then(|_| self.get_call_return_type()))
            .or_else(|| self.derive_return_type_from_builtin(builtin, elem_type_id))
            .ok_or_else(|| {
                CodegenError::not_found(
                    "iterator method return type",
                    format!("{method_name} (expr_id={expr_id:?})"),
                )
            })?;

        Ok((external_info, return_type_id))
    }

    /// Derive the return type from a `BuiltinMethod`'s return kind and element type.
    ///
    /// Used as a fallback when sema's `concrete_return_hint` is unavailable,
    /// e.g. in Iterable default method bodies.
    fn derive_return_type_from_builtin(
        &self,
        builtin: BuiltinMethod,
        elem_type_id: TypeId,
    ) -> Option<TypeId> {
        let table = self.vir_type_table();
        match builtin.return_kind() {
            BuiltinReturnKind::Iterator => table.lookup_iterator_interface_sema(elem_type_id),
            BuiltinReturnKind::Array => table.lookup_array_sema(elem_type_id),
            BuiltinReturnKind::I64 => Some(TypeId::I64),
            BuiltinReturnKind::Bool => Some(TypeId::BOOL),
            BuiltinReturnKind::Void => Some(TypeId::VOID),
            BuiltinReturnKind::ElemType => Some(elem_type_id),
            BuiltinReturnKind::Optional => table.lookup_optional_sema(elem_type_id),
        }
    }

    /// Handle method calls on Iterator<T> thin pointers — calls external Iterator functions directly
    pub(super) fn runtime_iterator_method(
        &mut self,
        obj: &CompiledValue,
        arg_source: &ArgSource<'_>,
        method_name: &str,
        builtin: BuiltinMethod,
        elem_type_id: TypeId,
        expr_id: Option<NodeId>,
        return_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let (external_info, return_type_id) = self.resolve_iterator_method(
            method_name,
            builtin,
            elem_type_id,
            expr_id,
            return_type_hint,
        )?;

        // When the iterator comes from a variable (borrowed), rc_inc it before
        // pipeline and terminal method calls. Both categories assume ownership
        // transfer — pipeline methods store the source pointer, terminal methods
        // dec_ref it. The variable's scope-exit cleanup will emit a separate
        // rc_dec, so we need an extra reference to avoid a double-free.
        // Non-consuming methods like `next` just borrow the iterator and don't
        // need an rc_inc.
        if obj.is_borrowed() && builtin.consumes_iterator() {
            self.emit_rc_inc(obj.value)?;
        }

        // Build args: self (iterator ptr) + method args
        //
        // Closure parameters are borrowed — the caller retains ownership and will
        // dec_ref them (either via scope-exit for locals, or on return for function
        // parameters).
        //   - Pipeline methods (stores_closure): iterator will also dec_ref the
        //     closure on drop. Emit rc_inc so both cleanup paths can dec independently.
        //   - Terminal methods: runtime borrows and does NOT free. The outer caller
        //     handles dec_ref (scope-exit or return cleanup). No extra action needed.
        let stores_closure = builtin.stores_closure();
        let mut args: ArgVec = smallvec![obj.value];
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        let iter_arg_count = arg_source.len();
        for i in 0..iter_arg_count {
            let compiled = self.compile_arg_from_source(arg_source, i)?;
            if stores_closure
                && compiled.is_borrowed()
                && self.cached_rc_state_v(compiled.type_id).needs_cleanup()
            {
                // Borrowed closure param: scope-exit (or return cleanup) will dec_ref
                // AND iterator will dec_ref on drop. Bump the refcount so both can
                // dec independently.
                self.emit_rc_inc(compiled.value)?;
            } else if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            args.push(compiled.value);
        }

        // Note: collect reads elem_tag from the iterator's stored tag
        // (set by vole_iter_set_elem_tag after pipeline methods or by
        // interface_iter_tagged in vtable wrappers), so no extra argument
        // is needed here.

        // Call the external function directly. For reduce and sum, use
        // tagged variants that accept explicit elem type tags so the runtime
        // can dispatch between integer and floating-point operations.
        let mut result = if builtin == BuiltinMethod::IterReduce {
            let tag = self.vir_query_unknown_type_tag(elem_type_id);
            let tag_val = self.iconst_cached(types::I64, tag as i64);
            args.push(tag_val); // acc_tag
            args.push(tag_val); // elem_tag
            let result_val = self.call_runtime(RuntimeKey::IterReduceTagged, &args)?;
            // IterReduceTagged always returns i64 (word-sized generic value).
            // When the element type is not i64 (e.g. f64, bool, i8), convert
            // the raw i64 bits back to the proper Cranelift type.
            let expected_cty = self.cranelift_type(return_type_id);
            let actual_cty = self.builder.func.dfg.value_type(result_val);
            let converted = if actual_cty != expected_cty {
                self.convert_from_i64_storage(result_val, return_type_id)
            } else {
                result_val
            };
            self.compiled_with_ty(converted, expected_cty, return_type_id)
        } else if builtin == BuiltinMethod::IterSum {
            // sum() -> T: the runtime always returns i64 (raw word). When the
            // element type is a float, the runtime does float addition and returns
            // f64 bits packed as i64. We bitcast the raw result to the proper
            // Cranelift type so downstream IR (select in when/match) is correct.
            //
            // For non-numeric T (e.g. Iterator<[i64]> after flatten()), the type
            // system says T=[i64] but the runtime actually sums i64 values. We
            // fall back to i64 in that case to avoid RC cleanup on a raw integer.
            let result_val = self.call_runtime(RuntimeKey::IterSum, &args)?;
            let effective_return_type = if return_type_id.is_numeric() {
                return_type_id
            } else {
                TypeId::I64
            };
            let expected_cty = self.cranelift_type(effective_return_type);
            let actual_cty = self.builder.func.dfg.value_type(result_val);
            let converted = if actual_cty != expected_cty {
                self.convert_from_i64_storage(result_val, effective_return_type)
            } else {
                result_val
            };
            self.compiled_with_ty(converted, expected_cty, effective_return_type)
        } else {
            self.call_external_id(&external_info, &args, return_type_id)?
        };

        // Free predicate closures for terminal methods that don't take ownership.
        // find/any/all borrow the closure — codegen must free it after the call.
        // for_each/reduce free the closure themselves via Closure::free in the runtime.
        // Pipeline methods (map, filter, etc.) store closures in the iterator.
        if builtin.codegen_frees_closure() {
            for mut tmp in rc_temps {
                self.consume_rc_value(&mut tmp)?;
            }
        }

        // Mark RC-typed results as Owned so they get properly cleaned up
        if self.rc_state(return_type_id).needs_cleanup() {
            result.rc_lifecycle = RcLifecycle::Owned;
        }

        // For methods that return iterators, set the elem_tag on the result iterator
        // so that intermediate pipeline operations (map, filter) can properly manage
        // RC values (rc_dec consumed/rejected values of RC types).
        let result_elem_type = {
            let vir = self.vir_lookup(return_type_id);
            self.vir_query_unwrap_iterator_interface_v(vir)
                .and_then(|elem_vir| self.vir_type_table().lookup_vir_type_id(elem_vir))
        };
        if let Some(result_elem_id) = result_elem_type {
            let tag = self.vir_query_unknown_type_tag(result_elem_id);
            if tag != 0 {
                // Only set tag for non-default types (RC types, etc.)
                let tag_val = self.iconst_cached(types::I64, tag as i64);
                self.call_runtime_void(RuntimeKey::IterSetElemTag, &[result.value, tag_val])?;
            }
        }

        Ok(result)
    }
}
