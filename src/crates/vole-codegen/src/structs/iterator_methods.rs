// src/codegen/structs/iterator_methods.rs
//
// RuntimeIterator method dispatch, Iterator interface resolution,
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
use vole_identity::{NodeId, TypeDefId, TypeId};

use super::methods::ArgSource;

impl Cg<'_, '_, '_> {
    /// Resolve an Iterator interface method: find the external binding and
    /// compute the substituted return type (converting Iterator<T> to RuntimeIterator(T)).
    ///
    /// `fallback_elem_type` is used when expression data is absent (e.g. when compiling
    /// Iterable default method bodies like `map` whose expressions were not analyzed by sema).
    fn resolve_iterator_method(
        &self,
        method_name: &str,
        expr_id: Option<NodeId>,
        fallback_elem_type: Option<TypeId>,
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

        // In monomorphized module contexts, substituted_return_type can be absent.
        // Fall back to expression type before failing.
        // When compiling Iterable default method bodies (e.g. `map` in traits.vole),
        // sema never analyzes the expression so both lookups return None.
        // In that case, derive the return type from the method name + fallback_elem_type.
        let return_type_id = return_type_hint
            .or_else(|| expr_id.and_then(|id| self.get_substituted_return_type(&id)))
            .or_else(|| expr_id.and_then(|id| self.get_expr_type(&id)))
            .or_else(|| {
                fallback_elem_type.and_then(|elem_type_id| {
                    self.derive_iterator_return_type(method_name, elem_type_id, iter_type_id)
                })
            })
            .ok_or_else(|| {
                CodegenError::not_found(
                    "iterator method return type",
                    format!("{method_name} (expr_id={expr_id:?})"),
                )
            })?;

        // Convert Iterator<T> return types to RuntimeIterator(T) since the runtime
        // functions return raw iterator pointers, not boxed interface values
        let return_type_id = self.convert_iterator_return_type(return_type_id, iter_type_id);

        Ok((external_info, return_type_id))
    }

    /// Derive the return type of an Iterator method from the method name and element type.
    ///
    /// Used as a fallback when expression data is absent (interface default method bodies
    /// are not analyzed by sema). Returns None if the type can't be determined without
    /// expression data.
    fn derive_iterator_return_type(
        &self,
        method_name: &str,
        elem_type_id: TypeId,
        iter_type_id: TypeDefId,
    ) -> Option<TypeId> {
        let table = self.vir_type_table();
        match method_name {
            // Methods returning Iterator<T> — convert to RuntimeIterator<elem_type_id>
            "map" | "filter" | "take" | "skip" | "reverse" | "sorted" | "unique" | "chain"
            | "flatten" | "flat_map" | "filter_map" => {
                table.lookup_runtime_iterator_sema(elem_type_id)
            }

            // Methods returning Iterator<[i64, T]> for enumerate.
            // The actual enumerate element is [i64, T], but the RuntimeIterator
            // is keyed on the base elem_type_id. Return that if it exists.
            "enumerate" => table.lookup_runtime_iterator_sema(elem_type_id),

            // Methods returning Iterator<[T, T]> for zip
            "zip" => table.lookup_runtime_iterator_sema(elem_type_id),

            // Methods returning Iterator<[T]> for chunks/windows
            "chunks" | "windows" => table.lookup_runtime_iterator_sema(elem_type_id),

            // Method returning [T] (collect)
            "collect" => table.lookup_array_sema(elem_type_id),

            // Methods returning i64
            "count" => Some(TypeId::I64),

            // Methods returning bool
            "any" | "all" => Some(TypeId::BOOL),

            // Methods returning void
            "for_each" => Some(TypeId::VOID),

            // Methods returning T (the element type)
            "sum" | "reduce" => Some(elem_type_id),

            // Methods returning T? (optional element): first, last, nth, find
            // Optional<T> is pre-created in the TypeArena during sema analysis
            // (alongside RuntimeIterator<T>) whenever an Iterable<T> impl is registered.
            "first" | "last" | "nth" | "find" => table.lookup_optional_sema(elem_type_id),

            // next() -> T | Done — return the T type directly
            "next" => {
                let _ = iter_type_id;
                Some(elem_type_id)
            }

            // Unknown method: can't derive
            _ => None,
        }
    }

    /// Box a custom Iterator<T> implementor as a RuntimeIterator.
    ///
    /// Boxes the class instance as an Iterator<T> interface, then wraps it via
    /// InterfaceIter to create a RuntimeIterator that can be dispatched via
    /// the standard runtime iterator methods (collect, map, filter, count, etc.).
    pub(super) fn box_custom_iterator_to_runtime(
        &mut self,
        obj: &CompiledValue,
        elem_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Look up the Iterator<T> interface type (already interned by sema)
        let iterator_type_def = self
            .name_table()
            .well_known
            .iterator_type_def
            .ok_or_else(|| CodegenError::internal("Iterator type_def not found"))?;
        let interface_type_id = self
            .vir_type_table()
            .lookup_interface_sema(iterator_type_def, &[elem_type_id])
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "Iterator<T> interface type not pre-interned by sema",
                    format!("elem_type_id={elem_type_id:?}"),
                )
            })?;

        // Box the class instance as Iterator<T>
        let boxed = self.box_interface_value(*obj, interface_type_id)?;

        // Wrap in RcIterator via InterfaceIter
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[boxed.value])?;
        // Release the boxed interface ref (InterfaceIter took its own reference)
        let mut boxed_iface = boxed;
        self.consume_rc_value(&mut boxed_iface)?;

        // Fall back to RuntimeIterator<i64> when the specific element type
        // wasn't pre-interned (e.g. propagated class method monomorphs).
        // All RuntimeIterator types share the same RC-pointer layout.
        let runtime_iter_type_id = self
            .vir_query_lookup_runtime_iterator(elem_type_id)
            .or_else(|| self.vir_query_lookup_runtime_iterator(TypeId::I64))
            .expect("RuntimeIterator<i64> must always be pre-interned");
        Ok(self.compiled_owned_with_ty(wrapped, types::I64, runtime_iter_type_id))
    }

    /// Handle method calls on RuntimeIterator - calls external Iterator functions directly
    pub(super) fn runtime_iterator_method(
        &mut self,
        obj: &CompiledValue,
        arg_source: &ArgSource<'_>,
        method_name: &str,
        elem_type_id: TypeId,
        expr_id: Option<NodeId>,
        return_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let (external_info, return_type_id) = self.resolve_iterator_method(
            method_name,
            expr_id,
            Some(elem_type_id),
            return_type_hint,
        )?;

        // When the iterator comes from a variable (borrowed), rc_inc it before
        // pipeline and terminal method calls. Both categories assume ownership
        // transfer — pipeline methods store the source pointer, terminal methods
        // dec_ref it. The variable's scope-exit cleanup will emit a separate
        // rc_dec, so we need an extra reference to avoid a double-free.
        // Non-consuming methods like `next` just borrow the iterator and don't
        // need an rc_inc.
        let consumes_iterator = method_name != "next";
        if obj.is_borrowed() && consumes_iterator {
            self.emit_rc_inc(obj.value)?;
        }

        // Build args: self (iterator ptr) + method args
        //
        // Two distinct ownership contexts for closure parameters:
        //
        // A) Iterable default body (self.in_iterable_default_body == true):
        //    The compiled body (e.g. `__array_iterable_map`) receives `f` as an
        //    *owned* reference — the outer call-site used `used_array_iterable_path`
        //    which skips rc_dec for the closure. The body therefore owns the single
        //    reference to `f`.
        //    - Pipeline methods (map/filter/flat_map): iterator takes ownership of `f`;
        //      do NOT emit rc_inc (there is only one reference, and the iterator frees it).
        //    - Terminal methods (any/all/find): runtime borrows `f` but does NOT free it.
        //      Codegen MUST emit rc_dec after the call (track in borrowed_closure_args).
        //
        // B) Regular user code (self.in_iterable_default_body == false):
        //    The closure is a *borrowed* reference — the outer caller retains ownership
        //    and will dec_ref it (either via scope-exit for locals, or on return for
        //    function parameters).
        //    - Pipeline methods: iterator will also dec_ref the closure on drop.
        //      We MUST emit rc_inc so both cleanup paths can dec independently.
        //    - Terminal methods: runtime borrows and does NOT free. The outer caller
        //      handles dec_ref (scope-exit or return cleanup). No extra action needed.
        let stores_closure = matches!(method_name, "map" | "filter" | "flat_map" | "filter_map");
        let codegen_frees_closure = matches!(method_name, "find" | "any" | "all");
        let mut args: ArgVec = smallvec![obj.value];
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        // Borrowed RC args for codegen_frees_closure methods inside an Iterable default body.
        // In that context the outer caller transferred ownership (no rc_dec), so the body
        // must emit the rc_dec here after the runtime call returns.
        let iter_arg_count = arg_source.len();
        let mut borrowed_closure_args: Vec<CompiledValue> = Vec::new();
        for i in 0..iter_arg_count {
            // Check whether this arg is a local variable with scope-exit RC cleanup
            // BEFORE compiling, so we can see the variable binding.
            let arg_var_has_scope_exit_cleanup =
                if let vole_vir::VirExpr::LocalLoad { name, .. } = arg_source.0[i].as_ref() {
                    self.vars
                        .get(name)
                        .map(|(var, _)| {
                            self.rc_scopes.is_rc_local(*var)
                                || self.rc_scopes.is_composite_rc_local(*var)
                                || self.rc_scopes.is_union_rc_local(*var)
                        })
                        .unwrap_or(false)
                } else {
                    false
                };
            let compiled = self.compile_arg_from_source(arg_source, i)?;
            if stores_closure
                && compiled.is_borrowed()
                && self.rc_state_v(compiled.type_id).needs_cleanup()
            {
                if self.in_iterable_default_body {
                    // Iterable default body: `f` is owned (caller transferred ownership).
                    // The iterator receives the single reference and frees it on drop.
                    // Do NOT emit rc_inc.
                } else if arg_var_has_scope_exit_cleanup {
                    // Regular code, local variable: scope-exit will dec_ref AND iterator
                    // will dec_ref on drop. Bump the refcount so both can dec independently.
                    self.emit_rc_inc(compiled.value)?;
                } else {
                    // Regular code, function parameter: caller will dec_ref on return AND
                    // iterator will dec_ref on drop. Bump the refcount so both can dec.
                    self.emit_rc_inc(compiled.value)?;
                }
            } else if codegen_frees_closure
                && compiled.is_borrowed()
                && self.rc_state_v(compiled.type_id).needs_cleanup()
                && self.in_iterable_default_body
                && !arg_var_has_scope_exit_cleanup
            {
                // Iterable default body: terminal predicate methods borrow the closure
                // but don't free it. The outer caller transferred ownership (no rc_dec),
                // so codegen must emit the rc_dec here after the runtime call.
                borrowed_closure_args.push(compiled);
                // When arg_var_has_scope_exit_cleanup == true even inside an Iterable default
                // body, scope-exit handles the dec. (Unusual but handle it safely.)
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
        let mut result = if method_name == "reduce" {
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
        } else if method_name == "sum" {
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
        //
        // We must free both:
        //   - Owned closures (rc_temps): fresh lambdas that are not yet refcounted to anything else
        //   - Borrowed closures (borrowed_closure_args): closures from function parameters
        //     (e.g., `f` in a compiled Iterable default body like `self.iter().any(f)`).
        //     In that case the outer caller does NOT free the closure (used_array_iterable_path),
        //     so the inner body must dec it explicitly after the runtime call returns.
        if codegen_frees_closure {
            for mut tmp in rc_temps {
                self.consume_rc_value(&mut tmp)?;
            }
            for borrow in &borrowed_closure_args {
                self.emit_rc_dec_for_type_v(borrow.value, borrow.type_id)?;
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
            self.vir_query_unwrap_runtime_iterator_v(vir)
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

    /// Convert Iterator<T> return types to RuntimeIterator(T)
    ///
    /// When calling external iterator methods, the runtime returns raw iterator pointers,
    /// not boxed interface values. This function converts Interface/GenericInstance types
    /// for Iterator to RuntimeIterator so that subsequent method calls use direct dispatch.
    fn convert_iterator_return_type(&self, ty: TypeId, iterator_type_id: TypeDefId) -> TypeId {
        self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
    }

    /// Convert Iterator<T> return types to RuntimeIterator(T), using well-known type metadata
    /// Takes and returns TypeId for O(1) equality; converts internally for matching
    pub(crate) fn maybe_convert_iterator_return_type(&self, ty: TypeId) -> TypeId {
        // Look up the Iterator interface via well-known type metadata
        if let Some(iterator_type_id) = self.name_table().well_known.iterator_type_def {
            self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
        } else {
            ty
        }
    }

    /// Core implementation of iterator return type conversion
    /// Uses VirTypeTable to check for Iterator interface and convert to RuntimeIterator
    fn convert_iterator_return_type_by_type_def_id(
        &self,
        ty: TypeId,
        iterator_type_id: TypeDefId,
    ) -> TypeId {
        // Check if this is an Interface type matching Iterator
        if let Some((type_def_id, vir_type_args)) = self.vir_query_unwrap_interface(ty)
            && type_def_id == iterator_type_id
            && let Some(&elem_vir) = vir_type_args.first()
        {
            let table = self.vir_type_table();
            let elem_type_id = table.vir_to_type_id(elem_vir);
            // Look up existing RuntimeIterator type if sema created one.
            // If not found, this is a user-defined Iterator (e.g., pure Vole
            // MapKeyIterator/SetIterator) — keep the original Interface type
            // for vtable dispatch.
            if let Some(runtime_iter_id) = self.vir_query_lookup_runtime_iterator(elem_type_id) {
                return runtime_iter_id;
            }
        }
        ty
    }
}
