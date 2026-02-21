// src/codegen/structs/methods.rs

use cranelift::prelude::*;
use cranelift_module::Module;
use smallvec::{SmallVec, smallvec};

use crate::RuntimeKey;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use super::helpers::convert_to_i64_for_storage;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::method_resolution::get_type_def_id_from_type_id;
use crate::types::{
    CompiledValue, RcLifecycle, array_element_tag_id, module_name_id, type_id_to_cranelift,
};
use vole_frontend::ast::CallArg;
use vole_frontend::{ExprKind, MethodCallExpr, NodeId, Symbol};
use vole_identity::{MethodId, NameId, TypeDefId};
use vole_identity::{ModuleId, NamerLookup};
use vole_sema::generic::ClassMethodMonomorphKey;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::resolution::ResolvedMethod;
use vole_sema::type_arena::TypeId;

impl Cg<'_, '_, '_> {
    fn consume_method_receiver(
        &mut self,
        receiver: &mut CompiledValue,
        receiver_is_global_init_rc_iface: bool,
    ) -> CodegenResult<()> {
        // Global interface initializers are recompiled per use. They can surface as
        // untracked/borrowed values in method-call paths, but still represent fresh
        // temporary interface boxes that must be released after dispatch.
        if receiver_is_global_init_rc_iface && self.arena().is_interface(receiver.type_id) {
            self.emit_rc_dec_for_type(receiver.value, receiver.type_id)?;
            receiver.mark_consumed();
            return Ok(());
        }
        self.consume_rc_value(receiver)
    }

    /// Look up a method NameId using the context's interner (which may be a module interner)
    fn method_name_id(&self, name: Symbol) -> CodegenResult<NameId> {
        let name_table = self.name_table();
        let namer = NamerLookup::new(name_table, self.interner());
        namer
            .method(name)
            .ok_or_else(|| CodegenError::not_found("method name_id", self.interner().resolve(name)))
    }

    #[tracing::instrument(skip(self, mc), fields(method = %self.interner().resolve(mc.method)))]
    pub fn method_call(
        &mut self,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Check for static method call FIRST - don't try to compile the receiver
        if let Some(ResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type_id,
            ..
        }) = self.analyzed().query().method_at(expr_id)
        {
            return self.static_method_call(*type_def_id, *method_id, *func_type_id, mc, expr_id);
        }

        // Look up method resolution early to get concrete_return_hint for builtin methods.
        // In monomorphized context, skip sema resolution because it was computed for the type parameter,
        // not the concrete type.
        let resolution = if self.substitutions.is_some() {
            None
        } else {
            self.analyzed().query().method_at(expr_id)
        };

        // Extract concrete_return_hint for builtin iterator methods (array.iter, string.iter, range.iter)
        let concrete_return_hint = resolution.and_then(|r| r.concrete_return_hint());

        // Handle range.iter() specially since range expressions can't be compiled to values directly.
        // Unwrap Grouping nodes (parenthesization) so `(0..n).iter()` is handled here
        // instead of falling through to builtin_method.
        let unwrapped_object = {
            let mut expr = &mc.object;
            while let ExprKind::Grouping(inner) = &expr.kind {
                expr = inner;
            }
            expr
        };
        if let ExprKind::Range(range) = &unwrapped_object.kind {
            let method_name = self.interner().resolve(mc.method);
            if method_name == "iter" {
                return self.range_iter(range, concrete_return_hint);
            }
        }

        // Track whether the receiver is a global init producing an RC interface.
        // Global inits re-compile the expression each time, creating a temporary
        // allocation (closure boxed to interface) that must be freed after the call.
        let receiver_is_global_init_rc_iface = if let ExprKind::Identifier(sym) = &mc.object.kind {
            self.global_init(*sym).is_some()
        } else {
            false
        };

        let obj = self.expr(&mc.object)?;
        let method_name_str = self.interner().resolve(mc.method);

        // Handle module method calls (e.g., math.sqrt(16.0), math.lerp(...))
        let module_id_opt = self.arena().unwrap_module(obj.type_id).map(|m| m.module_id);
        if let Some(module_id) = module_id_opt {
            return self.module_method_call(module_id, mc, expr_id, method_name_str);
        }

        // Handle built-in methods (passing concrete_return_hint for iter methods)
        if let Some(result) = self.builtin_method(&obj, method_name_str, concrete_return_hint)? {
            let mut obj = obj;
            self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
            return Ok(result);
        }

        // Handle array.push(value) - needs to compile argument and call runtime
        if let Some(_elem_type_id) = self.arena().unwrap_array(obj.type_id)
            && method_name_str == "push"
        {
            let result = self.array_push_call(&obj, mc)?;
            let mut obj = obj;
            self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
            return Ok(result);
        }

        // Handle RuntimeIterator methods - these call external functions directly
        // without interface boxing or vtable dispatch
        let runtime_iter_elem = self.arena().unwrap_runtime_iterator(obj.type_id);
        if let Some(elem_type_id) = runtime_iter_elem {
            return self.runtime_iterator_method(&obj, mc, method_name_str, elem_type_id, expr_id);
        }

        // Handle custom Iterator<T> implementors: box as Iterator<T> interface,
        // wrap via InterfaceIter into RuntimeIterator, then dispatch the method.
        if let Some(elem_type_id) = self.iterator_element_type(obj.type_id) {
            let runtime_iter = self.box_custom_iterator_to_runtime(&obj, elem_type_id)?;
            return self.runtime_iterator_method(
                &runtime_iter,
                mc,
                method_name_str,
                elem_type_id,
                expr_id,
            );
        }

        let method_name_id = self.method_name_id(mc.method)?;

        // Resolution was already looked up earlier (before builtin_method call)
        tracing::debug!(
            obj_type_id = ?obj.type_id,
            method = %method_name_str,
            resolution = ?resolution,
            "method call"
        );

        // If sema recorded InterfaceMethod dispatch but the receiver is a concrete (non-interface)
        // type, the resolution came from analyzing the interface default method body with `self:
        // Self`. When compiling that body for a concrete implementing type (e.g. string, [T],
        // range), vtable dispatch is wrong — we need direct/external dispatch instead. Treat
        // resolution as None so the monomorphized-fallback path (which derives dispatch from
        // obj.type_id) handles it correctly.
        let resolution = match resolution {
            Some(ResolvedMethod::InterfaceMethod { .. })
                if !self.arena().is_interface(obj.type_id) =>
            {
                None
            }
            other => other,
        };

        // Handle special cases from ResolvedMethod
        if let Some(resolved) = resolution {
            // Interface dispatch with pre-computed slot (optimized path)
            if let ResolvedMethod::InterfaceMethod {
                func_type_id,
                method_index,
                ..
            } = resolved
            {
                let result = self.interface_dispatch_call_args_by_slot(
                    &obj,
                    &mc.args,
                    *method_index,
                    *func_type_id,
                )?;
                // Consume the owned RC receiver after the call. For temporaries
                // (e.g. make_nums().collect()), this rc_dec's the interface's
                // data_ptr so the underlying instance is freed. For borrowed
                // receivers (variables), consume_rc_value is a no-op.
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                return Ok(result);
            }

            // Interface dispatch - check if object is an interface type and dispatch via vtable
            // This is a fallback path when we don't have InterfaceMethod (e.g., in monomorphized context)
            // Extract interface info before mutable borrow
            let interface_info = {
                let arena = self.arena();
                if arena.is_interface(obj.type_id) {
                    arena.unwrap_interface(obj.type_id).map(|(id, _)| id)
                } else {
                    None
                }
            };
            if let Some(interface_type_id) = interface_info {
                let result = self.interface_dispatch_call_args_by_type_def_id(
                    &obj,
                    &mc.args,
                    interface_type_id,
                    method_name_id,
                    resolved.func_type_id(),
                )?;
                // Consume the owned RC receiver after the call (same as above).
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                return Ok(result);
            }

            // Functional interface calls
            if let ResolvedMethod::FunctionalInterface { func_type_id, .. } = resolved {
                // Use TypeDefId directly for EntityRegistry-based dispatch
                let interface_type_def_id = {
                    let arena = self.arena();
                    arena.unwrap_interface(obj.type_id).map(|(id, _)| id)
                };
                if let Some(interface_type_def_id) = interface_type_def_id {
                    let result = self.interface_dispatch_call_args_by_type_def_id(
                        &obj,
                        &mc.args,
                        interface_type_def_id,
                        method_name_id,
                        *func_type_id,
                    )?;
                    let mut obj = obj;
                    self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                    return Ok(result);
                }
                // For functional interfaces, the object holds the function ptr or closure
                let is_closure = {
                    let arena = self.arena();
                    arena
                        .unwrap_function(obj.type_id)
                        .map(|(_, _, is_closure)| is_closure)
                        .or_else(|| {
                            arena
                                .unwrap_function(*func_type_id)
                                .map(|(_, _, is_closure)| is_closure)
                        })
                        .unwrap_or(true)
                };
                let result =
                    self.functional_interface_call(obj.value, *func_type_id, is_closure, mc)?;
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                return Ok(result);
            }

            // External method calls
            if let Some(external_info) = resolved.external_info() {
                let param_type_ids = self
                    .arena()
                    .unwrap_function(resolved.func_type_id())
                    .map(|(params, _, _)| params.clone());
                let mut args: ArgVec = smallvec![obj.value];
                let mut rc_temps: Vec<CompiledValue> = Vec::new();
                if let Some(param_type_ids) = &param_type_ids {
                    for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
                        let compiled = self.expr_with_expected_type(arg.expr(), param_type_id)?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        let compiled = self.coerce_to_type(compiled, param_type_id)?;
                        args.push(compiled.value);
                    }
                } else {
                    for arg in &mc.args {
                        let compiled = self.expr(arg.expr())?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        args.push(compiled.value);
                    }
                }
                // Use concrete_return_hint if available (for iter() methods),
                // otherwise fall back to maybe_convert_iterator_return_type for other methods
                let return_type_id = resolved.concrete_return_hint().unwrap_or_else(|| {
                    self.maybe_convert_iterator_return_type(resolved.return_type_id())
                });

                // Generic external methods with where-mappings are dispatched through
                // the generic intrinsic resolver (exact arm first, default arm fallback).
                if let Some(type_def_id) = resolved.type_def_id()
                    && let Some(generic_ext_info) = self
                        .analyzed()
                        .implement_registry()
                        .get_generic_external_method(type_def_id, resolved.method_name_id())
                {
                    let empty_substitutions = rustc_hash::FxHashMap::default();
                    let substitutions = self.substitutions.unwrap_or(&empty_substitutions);
                    let key = self.resolve_intrinsic_key_for_monomorph(
                        method_name_str,
                        &generic_ext_info.type_mappings,
                        substitutions,
                    )?;
                    let ext_module_path = self
                        .name_table()
                        .last_segment_str(generic_ext_info.module_path)
                        .unwrap_or_default();
                    let concrete_param_type_ids: Option<Vec<TypeId>> = param_type_ids
                        .as_ref()
                        .map(|ids| ids.iter().map(|&ty| self.try_substitute_type(ty)).collect());

                    // Clean up args from the initial compilation before generic intrinsic
                    // dispatch recompiles with expected type context.
                    self.consume_rc_args(&mut rc_temps)?;
                    let mut obj = obj;
                    self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                    return self.call_generic_external_intrinsic_args(
                        &ext_module_path,
                        &key,
                        &mc.args,
                        return_type_id,
                        concrete_param_type_ids.as_deref(),
                    );
                }

                let result = self.call_external_id(external_info, &args, return_type_id)?;
                // Consume RC receiver and temp args after the call completes.
                // In chained calls like s.trim().to_upper(), the intermediate
                // string from trim() is Owned but was never rc_dec'd, causing
                // leaks/heap corruption. Similarly, Owned string arguments
                // (e.g., s.replace("world", "vole")) need cleanup.
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                self.consume_rc_args(&mut rc_temps)?;
                return Ok(result);
            }

            // Builtin methods - return error since they should have been handled earlier
            if resolved.is_builtin() {
                return Err(CodegenError::internal_with_context(
                    "unhandled builtin method",
                    method_name_str,
                ));
            }
        }

        // Get func_key, return_type_id, and fallback_param_type_ids from resolution or fallback.
        // fallback_param_type_ids is used when resolution doesn't provide param types (e.g. in
        // monomorphized generic contexts where sema skips the generic body).
        // used_array_iterable_path tracks whether the method is a compiled Iterable default that
        // returns raw *mut RcIterator (not a boxed interface). This happens for:
        // 1. Array/primitive types whose Iterable default is in array_iterable_func_keys
        // 2. Primitive types (range, string) whose Iterable default is in method_func_keys
        //    (compiled via compile_implement_block) — these also return *mut RcIterator.
        let mut used_array_iterable_path = false;
        let (func_key, return_type_id, fallback_param_type_ids) = if let Some(resolved) = resolution
        {
            // Use ResolvedMethod's type_def_id and method_name_id for method_func_keys lookup
            // Uses type's NameId for stable lookup across different analyzer instances
            let type_def_id = resolved
                .type_def_id()
                .ok_or_else(|| CodegenError::not_found("type_def_id", method_name_str))?;
            let type_name_id = self.query().get_type(type_def_id).name_id;
            let resolved_method_name_id = resolved.method_name_id();

            // Detect if this is a DefaultMethod from Iterable interface.
            // Such methods (range::map, etc.) are compiled from the Iterable body which calls
            // self.iter().map(f). At runtime they return *mut RcIterator, not Iterator<T>.
            // Use interface_type_def_id (stable across interners) instead of interface_name
            // (Symbol), which fails when the interface is defined in the prelude's interner.
            let is_iterable_default_method = matches!(&resolved,
                ResolvedMethod::DefaultMethod { interface_type_def_id, .. }
                if self.name_table().well_known.is_iterable_type_def(*interface_type_def_id)
            );

            let func_key = self
                .method_func_keys()
                .get(&(type_name_id, resolved_method_name_id))
                .copied()
                .inspect(|_k| {
                    if is_iterable_default_method {
                        used_array_iterable_path = true;
                    }
                })
                .or_else(|| {
                    // Fallback: check array_iterable_func_keys for Iterable default methods on
                    // arrays and primitives (range, string). Each concrete self-type (e.g. [i64],
                    // range) has its own compiled function keyed by (method_name_id, self_type_id).
                    let key = self
                        .array_iterable_func_keys()
                        .get(&(resolved_method_name_id, obj.type_id))
                        .copied();
                    if key.is_some() {
                        used_array_iterable_path = true;
                    }
                    key
                });
            (func_key, resolved.return_type_id(), None)
        } else {
            // Fallback path for monomorphized context: derive type_def_id from object type.
            // When inside a monomorphized method body, the object type may still be a type
            // parameter (e.g. T from class<T: Disposable>). Apply substitutions to get the
            // concrete type before looking up the TypeDefId.
            let resolved_obj_type_id = self.substitute_type(obj.type_id);

            // In monomorphized context, resolution is None so the interface dispatch
            // paths above (lines 264-310) are skipped. Check here if the object is an
            // interface type and dispatch via vtable.
            let interface_type_def_id = {
                let arena = self.arena();
                if arena.is_interface(resolved_obj_type_id) {
                    arena
                        .unwrap_interface(resolved_obj_type_id)
                        .map(|(id, _)| id)
                } else {
                    None
                }
            };
            if let Some(interface_type_def_id) = interface_type_def_id {
                let func_type_id = self
                    .query()
                    .find_method(interface_type_def_id, method_name_id)
                    .map(|mid| self.query().get_method(mid).signature_id)
                    .ok_or_else(|| {
                        CodegenError::not_found(
                            "interface method",
                            format!("{method_name_str} on interface"),
                        )
                    })?;
                let result = self.interface_dispatch_call_args_by_type_def_id(
                    &obj,
                    &mc.args,
                    interface_type_def_id,
                    method_name_id,
                    func_type_id,
                )?;
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                return Ok(result);
            }

            let arena = self.arena();
            let type_def_id =
                get_type_def_id_from_type_id(resolved_obj_type_id, arena, self.analyzed())
                    .ok_or_else(|| CodegenError::not_found("TypeDefId", method_name_str))?;

            // Check for external method binding first (interface methods on primitives)
            if let Some(binding) = self.query().method_binding(type_def_id, method_name_id)
                && let Some(external_info) = binding.external_info
            {
                // External method - call via FFI
                let param_type_ids = &binding.func_type.params_id;
                let mut args: ArgVec = smallvec![obj.value];
                let mut rc_temps: Vec<CompiledValue> = Vec::new();
                for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
                    let compiled = self.expr_with_expected_type(arg.expr(), param_type_id)?;
                    if compiled.is_owned() {
                        rc_temps.push(compiled);
                    }
                    let compiled = self.coerce_to_type(compiled, param_type_id)?;
                    args.push(compiled.value);
                }
                let return_type_id =
                    self.maybe_convert_iterator_return_type(binding.func_type.return_type_id);
                let result = self.call_external_id(&external_info, &args, return_type_id)?;
                // Consume RC receiver and temp args after the call
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                self.consume_rc_args(&mut rc_temps)?;
                return Ok(result);
            }

            // Try method_func_keys lookup using type's NameId for stable lookup
            let type_name_id = self.query().get_type(type_def_id).name_id;
            let func_key = self
                .method_func_keys()
                .get(&(type_name_id, method_name_id))
                .copied()
                .or_else(|| {
                    // Fallback: check array_iterable_func_keys for Iterable default
                    // methods (filter, map, etc.) on arrays in monomorphized context.
                    self.array_iterable_func_keys()
                        .get(&(method_name_id, resolved_obj_type_id))
                        .copied()
                        .inspect(|_| {
                            used_array_iterable_path = true;
                        })
                });

            // Get return type and param types from entity registry
            let (return_type_id, fb_param_ids) = self
                .query()
                .method_binding(type_def_id, method_name_id)
                .map(|binding| {
                    (
                        binding.func_type.return_type_id,
                        Some(binding.func_type.params_id.clone()),
                    )
                })
                .or_else(|| {
                    self.query()
                        .find_method(type_def_id, method_name_id)
                        .map(|mid| {
                            let method = self.query().get_method(mid);
                            let (params, ret) = self
                                .arena()
                                .unwrap_function(method.signature_id)
                                .map(|(params, ret, _)| (Some(params.clone()), ret))
                                .unwrap_or((None, TypeId::VOID));
                            (ret, params)
                        })
                })
                .unwrap_or((TypeId::VOID, None));

            // In monomorphized context, the return type may still reference type
            // parameters (e.g. a method `getItem() -> T`). Apply substitutions to
            // get the concrete return type. Use best-effort substitution because
            // this fallback path can see partially specialized signatures; the
            // expression-level type (looked up below) remains the source of truth.
            let return_type_id = self.try_substitute_type(return_type_id);

            (func_key, return_type_id, fb_param_ids)
        };

        // In monomorphized contexts, method resolution already carries concrete
        // return types. Prefer that over expression-cache lookups, which can be
        // stale or collide across generic/module NodeIds.
        let mut return_type_id = if self.substitutions.is_some() {
            return_type_id
        } else {
            self.get_substituted_return_type(&expr_id)
                .unwrap_or(return_type_id)
        };

        // NOTE: RuntimeIterator conversion for Iterator<T> return types is handled
        // in the external method call paths above (which return early). Non-external
        // methods (pure Vole classes) return interface-boxed iterators and use vtable
        // dispatch — no RuntimeIterator conversion needed there.
        //
        // However, array_iterable_func_keys functions (compiled Iterable default methods
        // for arrays) return raw *mut RcIterator, not boxed interfaces. Apply the
        // RuntimeIterator conversion here so subsequent method calls use direct dispatch.
        if used_array_iterable_path {
            return_type_id = self.maybe_convert_iterator_return_type(return_type_id);
        }

        // Check if this is a monomorphized class method call
        // If so, use the monomorphized method's func_key instead
        let (method_func_ref, is_generic_class) =
            if let Some(monomorph_key) = self.query().class_method_generic_at(expr_id) {
                // Calls inside generic class methods are recorded with abstract keys
                // (TypeParam type_keys). In concrete monomorphized contexts, rewrite
                // those keys using the current substitution map before cache lookup.
                let effective_key = if let Some(subs) = self.substitutions {
                    let arena = self.arena();
                    let needs_substitution = monomorph_key
                        .type_keys
                        .iter()
                        .any(|&type_id| arena.unwrap_type_param(type_id).is_some());
                    if needs_substitution {
                        let concrete_keys: Vec<TypeId> = monomorph_key
                            .type_keys
                            .iter()
                            .map(|&type_id| {
                                if let Some(name_id) = arena.unwrap_type_param(type_id) {
                                    subs.get(&name_id).copied().unwrap_or(type_id)
                                } else {
                                    type_id
                                }
                            })
                            .collect();
                        ClassMethodMonomorphKey::new(
                            monomorph_key.class_name,
                            monomorph_key.method_name,
                            concrete_keys,
                        )
                    } else {
                        monomorph_key.clone()
                    }
                } else {
                    monomorph_key.clone()
                };

                // Look up the monomorphized instance
                if let Some(instance) = self
                    .registry()
                    .class_method_monomorph_cache
                    .get(&effective_key)
                {
                    return_type_id = instance.func_type.return_type_id;
                    let monomorph_func_key = self.funcs().intern_name_id(instance.mangled_name);
                    // Monomorphized methods have concrete types, no i64 conversion needed
                    (self.func_ref(monomorph_func_key)?, false)
                } else {
                    // Fallback to regular method if monomorph not found
                    let func_key = func_key.ok_or_else(|| {
                        CodegenError::not_found(
                            "method",
                            format!("{method_name_str} (no regular function key)"),
                        )
                    })?;
                    (self.func_ref(func_key)?, false)
                }
            } else {
                // Not a monomorphized class method, use regular dispatch
                let is_generic_class = self
                    .arena()
                    .unwrap_class(obj.type_id)
                    .map(|(_, type_args)| !type_args.is_empty())
                    .unwrap_or(false);
                let func_key = func_key.ok_or_else(|| {
                    CodegenError::not_found(
                        "method",
                        format!("{method_name_str} not found in method_func_keys"),
                    )
                })?;
                (self.func_ref(func_key)?, is_generic_class)
            };

        // Use TypeId-based params for argument coercion (e.g. concrete -> union, concrete -> interface).
        // Try resolution first, fall back to entity registry params from monomorphized context.
        let param_type_ids = resolution
            .and_then(|resolved: &ResolvedMethod| {
                self.arena()
                    .unwrap_function(resolved.func_type_id())
                    .map(|(params, _, _)| params.clone())
            })
            .or(fallback_param_type_ids);
        let mut args: ArgVec = smallvec![obj.value];
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        // When named args were used, sema stored a resolved_call_args mapping that tells
        // us which call.args[j] fills each parameter slot i (and None means use the default).
        let named_mapping = self
            .analyzed()
            .expression_data
            .get_resolved_call_args(expr_id)
            .cloned();
        if let Some(ref mapping) = named_mapping {
            let method_id_for_defaults = resolution.and_then(|r| r.method_id());
            if let Some(param_type_ids) = &param_type_ids {
                for (slot, opt_call_idx) in mapping.iter().enumerate() {
                    let param_type_id = param_type_ids[slot];
                    let compiled = if let Some(&Some(call_arg_idx)) = Some(opt_call_idx) {
                        let arg = &mc.args[call_arg_idx];
                        let compiled = self.expr_with_expected_type(arg.expr(), param_type_id)?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        let compiled = self.coerce_to_type(compiled, param_type_id)?;

                        if is_generic_class && compiled.ty != types::I64 {
                            self.emit_word(&compiled, None)?
                        } else {
                            compiled.value
                        }
                    } else if let Some(method_id) = method_id_for_defaults {
                        // slot uses its default value
                        let (default_vals, rc_owned) = self.compile_method_default_args(
                            method_id,
                            slot,
                            &[param_type_id],
                            is_generic_class,
                        )?;
                        rc_temps.extend(rc_owned);
                        if let Some(&val) = default_vals.first() {
                            val
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    };
                    args.push(compiled);
                }
            }
        } else if let Some(param_type_ids) = &param_type_ids {
            for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
                let compiled = self.expr_with_expected_type(arg.expr(), param_type_id)?;
                if compiled.is_owned() {
                    rc_temps.push(compiled);
                }
                // Coerce argument to parameter type if needed
                // (e.g., concrete type -> interface box, concrete type -> union)
                let compiled = self.coerce_to_type(compiled, param_type_id)?;

                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    self.emit_word(&compiled, None)?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }

            // Compile default arguments if fewer args provided than expected
            // args includes self, so provided_args = args.len() - 1, expected includes params only
            let provided_args = args.len() - 1; // subtract self
            let expected_params = param_type_ids.len();
            if provided_args < expected_params {
                // Get method_id from resolution to look up param_defaults
                if let Some(method_id) = resolution.and_then(|r| r.method_id()) {
                    let (default_args, _rc_owned) = self.compile_method_default_args(
                        method_id,
                        provided_args,
                        &param_type_ids[provided_args..],
                        is_generic_class,
                    )?;
                    args.extend(default_args);
                }
            }
        } else {
            for arg in &mc.args {
                let compiled = self.expr(arg.expr())?;
                if compiled.is_owned() {
                    rc_temps.push(compiled);
                }
                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    self.emit_word(&compiled, None)?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }
        // Handle struct return conventions: sret (large structs) or multi-value (small structs)
        let is_sret = if let Some(sret_ptr) = self.alloc_sret_ptr(return_type_id)? {
            args.insert(0, sret_ptr);
            true
        } else {
            false
        };

        let coerced = self.coerce_call_args(method_func_ref, &args);
        let call = self.builder.ins().call(method_func_ref, &coerced);
        self.field_cache.clear(); // Methods may mutate fields via self

        // If the return type is a union, copy the data from the callee's stack to our own
        // IMMEDIATELY after the call, before any rc_dec calls (consume_rc_value/consume_rc_args)
        // can clobber the callee's stack frame.
        if self.arena().is_union(return_type_id) && !is_sret {
            let results = self.builder.inst_results(call);
            if !results.is_empty() {
                let src_ptr = results[0];
                let union_copy = self.copy_union_ptr_to_local(src_ptr, return_type_id);

                // Now consume RC receiver and arg temps.
                // For compiled Iterable default methods (used_array_iterable_path), the callee
                // owns RC args (closures) and frees them internally. Mark them consumed without
                // emitting rc_dec to avoid a double-free.
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                if used_array_iterable_path {
                    for cv in rc_temps.iter_mut() {
                        cv.mark_consumed();
                    }
                } else {
                    self.consume_rc_args(&mut rc_temps)?;
                }

                return Ok(union_copy);
            }
        }

        // Consume RC receiver and arg temps after the call completes.
        // In chained calls like s.trim().to_upper(), the intermediate string
        // from trim() is Owned but was never rc_dec'd, causing leaks/heap
        // corruption. Similarly, Owned class arguments (e.g., b.equals(Id{n:5}))
        // need cleanup after the callee has consumed them.
        //
        // Exception: compiled Iterable default methods (used_array_iterable_path) take
        // ownership of all RC arguments (closures, etc.) and free them internally —
        // either by storing them in iterators (map/filter/flat_map), passing them through
        // to runtime functions that free them (reduce/for_each via vole_iter_reduce_tagged),
        // or borrowing and freeing them in the runtime (find/any/all). The caller must NOT
        // free these args again. Mark them consumed without emitting an rc_dec.
        let mut obj = obj;
        self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
        if used_array_iterable_path {
            // Ownership of RC args transferred to the compiled Iterable default method.
            // Mark as consumed to satisfy lifecycle tracking without emitting a double-free.
            for cv in rc_temps.iter_mut() {
                cv.mark_consumed();
            }
        } else {
            self.consume_rc_args(&mut rc_temps)?;
        }

        if is_sret {
            // Sret: result[0] is the sret pointer we passed in
            let results = self.builder.inst_results(call);
            return Ok(CompiledValue::new(
                results[0],
                self.ptr_type(),
                return_type_id,
            ));
        }

        // Small struct multi-value return: reconstruct from registers
        if self.is_small_struct_return(return_type_id) {
            let results = self.builder.inst_results(call);
            if results.len() == 2 {
                let results_vec: Vec<Value> = results.to_vec();
                return self.reconstruct_struct_from_regs(&results_vec, return_type_id);
            }
        }

        let results = self.builder.inst_results(call);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            // Generic methods are compiled with TypeParam -> i64, but we may need
            // a different type (f64, bool, etc). Convert using word_to_value.
            let expected_ty = self.cranelift_type(return_type_id);
            let actual_result = results[0];
            let actual_ty = self.builder.func.dfg.value_type(actual_result);

            let result_value = if actual_ty != expected_ty && actual_ty == types::I64 {
                // Method returned i64 (TypeParam) but we expect a different type
                self.convert_from_i64_storage(actual_result, return_type_id)
            } else {
                actual_result
            };

            // For union returns, copy out of the callee stack into a local stack
            // slot and mark RC unions as owned so discard paths can clean them.
            if self.arena().is_union(return_type_id) {
                return Ok(self.copy_union_ptr_to_local(result_value, return_type_id));
            }

            Ok(CompiledValue::new(
                result_value,
                expected_ty,
                return_type_id,
            ))
        }
    }

    /// Compile range.iter() - creates a range iterator from start..end
    /// `iter_type_hint` is the pre-computed RuntimeIterator type from sema's concrete_return_hint.
    fn range_iter(
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

    /// Handle method calls on module objects (e.g., math.sqrt(16.0), math.lerp(...)).
    /// Dispatches to external native functions, generic intrinsics, or pure Vole module functions.
    fn module_method_call(
        &mut self,
        module_id: ModuleId,
        mc: &MethodCallExpr,
        expr_id: NodeId,
        method_name_str: &str,
    ) -> CodegenResult<CompiledValue> {
        let module_path = self
            .analyzed()
            .name_table()
            .module_path(module_id)
            .to_string();
        let name_id = module_name_id(self.analyzed(), module_id, method_name_str);
        let resolution = self.analyzed().query().method_at(expr_id);
        let Some(ResolvedMethod::Implemented {
            external_info,
            func_type_id,
            ..
        }) = resolution
        else {
            return Err(CodegenError::not_found(
                "module method",
                format!("{}::{}", module_path, method_name_str),
            ));
        };

        // Get return type from arena
        let return_type_id = {
            let arena = self.arena();
            let (_, ret, _) = arena
                .unwrap_function(*func_type_id)
                .expect("INTERNAL: module method: missing function type");
            ret
        };

        // Compile arguments, tracking owned RC temps for cleanup
        let (args, mut rc_temps) = self.compile_call_args_tracking_rc(&mc.args)?;

        if let Some(ext_info) = external_info {
            // External FFI function
            let result = self.call_external_id(ext_info, &args, return_type_id)?;
            self.consume_rc_args(&mut rc_temps)?;
            return Ok(result);
        }

        // Check if this is a generic external intrinsic (e.g., math.sqrt<f64>)
        if let Some(monomorph_key) = self.query().monomorph_for(expr_id) {
            let instance_data = self.monomorph_cache().get(monomorph_key).map(|inst| {
                (
                    inst.original_name,
                    inst.func_type.params_id.to_vec(),
                    inst.func_type.return_type_id,
                    inst.substitutions.clone(),
                )
            });

            if let Some((original_name, mono_param_type_ids, mono_return_type_id, substitutions)) =
                instance_data
                && let Some(callee_name) = self.name_table().last_segment_str(original_name)
                && let Some(generic_ext_info) = self
                    .analyzed()
                    .implement_registry()
                    .get_generic_external(&callee_name)
            {
                let key = self.resolve_intrinsic_key_for_monomorph(
                    &callee_name,
                    &generic_ext_info.type_mappings,
                    &substitutions,
                )?;
                let ext_module_path = self
                    .name_table()
                    .last_segment_str(generic_ext_info.module_path)
                    .unwrap_or_default();

                let return_type_id = self.substitute_type(mono_return_type_id);
                let concrete_param_type_ids: Vec<TypeId> = mono_param_type_ids
                    .iter()
                    .map(|&ty| {
                        self.arena().expect_substitute(
                            ty,
                            &substitutions,
                            "module generic intrinsic args",
                        )
                    })
                    .collect();

                // Clean up rc_temps from initial arg compilation
                // (generic intrinsic recompiles args internally)
                self.consume_rc_args(&mut rc_temps)?;
                return self.call_generic_external_intrinsic_args(
                    &ext_module_path,
                    &key,
                    &mc.args,
                    return_type_id,
                    Some(&concrete_param_type_ids),
                );
            }
        }

        // Pure Vole function - call by mangled name
        let name_id = name_id.ok_or_else(|| {
            CodegenError::not_found(
                "module method",
                format!("{}::{}", module_path, method_name_str),
            )
        })?;
        let func_key = self.funcs().intern_name_id(name_id);
        let func_id = self.funcs().func_id(func_key).ok_or_else(|| {
            CodegenError::not_found(
                "module function",
                format!("{}::{}", module_path, method_name_str),
            )
        })?;

        // Use the func_registry's return type if it was overridden (e.g. generators
        // have their return type changed from Iterator<T> to RuntimeIterator(T) in
        // pass 1). Fall back to the sema return type otherwise.
        let return_type_id = self.funcs().return_type(func_key).unwrap_or(return_type_id);

        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);
        // Handle sret convention for large struct returns (3+ flat slots).
        let mut call_args = args;
        let is_sret = if let Some(sret_ptr) = self.alloc_sret_ptr(return_type_id)? {
            call_args.insert(0, sret_ptr);
            true
        } else {
            false
        };

        let coerced = self.coerce_call_args(func_ref, &call_args);
        let call_inst = self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear(); // Callee may mutate instance fields

        // For sret, result[0] is the sret pointer we passed in
        let result = if is_sret {
            let results = self.builder.inst_results(call_inst);
            CompiledValue::new(results[0], self.ptr_type(), return_type_id)
        } else {
            self.call_result(call_inst, return_type_id)?
        };
        self.consume_rc_args(&mut rc_temps)?;
        Ok(result)
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
    fn array_push_call(
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
        let push_args = self.coerce_call_args(push_ref, &[arr_obj.value, tag_val, value_bits]);
        self.builder.ins().call(push_ref, &push_args);

        // Return void
        let void_type_id = self.arena().void();
        Ok(CompiledValue::new(
            self.iconst_cached(types::I64, 0),
            types::I64,
            void_type_id,
        ))
    }

    /// Resolve an Iterator interface method: find the external binding and
    /// compute the substituted return type (converting Iterator<T> to RuntimeIterator(T)).
    ///
    /// `fallback_elem_type` is used when expression data is absent (e.g. when compiling
    /// Iterable default method bodies like `map` whose expressions were not analyzed by sema).
    fn resolve_iterator_method(
        &self,
        method_name: &str,
        expr_id: NodeId,
        fallback_elem_type: Option<TypeId>,
    ) -> CodegenResult<(ExternalMethodInfo, TypeId)> {
        // Look up the Iterator interface
        let iter_type_id = self
            .resolve_type_str_or_interface("Iterator")
            .ok_or_else(|| CodegenError::not_found("interface", "Iterator"))?;

        let iter_def = self.query().get_type(iter_type_id);

        // Find the method by name
        let method_id = iter_def
            .methods
            .iter()
            .find(|&&mid| {
                let m = self.query().get_method(mid);
                self.analyzed()
                    .name_table()
                    .last_segment_str(m.name_id)
                    .is_some_and(|n| n == method_name)
            })
            .ok_or_else(|| CodegenError::not_found("Iterator method", method_name))?;

        // Get the external binding for this method
        let external_info = *self
            .query()
            .method_external_binding(*method_id)
            .ok_or_else(|| CodegenError::not_found("external binding for Iterator", method_name))?;

        // In monomorphized module contexts, substituted_return_type can be absent.
        // Fall back to expression type before failing.
        // When compiling Iterable default method bodies (e.g. `map` in traits.vole),
        // sema never analyzes the expression so both lookups return None.
        // In that case, derive the return type from the method name + fallback_elem_type.
        let return_type_id = self
            .get_substituted_return_type(&expr_id)
            .or_else(|| self.get_expr_type(&expr_id))
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
        let arena = self.arena();
        match method_name {
            // Methods returning Iterator<T> — convert to RuntimeIterator<elem_type_id>
            "map" | "filter" | "take" | "skip" | "reverse" | "sorted" | "unique" | "chain"
            | "flatten" | "flat_map" => arena.lookup_runtime_iterator(elem_type_id),

            // Methods returning Iterator<[i64, T]> for enumerate
            "enumerate" => {
                // [i64, T] element type
                let tuple_type = arena.lookup_array(TypeId::I64).or_else(|| {
                    // Fall back to any array if [i64] not found
                    arena.lookup_runtime_iterator(elem_type_id)
                });
                // We need Iterator<[i64, T]> but that may not be in the arena.
                // Return the same RuntimeIterator<elem_type_id> as a best-effort fallback.
                // The actual element type tag will be set at runtime.
                tuple_type.and_then(|_| arena.lookup_runtime_iterator(elem_type_id))
            }

            // Methods returning Iterator<[T, T]> for zip
            "zip" => arena.lookup_runtime_iterator(elem_type_id),

            // Methods returning Iterator<[T]> for chunks/windows
            "chunks" | "windows" => arena.lookup_runtime_iterator(elem_type_id),

            // Method returning [T] (collect)
            "collect" => arena.lookup_array(elem_type_id),

            // Methods returning i64
            "count" => Some(TypeId::I64),

            // Methods returning bool
            "any" | "all" => Some(TypeId::BOOL),

            // Methods returning void
            "for_each" => Some(arena.void()),

            // Methods returning T (the element type)
            "sum" | "reduce" => Some(elem_type_id),

            // Methods returning T? (optional element): first, last, nth, find
            // The optional type is a Union(T, nil). Try to look it up in the arena.
            // If not found, fall back to elem_type_id (codegen will handle it).
            "first" | "last" | "nth" | "find" => {
                // Look for the optional type in the arena (Union with nil + elem).
                // The arena may have interned T? during sema analysis.
                arena.lookup_optional(elem_type_id)
            }

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
    fn box_custom_iterator_to_runtime(
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
            .arena()
            .lookup_interface(iterator_type_def, smallvec![elem_type_id])
            .ok_or_else(|| {
                CodegenError::internal("Iterator<T> interface type not found in arena")
            })?;

        // Box the class instance as Iterator<T>
        let boxed = self.box_interface_value(*obj, interface_type_id)?;

        // Wrap in RcIterator via InterfaceIter
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[boxed.value])?;
        // Release the boxed interface ref (InterfaceIter took its own reference)
        let mut boxed_iface = boxed;
        self.consume_rc_value(&mut boxed_iface)?;

        let runtime_iter_type_id = self
            .arena()
            .lookup_runtime_iterator(elem_type_id)
            .unwrap_or(TypeId::STRING);
        Ok(CompiledValue::owned(
            wrapped,
            types::I64,
            runtime_iter_type_id,
        ))
    }

    /// Handle method calls on RuntimeIterator - calls external Iterator functions directly
    fn runtime_iterator_method(
        &mut self,
        obj: &CompiledValue,
        mc: &MethodCallExpr,
        method_name: &str,
        elem_type_id: TypeId,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let (external_info, return_type_id) =
            self.resolve_iterator_method(method_name, expr_id, Some(elem_type_id))?;

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
        let stores_closure = matches!(method_name, "map" | "filter" | "flat_map");
        let codegen_frees_closure = matches!(method_name, "find" | "any" | "all");
        let mut args: ArgVec = smallvec![obj.value];
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        // Borrowed RC args for codegen_frees_closure methods inside an Iterable default body.
        // In that context the outer caller transferred ownership (no rc_dec), so the body
        // must emit the rc_dec after the runtime call returns.
        let mut borrowed_closure_args: Vec<CompiledValue> = Vec::new();
        for arg in &mc.args {
            let expr = arg.expr();
            // Check whether this arg is a local variable with scope-exit RC cleanup
            // BEFORE compiling, so we can see the variable binding.
            let arg_var_has_scope_exit_cleanup = if let ExprKind::Identifier(sym) = &expr.kind {
                self.vars
                    .get(sym)
                    .map(|(var, _)| {
                        self.rc_scopes.is_rc_local(*var)
                            || self.rc_scopes.is_composite_rc_local(*var)
                            || self.rc_scopes.is_union_rc_local(*var)
                    })
                    .unwrap_or(false)
            } else {
                // Non-identifier expressions (inline lambdas, etc.) are Owned, not Borrowed.
                // They won't enter borrowed-specific branches, so this value is unused.
                false
            };
            let compiled = self.expr(expr)?;
            if stores_closure
                && compiled.is_borrowed()
                && self.rc_state(compiled.type_id).needs_cleanup()
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
                && self.rc_state(compiled.type_id).needs_cleanup()
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
            let tag = crate::types::unknown_type_tag(elem_type_id, self.arena());
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
            CompiledValue::new(converted, expected_cty, return_type_id)
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
            CompiledValue::new(converted, expected_cty, effective_return_type)
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
                self.emit_rc_dec_for_type(borrow.value, borrow.type_id)?;
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
            let arena = self.arena();
            arena.unwrap_runtime_iterator(return_type_id)
        };
        if let Some(result_elem_id) = result_elem_type {
            let tag = crate::types::unknown_type_tag(result_elem_id, self.arena());
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

    /// Convert Iterator<T> return types to RuntimeIterator(T), looking up Iterator interface by name
    /// Takes and returns TypeId for O(1) equality; converts internally for matching
    pub(crate) fn maybe_convert_iterator_return_type(&self, ty: TypeId) -> TypeId {
        // Look up the Iterator interface
        let iterator_type_id = self.resolve_type_str_or_interface("Iterator");
        if let Some(iterator_type_id) = iterator_type_id {
            self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
        } else {
            ty
        }
    }

    /// Core implementation of iterator return type conversion
    /// Uses arena methods to check for Iterator interface and convert to RuntimeIterator
    fn convert_iterator_return_type_by_type_def_id(
        &self,
        ty: TypeId,
        iterator_type_id: TypeDefId,
    ) -> TypeId {
        let arena = self.arena();
        // Check if this is an Interface type matching Iterator
        if let Some((type_def_id, type_args)) = arena.unwrap_interface(ty)
            && type_def_id == iterator_type_id
            && let Some(&elem_type_id) = type_args.first()
        {
            // Look up existing RuntimeIterator type if sema created one.
            // If not found, this is a user-defined Iterator (e.g., pure Vole
            // MapKeyIterator/SetIterator) — keep the original Interface type
            // for vtable dispatch.
            if let Some(runtime_iter_id) = arena.lookup_runtime_iterator(elem_type_id) {
                return runtime_iter_id;
            }
        }
        ty
    }

    fn functional_interface_call(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        is_closure: bool,
        mc: &MethodCallExpr,
    ) -> CodegenResult<CompiledValue> {
        // Extract function type components from the arena
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) = arena.unwrap_function(func_type_id).ok_or_else(|| {
                CodegenError::type_mismatch("functional interface call", "function type", "other")
            })?;
            (params.clone(), ret)
        };

        // Check if this is actually a closure or a pure function
        // The is_closure flag is determined by the caller based on the actual
        // lambda's compilation, not the interface's generic signature.
        if is_closure {
            // It's a closure - extract function pointer and pass closure
            let func_ptr = self.call_runtime(RuntimeKey::ClosureGetFunc, &[func_ptr_or_closure])?;

            // Build the Cranelift signature for the closure call
            // First param is the closure pointer, then the user params
            let mut sig = self.jit_module().make_signature();
            sig.params.push(AbiParam::new(self.ptr_type())); // Closure pointer
            for &param_id in &param_ids {
                sig.params.push(AbiParam::new(type_id_to_cranelift(
                    param_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }
            let is_void_return = self.arena().is_void(return_type_id);
            if !is_void_return {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_type_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }

            // Compile arguments - closure pointer first, then user args
            let mut args: ArgVec = smallvec![func_ptr_or_closure];
            for arg in &mc.args {
                let compiled = self.expr(arg.expr())?;
                args.push(compiled.value);
            }

            let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);

            // Perform the indirect call
            let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
            self.call_result(call_inst, return_type_id)
        } else {
            // It's a pure function - call directly
            let mut sig = self.jit_module().make_signature();
            for &param_id in &param_ids {
                sig.params.push(AbiParam::new(type_id_to_cranelift(
                    param_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }
            let is_void_return = self.arena().is_void(return_type_id);
            if !is_void_return {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_type_id,
                    self.arena(),
                    self.ptr_type(),
                )));
            }

            let mut args = self.compile_call_args(&mc.args)?;
            let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);
            let call_inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_or_closure, &args);
            self.call_result(call_inst, return_type_id)
        }
    }

    /// Get the vtable slot index for an interface method by TypeDefId and method NameId.
    fn interface_method_slot(
        &self,
        interface_type_id: TypeDefId,
        method_name_id: NameId,
    ) -> CodegenResult<usize> {
        crate::interfaces::interface_method_slot_by_type_def_id(
            interface_type_id,
            method_name_id,
            self.registry(),
        )
    }

    /// Dispatch an interface method call by TypeDefId (EntityRegistry-based)
    pub(crate) fn interface_dispatch_call_args_by_type_def_id(
        &mut self,
        obj: &CompiledValue,
        args: &[CallArg],
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let slot = self.interface_method_slot(interface_type_id, method_name_id)?;
        self.interface_dispatch_call_args_inner(obj, args, slot, func_type_id)
    }

    /// Dispatch an interface method call with pre-computed vtable slot index.
    /// This is the optimized path where sema has already computed the slot.
    pub(crate) fn interface_dispatch_call_args_by_slot(
        &mut self,
        obj: &CompiledValue,
        args: &[CallArg],
        slot: u32,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.interface_dispatch_call_args_inner(obj, args, slot as usize, func_type_id)
    }

    fn interface_dispatch_call_args_inner(
        &mut self,
        obj: &CompiledValue,
        args: &[CallArg],
        slot: usize,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let word_type = self.ptr_type();
        let word_bytes = word_type.bytes() as i32;

        // Unwrap function type to get params and return type
        let (param_count, param_type_ids, return_type_id, is_void_return) = {
            let arena = self.arena();
            let (params, ret_id, _is_closure) =
                arena.unwrap_function(func_type_id).ok_or_else(|| {
                    CodegenError::type_mismatch(
                        "interface dispatch",
                        "function type",
                        "non-function",
                    )
                })?;
            (params.len(), params.to_vec(), ret_id, arena.is_void(ret_id))
        };

        // Load data pointer from boxed interface (first word)
        // Currently unused but kept for interface dispatch debugging
        let _data_word = self
            .builder
            .ins()
            .load(word_type, MemFlags::new(), obj.value, 0);
        let vtable_ptr = self
            .builder
            .ins()
            .load(word_type, MemFlags::new(), obj.value, word_bytes);
        let func_ptr = self.builder.ins().load(
            word_type,
            MemFlags::new(),
            vtable_ptr,
            (slot as i32) * word_bytes,
        );

        tracing::trace!(slot = slot, "interface vtable dispatch");

        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(word_type));
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(word_type));
        }
        if !is_void_return {
            sig.returns.push(AbiParam::new(word_type));
        }
        let sig_ref = self.builder.import_signature(sig);

        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;

        // Pass the full boxed interface pointer (not just data_word) so wrappers can
        // access both data and vtable. This is needed for Iterator methods that create
        // RcIterator adapters via vole_interface_iter.
        let mut call_args: ArgVec = smallvec![obj.value];
        for (i, arg) in args.iter().enumerate() {
            let compiled = if let Some(&expected_type_id) = param_type_ids.get(i) {
                self.expr_with_expected_type(arg.expr(), expected_type_id)?
            } else {
                self.expr(arg.expr())?
            };
            // Coerce arguments to their expected parameter types before converting
            // to word representation. Without this, union-typed parameters would be
            // passed as their concrete variant (e.g. i16) rather than as a tagged
            // union pointer, causing the callee's `is` checks to segfault.
            let compiled = if let Some(&expected_type_id) = param_type_ids.get(i) {
                self.coerce_to_type(compiled, expected_type_id)?
            } else {
                compiled
            };
            let word = self.emit_word(&compiled, Some(heap_alloc_ref))?;
            call_args.push(word);
        }

        let call = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr, &call_args);
        self.field_cache.clear(); // Interface methods may mutate fields
        let results = self.builder.inst_results(call);

        if is_void_return {
            return Ok(self.void_value());
        }

        let word = results
            .first()
            .copied()
            .ok_or_else(|| CodegenError::internal("interface call missing return value"))?;
        let value = self.convert_from_i64_storage(word, return_type_id);

        // Convert Iterator return types to RuntimeIterator for interface dispatch
        // since external iterator methods return raw iterator pointers, not boxed interfaces
        let return_type_id = self.maybe_convert_iterator_return_type(return_type_id);

        Ok(self.compiled(value, return_type_id))
    }

    /// Compile default expressions for omitted method parameters.
    /// Returns compiled values for parameters starting at `start_index`.
    pub(super) fn compile_method_default_args(
        &mut self,
        method_id: MethodId,
        start_index: usize,
        expected_types: &[TypeId],
        is_generic_class: bool,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        self.compile_method_defaults(method_id, start_index, expected_types, is_generic_class)
    }
}
