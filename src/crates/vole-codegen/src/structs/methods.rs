// src/codegen/structs/methods.rs
//
// Method call orchestration: the main `method_call` entry point routes to
// builtin_methods, iterator_methods, and method_dispatch submodules.

use cranelift::prelude::*;
use smallvec::{SmallVec, smallvec};

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use crate::context::Cg;
use crate::context::ExternalMethodRef;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use vole_identity::Symbol;
use vole_identity::{
    ClassMethodMonomorphKey, ImplementMethodMonomorphKey, MethodId, NameId, NamerLookup, NodeId,
    TypeId, VirTypeId,
};
use vole_vir::BuiltinMethod;
use vole_vir::VirRef;
use vole_vir::expr::{VirMethodDispatchKind, VirMethodDispatchMeta, VirResolvedMethod};
use vole_vir::types::VirType;

use super::static_methods::StaticMethodCallArgs;

// ============================================================================
// ArgSource / MethodCallSource: VIR method call data
// ============================================================================

/// Source of a call's arguments: VIR expression refs.
pub struct ArgSource<'a>(pub &'a [VirRef]);

impl ArgSource<'_> {
    /// Number of arguments in this source.
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

/// Source of a method call: VIR-native fields.
///
/// VIR method calls carry the pre-lowered receiver and args as `VirExpr` nodes
/// plus the original `NodeId` for sema metadata lookup.
pub struct MethodCallSource<'a> {
    pub receiver: &'a vole_vir::VirExpr,
    pub method: Symbol,
    pub args: &'a [VirRef],
}

impl<'a> MethodCallSource<'a> {
    /// The call arguments as an `ArgSource`.
    pub fn arg_source(&self) -> ArgSource<'a> {
        ArgSource(self.args)
    }

    /// Number of arguments (not counting receiver).
    pub fn arg_count(&self) -> usize {
        self.args.len()
    }
}

/// Thin wrapper around `VirResolvedMethod` for method resolution access.
#[derive(Clone, Copy, Debug)]
struct MethodResolutionRef<'a>(&'a VirResolvedMethod);

impl MethodResolutionRef<'_> {
    fn method_id(self) -> Option<MethodId> {
        self.0.method_id()
    }

    fn type_def_id(self) -> Option<vole_identity::TypeDefId> {
        self.0.type_def_id()
    }

    fn is_builtin(self) -> bool {
        self.0.is_builtin()
    }

    fn method_index(self) -> Option<u32> {
        self.0.method_index()
    }

    fn external_info(self) -> Option<ExternalMethodRef> {
        self.0.external_info().map(ExternalMethodRef::from)
    }

    fn is_interface_method(self) -> bool {
        self.0.is_interface_method()
    }
}

impl Cg<'_, '_, '_> {
    // ========================================================================
    // ArgSource helpers: compile arguments from VIR refs
    // ========================================================================

    /// Compile a single argument from an `ArgSource` at the given index.
    pub(crate) fn compile_arg_from_source(
        &mut self,
        source: &ArgSource<'_>,
        index: usize,
    ) -> CodegenResult<CompiledValue> {
        self.compile_vir_expr(&source.0[index])
    }

    /// Compile a single argument from an `ArgSource` with an expected type.
    ///
    /// Compiles the expression without coercion.  The caller is responsible
    /// for calling `coerce_to_type` after recording RC ownership in
    /// `rc_temps` (compile -> track ownership -> coerce).
    pub(crate) fn compile_arg_with_expected_type(
        &mut self,
        source: &ArgSource<'_>,
        index: usize,
        _expected_type: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.compile_vir_expr(&source.0[index])
    }

    /// Compile all arguments from an `ArgSource`, tracking RC temps.
    pub(crate) fn compile_args_tracking_rc(
        &mut self,
        source: &ArgSource<'_>,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let count = source.len();
        let mut values = Vec::with_capacity(count);
        let mut rc_temps = Vec::new();
        for i in 0..count {
            let compiled = self.compile_arg_from_source(source, i)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            values.push(compiled.value);
        }
        Ok((values, rc_temps))
    }

    fn resolved_func_type_id(&self, resolved: MethodResolutionRef<'_>) -> TypeId {
        let v = self.try_substitute_type_v(resolved.0.func_type_id());
        self.vir_type_table().vir_to_type_id(v)
    }

    fn resolved_return_type_id(&self, resolved: MethodResolutionRef<'_>) -> TypeId {
        let v = self.try_substitute_type_v(resolved.0.return_type_id());
        self.vir_type_table().vir_to_type_id(v)
    }

    fn resolved_dispatch_func_type_id(&self, resolved: MethodResolutionRef<'_>) -> TypeId {
        if let Some(method_id) = resolved.method_id() {
            return self.analyzed().method_signature_id(method_id);
        }
        self.resolved_func_type_id(resolved)
    }

    fn resolved_concrete_return_hint(&self, resolved: MethodResolutionRef<'_>) -> Option<TypeId> {
        resolved.0.concrete_return_hint().map(|ty| {
            let v = self.try_substitute_type_v(ty);
            self.vir_type_table().vir_to_type_id(v)
        })
    }

    /// Resolve method parameter types for argument coercion.
    ///
    /// Primary source is the VIR method definition's `param_types`.  Falls back
    /// to the resolved function type from the VIR type table.
    fn resolved_method_param_type_ids(
        &self,
        resolved: MethodResolutionRef<'_>,
    ) -> Option<Vec<TypeId>> {
        let table = self.vir_type_table();

        // Prefer VirMethodDef.param_types (VIR resolves Self during lowering)
        if let Some(method_id) = resolved.method_id() {
            let method_def = self.analyzed().method_def(method_id);
            return Some(
                method_def
                    .param_types
                    .iter()
                    .map(|&ty| {
                        let v = self.try_substitute_type_v(ty);
                        table.vir_to_type_id(v)
                    })
                    .collect(),
            );
        }

        // Fall back to the resolved function type from VIR
        if let VirType::Function { params, .. } = table.get(resolved.0.func_type_id()) {
            return Some(
                params
                    .iter()
                    .map(|&ty| {
                        let v = self.try_substitute_type_v(ty);
                        table.vir_to_type_id(v)
                    })
                    .collect(),
            );
        }
        None
    }

    /// Resolve method parameter TypeIds to concrete call-site types.
    ///
    /// Applies both function-level substitutions and receiver-generic
    /// substitutions (e.g. `Channel<T>.send(value: T)` with receiver
    /// `Channel<i64|string>`), so argument coercion sees concrete parameter
    /// types instead of raw `TypeParam` placeholders.
    fn concretize_method_param_type_ids_for_receiver(
        &self,
        receiver_type_id: TypeId,
        param_type_ids: &[TypeId],
    ) -> Vec<TypeId> {
        // VIR lowering resolves Self placeholders, so param types from VirMethodDef
        // should not contain Self.  However, UNKNOWN TypeIds (which Self maps to in
        // VIR before resolution) are replaced with the concrete receiver type.
        let table = self.vir_type_table();
        let mut resolved: Vec<TypeId> = param_type_ids
            .iter()
            .map(|&ty| {
                let vir_ty = table.lookup_type_id(ty);
                let ty = if vir_ty == Some(VirTypeId::UNKNOWN) {
                    receiver_type_id
                } else {
                    ty
                };
                self.try_substitute_type(ty)
            })
            .collect();

        let resolved_receiver = self.try_substitute_type(receiver_type_id);
        let resolved_receiver_vir = self.to_vir_type(resolved_receiver);
        let receiver_generic = self
            .vir_query_unwrap_class_v(resolved_receiver_vir)
            .or_else(|| self.vir_query_unwrap_interface_v(resolved_receiver_vir))
            .map(|(def_id, vir_args)| {
                let table = self.vir_type_table();
                let args: Vec<TypeId> = vir_args.iter().map(|&v| table.vir_to_type_id(v)).collect();
                (def_id, args)
            });

        let Some((type_def_id, type_args)) = receiver_generic else {
            return resolved;
        };
        if type_args.is_empty() {
            return resolved;
        }

        let type_params = self.analyzed().entity_type_params(type_def_id);
        if type_params.len() != type_args.len() {
            return resolved;
        }

        let mut subs: rustc_hash::FxHashMap<NameId, TypeId> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();
        if let Some(func_subs) = self.substitutions {
            let table = self.vir_type_table();
            for (&k, &v) in func_subs {
                subs.insert(k, table.vir_to_type_id(v));
            }
        }

        resolved = resolved
            .into_iter()
            .map(|ty| self.vir_query_lookup_substitute(ty, &subs).unwrap_or(ty))
            .collect();
        resolved
    }

    /// VirTypeId-accepting overload of
    /// [`concretize_method_param_type_ids_for_receiver`](Self::concretize_method_param_type_ids_for_receiver).
    ///
    /// Bridge method — converts the receiver `VirTypeId` to sema `TypeId`,
    /// then delegates to the original.
    fn concretize_method_param_type_ids_for_receiver_v(
        &self,
        receiver_vir_type_id: VirTypeId,
        param_type_ids: &[TypeId],
    ) -> Vec<TypeId> {
        let receiver_type_id = self.vir_type_table().vir_to_type_id(receiver_vir_type_id);
        self.concretize_method_param_type_ids_for_receiver(receiver_type_id, param_type_ids)
    }

    fn consume_method_receiver(
        &mut self,
        receiver: &mut CompiledValue,
        receiver_is_global_init_rc_iface: bool,
        receiver_is_interface: bool,
    ) -> CodegenResult<()> {
        // Global interface initializers are recompiled per use. They can surface as
        // untracked/borrowed values in method-call paths, but still represent fresh
        // temporary interface boxes that must be released after dispatch.
        if receiver_is_global_init_rc_iface && receiver_is_interface {
            self.emit_rc_dec_for_type_v(receiver.value, receiver.type_id)?;
            receiver.mark_consumed();
            return Ok(());
        }
        self.consume_rc_value(receiver)
    }

    /// Look up a method NameId using the context's interner (which may be a module interner)
    fn method_name_id(&self, name: Symbol) -> CodegenResult<NameId> {
        let name_table = self.name_table();
        let namer = NamerLookup::new(name_table, self.interner());
        namer.method(name).ok_or_else(|| {
            let resolved = self.interner().resolve(name);
            CodegenError::not_found("method name_id", resolved)
        })
    }

    /// Resolve an implement method monomorph from VIR dispatch metadata.
    ///
    /// Looks up `dispatch.implement_method_monomorph` in the VirProgram's
    /// `implement_method_monomorphs` map, returning the function key if the
    /// function has already been declared by `compile_implement_method_monomorphs`.
    fn try_resolve_implement_method_monomorph(
        &mut self,
        dispatch: &VirMethodDispatchMeta,
    ) -> Option<crate::FunctionKey> {
        let info = dispatch
            .implement_method_monomorph
            .as_ref()
            .and_then(|key| self.analyzed().implement_method_monomorphs.get(key))?;
        let fk = self.funcs().intern_name_id(info.mangled_name);
        self.funcs_ref().func_id(fk).is_some().then_some(fk)
    }

    /// Resolve an implement method monomorph by constructing the key from
    /// the object's VIR type and method name.
    ///
    /// Used in monomorphized generic contexts where the VIR dispatch metadata
    /// doesn't carry `implement_method_monomorph` (generic templates set it to
    /// `None`). Extracts the element type from array/string/range receivers
    /// and looks up the corresponding compiled function.
    fn try_resolve_implement_method_by_type(
        &mut self,
        method_name_id: NameId,
        obj_vir_type: VirTypeId,
    ) -> Option<crate::FunctionKey> {
        // Extract element VirTypeId from the receiver type.
        let elem_vir = self.vir_query_iterable_element_type_v(obj_vir_type)?;

        // Look up the array TypeDefId and Iterable interface TypeDefId.
        let array_name_id = self.analyzed().array_type_name_id()?;
        let array_tdef_id = self.analyzed().try_type_def_id(array_name_id)?;
        let interfaces = self.analyzed().implemented_interfaces(array_tdef_id);
        let iterable_tdef_id = interfaces.first().copied()?;

        let key = ImplementMethodMonomorphKey::new(
            iterable_tdef_id,
            array_tdef_id,
            method_name_id,
            vec![elem_vir],
        );
        let info = self.analyzed().implement_method_monomorphs.get(&key)?;
        let fk = self.funcs().intern_name_id(info.mangled_name);
        self.funcs_ref().func_id(fk).is_some().then_some(fk)
    }

    #[tracing::instrument(skip(self, mc), fields(method = %self.interner().resolve(mc.method)))]
    pub fn method_call(
        &mut self,
        mc: &MethodCallSource<'_>,
        expr_id: NodeId,
        dispatch: &VirMethodDispatchMeta,
    ) -> CodegenResult<CompiledValue> {
        let mc_method = mc.method;

        // Check for static method call FIRST - don't try to compile the receiver
        if let Some(VirResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type_id,
            ..
        }) = dispatch.resolved_method.as_ref()
        {
            return self.static_method_call(StaticMethodCallArgs {
                type_def_id: *type_def_id,
                method_id: *method_id,
                func_type_id: {
                    let v = self.try_substitute_type_v(*func_type_id);
                    let table = self.vir_type_table();
                    table.vir_to_type_id(v)
                },
                arg_source: &mc.arg_source(),
                expr_id,
                vir_dispatch: Some(dispatch),
            });
        }

        // Look up method resolution early to get concrete_return_hint for builtin methods.
        // In monomorphized context, skip sema resolution because it was computed for the type parameter,
        // not the concrete type.
        let resolution = if self.substitutions.is_some() {
            None
        } else {
            dispatch.resolved_method.as_ref().map(MethodResolutionRef)
        };

        // Extract concrete_return_hint for builtin iterator methods (array.iter, string.iter, range.iter)
        let concrete_return_hint = resolution.and_then(|r| self.resolved_concrete_return_hint(r));

        // Handle range.iter() specially when the receiver is a range literal expression.
        // Range expressions can't be compiled to values directly, so we extract
        // start/end from the VIR node and pass them to the runtime.
        // Check dispatch_kind when available; fall back to method name for
        // monomorphized contexts where sema doesn't annotate dispatch.
        if let vole_vir::VirExpr::Range {
            start,
            end,
            inclusive,
        } = mc.receiver
        {
            let is_range_iter = match dispatch.dispatch_kind {
                Some(VirMethodDispatchKind::Builtin(BuiltinMethod::RangeIter)) => true,
                None => self.interner().resolve(mc_method) == "iter",
                _ => false,
            };
            if is_range_iter {
                return self.vir_range_iter(start, end, *inclusive, concrete_return_hint);
            }
        }

        // Track whether the receiver is a global init producing an RC interface.
        // Global inits re-compile the expression each time, creating a temporary
        // allocation (closure boxed to interface) that must be freed after the call.
        let receiver_is_global_init_rc_iface =
            if let vole_vir::VirExpr::LocalLoad { name, .. } = mc.receiver {
                self.has_global_init(*name)
            } else {
                false
            };

        // Compile the receiver expression.
        let obj = self.compile_vir_expr(mc.receiver)?;
        let method_name_str = self.interner().resolve(mc_method);

        // Route method dispatch based on VIR's MethodDispatchKind annotation.
        // Normally set by sema during VIR lowering or by rederive after
        // monomorphization.  When compiling interface default method bodies
        // from templates (where the VIR has UNKNOWN receiver types and
        // dispatch_kind is None), derive it from the compiled receiver's
        // concrete VIR type using the canonical rederive logic.
        let dispatch_kind = dispatch.dispatch_kind.unwrap_or_else(|| {
            vole_vir::rederive_method_dispatch_kind_with_entities(
                obj.type_id,
                mc_method,
                self.vir_type_table(),
                self.interner(),
                self.analyzed().entity_metadata(),
            )
        });
        match dispatch_kind {
            VirMethodDispatchKind::Module { module_id } => {
                let resolved = dispatch.resolved_method.as_ref().ok_or_else(|| {
                    CodegenError::missing_resource("module method call missing VIR resolved method")
                })?;
                return self.module_method_call(
                    module_id,
                    &mc.arg_source(),
                    method_name_str,
                    resolved,
                    dispatch.generic_monomorph.as_ref(),
                    dispatch.resolved_call_args.as_deref(),
                );
            }
            VirMethodDispatchKind::Builtin(builtin) => {
                let result = self.builtin_method(builtin, &obj, concrete_return_hint)?;
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                return Ok(result);
            }
            VirMethodDispatchKind::ArrayPush => {
                let result = self.array_push_call(&obj, &mc.arg_source())?;
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                return Ok(result);
            }
            VirMethodDispatchKind::Iterator { elem_type } => {
                // elem_type is already concrete: it comes from sema VIR
                // lowering (non-generic), from rederive after monomorphization,
                // or from the codegen fallback (unwrapped from obj.type_id).
                // Use the VIR type table directly — no substitution needed.
                let table = self.vir_type_table();
                let elem_type_id = table.vir_to_type_id(elem_type);
                let return_type_hint = dispatch
                    .substituted_return_type
                    .map(|ty| {
                        let v = self.try_substitute_type_v(ty);
                        let table = self.vir_type_table();
                        table.vir_to_type_id(v)
                    })
                    .or_else(|| {
                        dispatch.resolved_method.as_ref().and_then(|r| {
                            self.resolved_concrete_return_hint(MethodResolutionRef(r))
                        })
                    })
                    .or_else(|| resolution.map(|r| self.resolved_return_type_id(r)));
                let builtin =
                    BuiltinMethod::from_iter_method_name(method_name_str).ok_or_else(|| {
                        CodegenError::not_found("iterator builtin method", method_name_str)
                    })?;
                return self.iterator_method(
                    &obj,
                    &mc.arg_source(),
                    method_name_str,
                    builtin,
                    elem_type_id,
                    None,
                    return_type_hint,
                );
            }
            VirMethodDispatchKind::CustomIterator {
                elem_type,
                interface_type,
            } => {
                let builtin =
                    BuiltinMethod::from_iter_method_name(method_name_str).ok_or_else(|| {
                        CodegenError::not_found("custom iterator builtin method", method_name_str)
                    })?;
                let return_type_hint = resolution
                    .and_then(|r| self.resolved_concrete_return_hint(r))
                    .or_else(|| {
                        dispatch.substituted_return_type.map(|ty| {
                            let v = self.try_substitute_type_v(ty);
                            let table = self.vir_type_table();
                            table.vir_to_type_id(v)
                        })
                    })
                    .or_else(|| resolution.map(|r| self.resolved_return_type_id(r)));
                return self.dispatch_custom_iterator_method(
                    obj,
                    &mc.arg_source(),
                    method_name_str,
                    builtin,
                    elem_type,
                    interface_type,
                    return_type_hint,
                );
            }
            VirMethodDispatchKind::Standard => {
                // Fall through to standard dispatch below.
            }
        }

        let method_name_id = self.method_name_id(mc_method)?;

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
            Some(r) if r.is_interface_method() && !dispatch.receiver_is_interface => None,
            other => other,
        };

        // Handle special cases from method resolution metadata.
        if let Some(resolved) = resolution {
            // Interface dispatch with pre-computed slot (optimized path)
            if let Some(method_index) = resolved.method_index() {
                // Compute the concrete return type for this vtable dispatch.
                // 1. Use concrete_return_hint if available (already Iterator<T>
                //    for iterator methods from sema's VirResolvedMethod).
                // 2. Otherwise derive from substituted_return_type (which has
                //    concrete type args).
                let return_type_override =
                    self.resolved_concrete_return_hint(resolved).or_else(|| {
                        dispatch.substituted_return_type.map(|ty| {
                            let v = self.try_substitute_type_v(ty);
                            let table = self.vir_type_table();
                            table.vir_to_type_id(v)
                        })
                    });
                let result = self.interface_dispatch_call_args_by_slot(
                    &obj,
                    &mc.arg_source(),
                    method_index,
                    self.resolved_dispatch_func_type_id(resolved),
                    return_type_override,
                )?;
                // Consume the owned RC receiver after the call. For temporaries
                // (e.g. make_nums().collect()), this rc_dec's the interface's
                // data_ptr so the underlying instance is freed. For borrowed
                // receivers (variables), consume_rc_value is a no-op.
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                return Ok(result);
            }

            // Interface dispatch - check if object is an interface type and dispatch via vtable
            // This is a fallback path when we don't have InterfaceMethod (e.g., in monomorphized context)
            // Extract interface info before mutable borrow
            let interface_info = self
                .vir_query_unwrap_interface_v(obj.type_id)
                .map(|(id, _)| id);
            if let Some(interface_type_id) = interface_info {
                let result = self.interface_dispatch_call_args_by_type_def_id(
                    &obj,
                    &mc.arg_source(),
                    interface_type_id,
                    method_name_id,
                    self.resolved_dispatch_func_type_id(resolved),
                )?;
                // Consume the owned RC receiver after the call (same as above).
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                return Ok(result);
            }

            // Functional interface calls
            let functional_func_type_id =
                if let VirResolvedMethod::FunctionalInterface { func_type_id, .. } = resolved.0 {
                    let v = self.try_substitute_type_v(*func_type_id);
                    let table = self.vir_type_table();
                    Some(table.vir_to_type_id(v))
                } else {
                    None
                };
            if let Some(func_type_id) = functional_func_type_id {
                // Use TypeDefId directly for EntityRegistry-based dispatch
                let interface_type_def_id = self
                    .vir_query_unwrap_interface_v(obj.type_id)
                    .map(|(id, _)| id);
                if let Some(interface_type_def_id) = interface_type_def_id {
                    let result = self.interface_dispatch_call_args_by_type_def_id(
                        &obj,
                        &mc.arg_source(),
                        interface_type_def_id,
                        method_name_id,
                        func_type_id,
                    )?;
                    let mut obj = obj;
                    self.consume_method_receiver(
                        &mut obj,
                        receiver_is_global_init_rc_iface,
                        dispatch.receiver_is_interface,
                    )?;
                    return Ok(result);
                }
                // For functional interfaces, the object holds the function ptr or closure.
                // All lambdas are now wrapped in Closure structs, so is_closure is always true.
                let is_closure = true;
                let result = self.functional_interface_call(
                    obj.value,
                    func_type_id,
                    is_closure,
                    &mc.arg_source(),
                )?;
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                return Ok(result);
            }

            // External method calls
            if let Some(external_info) = resolved.external_info() {
                let mut args: ArgVec = smallvec![obj.value];
                let mut rc_temps: Vec<CompiledValue> = Vec::new();
                let arg_source = mc.arg_source();
                let arg_count = mc.arg_count();
                let param_type_ids = self
                    .resolved_method_param_type_ids(resolved)
                    .map(|ids| ids.to_vec());
                if let Some(param_type_ids) = &param_type_ids {
                    for (i, &param_type_id) in param_type_ids.iter().enumerate().take(arg_count) {
                        let compiled =
                            self.compile_arg_with_expected_type(&arg_source, i, param_type_id)?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        let compiled = self.coerce_to_type_id(compiled, param_type_id)?;
                        args.push(compiled.value);
                    }
                } else {
                    for i in 0..arg_count {
                        let compiled = self.compile_arg_from_source(&arg_source, i)?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        args.push(compiled.value);
                    }
                }
                // Use concrete_return_hint if available (carries the correct
                // Iterator<T> type for iterator methods); otherwise use
                // the VIR-normalized return type (already Iterator<T>
                // for external methods, see VIR lowering).
                let return_type_id = self
                    .resolved_concrete_return_hint(resolved)
                    .unwrap_or_else(|| self.resolved_return_type_id(resolved));

                // Generic external methods with where-mappings are dispatched through
                // the generic intrinsic resolver (exact arm first, default arm fallback).
                if let Some(type_def_id) = resolved.type_def_id()
                    && let Some(generic_ext_info) = self
                        .analyzed()
                        .generic_external_method(type_def_id, method_name_id)
                {
                    let key = {
                        let empty_substitutions = rustc_hash::FxHashMap::default();
                        let sema_subs_ref = self.sema_substitutions();
                        let substitutions: &rustc_hash::FxHashMap<NameId, TypeId> =
                            match &sema_subs_ref {
                                Some(r) => r,
                                None => &empty_substitutions,
                            };
                        self.resolve_intrinsic_key_for_monomorph(
                            method_name_str,
                            &generic_ext_info.type_mappings,
                            substitutions,
                        )?
                    };
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
                    self.consume_method_receiver(
                        &mut obj,
                        receiver_is_global_init_rc_iface,
                        dispatch.receiver_is_interface,
                    )?;
                    return self.call_generic_external_intrinsic_method_args(
                        &ext_module_path,
                        &key,
                        &arg_source,
                        return_type_id,
                        concrete_param_type_ids.as_deref(),
                    );
                }

                let result = self.call_external_id(&external_info, &args, return_type_id)?;
                // Consume RC receiver and temp args after the call completes.
                // In chained calls like s.trim().to_upper(), the intermediate
                // string from trim() is Owned but was never rc_dec'd, causing
                // leaks/heap corruption. Similarly, Owned string arguments
                // (e.g., s.replace("world", "vole")) need cleanup.
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
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
        let (func_key, return_type_id, fallback_param_type_ids) = if let Some(resolved) = resolution
        {
            // Use method resolution's type_def_id for method_func_keys lookup.
            // Uses type's NameId for stable lookup across different analyzer instances
            let type_def_id = resolved
                .type_def_id()
                .ok_or_else(|| CodegenError::not_found("type_def_id", method_name_str))?;
            let type_name_id = self.analyzed().entity_type_name_id(type_def_id);

            let func_key = self
                .method_func_keys()
                .get(&(type_name_id, method_name_id))
                .copied()
                .or_else(|| {
                    // VIR metadata path: look up implement method monomorph by the
                    // per-call-site key stored during VIR lowering.
                    self.try_resolve_implement_method_monomorph(dispatch)
                });
            (func_key, self.resolved_return_type_id(resolved), None)
        } else {
            // Fallback path for monomorphized context: derive type_def_id from object type.
            // When inside a monomorphized method body, the object type may still be a type
            // parameter (e.g. T from class<T: Disposable>). Apply substitutions to get the
            // concrete type before looking up the TypeDefId.
            let resolved_obj_vir = self.try_substitute_type_v(obj.type_id);

            // In monomorphized context, resolution is None so the interface dispatch
            // paths above (lines 264-310) are skipped. Check here if the object is an
            // interface type and dispatch via vtable using VirTypeId directly.
            let interface_type_def_id = self
                .vir_query_unwrap_interface_v(resolved_obj_vir)
                .map(|(id, _)| id);
            if let Some(interface_type_def_id) = interface_type_def_id {
                let func_type_id = self
                    .analyzed()
                    .find_method(interface_type_def_id, method_name_id)
                    .map(|mid| self.analyzed().method_signature_id(mid))
                    .ok_or_else(|| {
                        CodegenError::not_found(
                            "interface method",
                            format!("{method_name_str} on interface"),
                        )
                    })?;
                let result = self.interface_dispatch_call_args_by_type_def_id(
                    &obj,
                    &mc.arg_source(),
                    interface_type_def_id,
                    method_name_id,
                    func_type_id,
                )?;
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                return Ok(result);
            }

            let resolved_obj_type_id = {
                let table = self.vir_type_table();
                table.vir_to_type_id(resolved_obj_vir)
            };
            let vir_obj = self.vir_lookup(resolved_obj_type_id);
            let type_def_id = self.vir_type_table().type_def_id(vir_obj).ok_or_else(|| {
                CodegenError::not_found(
                    "TypeDefId",
                    format!("{method_name_str} (receiver_type={resolved_obj_type_id:?})"),
                )
            })?;

            // Check for external method binding first (interface methods on primitives)
            if let Some(binding) = self
                .analyzed()
                .entity_metadata()
                .find_method_binding(type_def_id, method_name_id)
                && let Some(external_info) = &binding.external_info
            {
                // External method - call via FFI
                let param_type_ids = &binding.sema_func_type.params_id;
                let ext_arg_source = mc.arg_source();
                let ext_arg_count = mc.arg_count();
                let mut args: ArgVec = smallvec![obj.value];
                let mut rc_temps: Vec<CompiledValue> = Vec::new();
                for (i, &param_type_id) in param_type_ids.iter().enumerate().take(ext_arg_count) {
                    let compiled =
                        self.compile_arg_with_expected_type(&ext_arg_source, i, param_type_id)?;
                    if compiled.is_owned() {
                        rc_temps.push(compiled);
                    }
                    let compiled = self.coerce_to_type_id(compiled, param_type_id)?;
                    args.push(compiled.value);
                }
                // Use concrete_return_hint (already Iterator<T>) when
                // available; otherwise use VIR-normalized return type (already
                // Iterator<T> for external methods, see VIR lowering).
                // Falls back to entity binding's return type as last resort.
                let return_type_id = dispatch
                    .resolved_method
                    .as_ref()
                    .and_then(|r| {
                        self.resolved_concrete_return_hint(MethodResolutionRef(r))
                            .or_else(|| Some(self.resolved_return_type_id(MethodResolutionRef(r))))
                    })
                    .unwrap_or(binding.sema_func_type.return_type_id);
                let ext = ExternalMethodRef::from(*external_info);
                let result = self.call_external_id(&ext, &args, return_type_id)?;
                // Consume RC receiver and temp args after the call
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                self.consume_rc_args(&mut rc_temps)?;
                return Ok(result);
            }

            // Try method_func_keys lookup using type's NameId for stable lookup
            let type_name_id = self.analyzed().entity_type_name_id(type_def_id);
            let func_key = self
                .method_func_keys()
                .get(&(type_name_id, method_name_id))
                .copied()
                .or_else(|| {
                    // VIR metadata path: look up implement method monomorph by the
                    // per-call-site key stored during VIR lowering.
                    self.try_resolve_implement_method_monomorph(dispatch)
                })
                .or_else(|| {
                    // Fallback for monomorphized generic contexts where the VIR
                    // dispatch metadata lacks implement_method_monomorph (generic
                    // templates set it to None). Construct the key from the
                    // receiver's concrete VIR type.
                    self.try_resolve_implement_method_by_type(method_name_id, resolved_obj_vir)
                });

            // Get return type and param types from entity registry
            let (return_type_id, fb_param_ids) = self
                .analyzed()
                .entity_metadata()
                .find_method_binding(type_def_id, method_name_id)
                .map(|binding| {
                    (
                        binding.sema_func_type.return_type_id,
                        Some(binding.sema_func_type.params_id.clone()),
                    )
                })
                .or_else(|| {
                    self.analyzed()
                        .find_method(type_def_id, method_name_id)
                        .map(|mid| {
                            let method = self.analyzed().method_def(mid);
                            let vir_table = &self.analyzed().type_table;
                            let (params, ret) = vir_table
                                .lookup_type_id(method.signature_id)
                                .and_then(|vir_id| vir_table.unwrap_function(vir_id))
                                .map(|(params, ret)| {
                                    let sema_params: SmallVec<[TypeId; 4]> = params
                                        .iter()
                                        .map(|&p| vir_table.vir_to_type_id(p))
                                        .collect();
                                    let sema_ret = vir_table.vir_to_type_id(ret);
                                    (Some(sema_params), sema_ret)
                                })
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

        // Prefer VIR dispatch's substituted_return_type when available. In both
        // monomorphized and non-monomorphized contexts, the VIR metadata carries
        // the fully-resolved concrete return type. The entity registry fallback
        // (return_type_id from above) can contain unresolved interface type
        // parameters — e.g. Iterable default methods like sum() -> T where T is
        // the Iterable interface's type parameter, not the function's own type
        // parameter. try_substitute_type can't resolve these because they're not
        // in the function's substitution map.
        let mut return_type_id = dispatch
            .substituted_return_type
            .map(|ty| {
                let v = self.try_substitute_type_v(ty);
                let table = self.vir_type_table();
                table.vir_to_type_id(v)
            })
            .unwrap_or(return_type_id);

        // In monomorphized contexts, the return type may still contain an unsubstituted
        // type parameter from the Iterable interface (e.g. Iterator<T> where T is the
        // interface's type param, not the function's). The function's substitution map
        // can't resolve these. When this happens, construct Iterator<T> from the
        // receiver's concrete element type.
        if self.substitutions.is_some() {
            let needs_derivation = {
                let vir_ret = self.vir_lookup(return_type_id);
                if let Some((type_def_id, _)) = self.vir_query_unwrap_interface_v(vir_ret) {
                    self.name_table()
                        .well_known
                        .is_iterator_type_def(type_def_id)
                } else {
                    false
                }
            };
            if needs_derivation
                && let Some(elem_vir) = self.vir_query_iterable_element_type_v(obj.type_id)
            {
                let table = self.vir_type_table();
                let elem_type_id = table.vir_to_type_id(elem_vir);
                if let Some(runtime_iter) = table.lookup_iterator_interface_sema(elem_type_id) {
                    return_type_id = runtime_iter;
                }
            }
        }

        let class_method_monomorph_key = dispatch.class_method_generic.as_ref().map(|key| {
            ClassMethodMonomorphKey::new(
                key.class_name,
                key.method_name,
                key.type_keys
                    .iter()
                    .map(|&ty| self.try_substitute_type_v(ty))
                    .collect(),
            )
        });

        // Check if this is a monomorphized class method call
        // If so, use the monomorphized method's func_key instead
        let (method_func_ref, is_generic_class) = if let Some(monomorph_key) =
            class_method_monomorph_key.as_ref()
        {
            // Calls inside generic class methods are recorded with abstract keys
            // (TypeParam type_keys). In concrete monomorphized contexts, rewrite
            // those keys using the current substitution map before cache lookup.
            let effective_key = if let Some(subs) = self.substitutions {
                let needs_substitution = monomorph_key
                    .type_keys
                    .iter()
                    .any(|&vir_ty| self.vir_query_unwrap_type_param_v(vir_ty).is_some());
                if needs_substitution {
                    let concrete_keys: Vec<VirTypeId> = monomorph_key
                        .type_keys
                        .iter()
                        .map(|&vir_ty| {
                            if let Some(name_id) = self.vir_query_unwrap_type_param_v(vir_ty) {
                                subs.get(&name_id).copied().unwrap_or(vir_ty)
                            } else {
                                vir_ty
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

            // Look up the monomorphized instance from VirProgram
            if let Some(instance) = self.analyzed().class_method_monomorphs.get(&effective_key) {
                return_type_id = instance.func_type.return_type_id;
                let monomorph_func_key = self.funcs().intern_name_id(instance.mangled_name);
                // Monomorphized methods have concrete types, no i64 conversion needed
                (self.func_ref(monomorph_func_key)?, false)
            } else if let Some(expanded_info) = self
                .env
                .state
                .expanded_class_method_monomorphs
                .get(&effective_key)
            {
                // Found in codegen-side expanded monomorphs table.
                // This handles methods on generic module types (e.g. Channel<T>.close())
                // called from within monomorphized code (e.g. Task.stream<i64>).
                return_type_id = expanded_info.return_type_id;
                (self.func_ref(expanded_info.func_key)?, false)
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
                .vir_query_unwrap_class_v(obj.type_id)
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
            .and_then(|resolved| self.resolved_method_param_type_ids(resolved))
            .or_else(|| fallback_param_type_ids.map(|ids| ids.to_vec()));
        let mut args: ArgVec = smallvec![obj.value];
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        let final_arg_source = mc.arg_source();
        let final_arg_count = mc.arg_count();
        let param_type_ids = param_type_ids
            .map(|ids| ids.to_vec())
            .map(|ids| self.concretize_method_param_type_ids_for_receiver_v(obj.type_id, &ids));
        let mapping_is_valid = |mapping: &[Option<usize>]| {
            let mut method_param_offset = 0usize;
            if let Some(param_type_ids) = &param_type_ids {
                let len = param_type_ids.len();
                method_param_offset = usize::from(mapping.len() == len.saturating_add(1));
                if mapping.len() != len && method_param_offset == 0 {
                    return false;
                }
                if method_param_offset == 1 && mapping.first().and_then(|entry| *entry).is_some() {
                    return false;
                }
            }
            let mut seen = vec![false; final_arg_count];
            let mut mapped_count = 0usize;
            for call_idx in mapping.iter().skip(method_param_offset).flatten().copied() {
                if call_idx >= final_arg_count || seen[call_idx] {
                    return false;
                }
                seen[call_idx] = true;
                mapped_count += 1;
            }
            mapped_count == final_arg_count
        };
        // When named args were used, sema stored a resolved_call_args mapping that tells
        // us which call.args[j] fills each parameter slot i (and None means use the default).
        let named_mapping = dispatch
            .resolved_call_args
            .clone()
            .filter(|mapping| mapping_is_valid(mapping));
        if let Some(ref mapping) = named_mapping {
            let method_id_for_defaults = resolution.and_then(|r| r.method_id());
            if let Some(param_type_ids) = &param_type_ids {
                let method_param_offset =
                    usize::from(mapping.len() == param_type_ids.len().saturating_add(1));
                for (slot, opt_call_idx) in mapping.iter().enumerate() {
                    if slot < method_param_offset {
                        continue;
                    }
                    let param_index = slot - method_param_offset;
                    let Some(&param_type_id) = param_type_ids.get(param_index) else {
                        continue;
                    };
                    let compiled = if let Some(&Some(call_arg_idx)) = Some(opt_call_idx) {
                        let compiled = self.compile_arg_with_expected_type(
                            &final_arg_source,
                            call_arg_idx,
                            param_type_id,
                        )?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        let compiled = self.coerce_to_type_id(compiled, param_type_id)?;

                        if is_generic_class && compiled.ty != types::I64 {
                            self.emit_word(&compiled, None)?
                        } else {
                            compiled.value
                        }
                    } else if let Some(method_id) = method_id_for_defaults {
                        // slot uses its default value
                        let (default_vals, rc_owned) = self.compile_method_default_args(
                            method_id,
                            param_index,
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
            for (i, &param_type_id) in param_type_ids.iter().enumerate().take(final_arg_count) {
                let compiled =
                    self.compile_arg_with_expected_type(&final_arg_source, i, param_type_id)?;
                if compiled.is_owned() {
                    rc_temps.push(compiled);
                }
                // Coerce argument to parameter type if needed
                // (e.g., concrete type -> interface box, concrete type -> union)
                let compiled = self.coerce_to_type_id(compiled, param_type_id)?;

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
            for i in 0..final_arg_count {
                let compiled = self.compile_arg_from_source(&final_arg_source, i)?;
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

        let call = self.emit_call(method_func_ref, &args);

        // If the return type is a union, copy the data from the callee's stack to our own
        // IMMEDIATELY after the call, before any rc_dec calls (consume_rc_value/consume_rc_args)
        // can clobber the callee's stack frame.
        if self.vir_query_is_union(return_type_id) && !is_sret {
            let results = self.builder.inst_results(call);
            if !results.is_empty() {
                let src_ptr = results[0];
                let union_copy = self.copy_union_ptr_to_local(src_ptr, return_type_id);

                // Now consume RC receiver and arg temps.
                let mut obj = obj;
                self.consume_method_receiver(
                    &mut obj,
                    receiver_is_global_init_rc_iface,
                    dispatch.receiver_is_interface,
                )?;
                self.consume_rc_args(&mut rc_temps)?;

                return Ok(union_copy);
            }
        }

        // Consume RC receiver and arg temps after the call completes.
        // In chained calls like s.trim().to_upper(), the intermediate string
        // from trim() is Owned but was never rc_dec'd, causing leaks/heap
        // corruption. Similarly, Owned class arguments (e.g., b.equals(Id{n:5}))
        // need cleanup after the callee has consumed them.
        let mut obj = obj;
        self.consume_method_receiver(
            &mut obj,
            receiver_is_global_init_rc_iface,
            dispatch.receiver_is_interface,
        )?;
        self.consume_rc_args(&mut rc_temps)?;

        if is_sret {
            // Sret: result[0] is the sret pointer we passed in
            let results = self.builder.inst_results(call);
            return Ok(self.compiled_with_ty(results[0], self.ptr_type(), return_type_id));
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
            if self.vir_query_is_union(return_type_id) {
                return Ok(self.copy_union_ptr_to_local(result_value, return_type_id));
            }

            Ok(self.compiled_with_ty(result_value, expected_ty, return_type_id))
        }
    }

    /// Box+wrap a custom Iterator<T> implementor as an Iterator<T> thin pointer
    /// and dispatch the method via `iterator_method`.
    ///
    /// Called from both the resolved-method and fallback paths when the
    /// receiver is a concrete class/struct implementing Iterator<T>.
    fn dispatch_custom_iterator_method(
        &mut self,
        obj: CompiledValue,
        arg_source: &ArgSource<'_>,
        method_name: &str,
        builtin: BuiltinMethod,
        elem_vir: VirTypeId,
        iface_vir: VirTypeId,
        return_type_hint: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let iter_val = self.box_and_wrap_as_iterator(obj, iface_vir, elem_vir)?;
        let elem_type = {
            let v = self.try_substitute_type_v(elem_vir);
            let table = self.vir_type_table();
            table.vir_to_type_id(v)
        };
        self.iterator_method(
            &iter_val,
            arg_source,
            method_name,
            builtin,
            elem_type,
            None,
            return_type_hint,
        )
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
