// src/codegen/structs/methods.rs
//
// Method call orchestration: the main `method_call` entry point routes to
// builtin_methods, iterator_methods, and method_dispatch submodules.

use cranelift::prelude::*;
use smallvec::{SmallVec, smallvec};

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::method_resolution::get_type_def_id_from_type_id;
use crate::types::CompiledValue;
use vole_frontend::ast::CallArg;
use vole_frontend::{ExprKind, MethodCallExpr, NodeId, Symbol};
use vole_identity::NamerLookup;
use vole_identity::{MethodId, NameId};
use vole_sema::generic::ClassMethodMonomorphKey;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::resolution::ResolvedMethod;
use vole_sema::type_arena::TypeId;
use vole_vir::VirRef;
use vole_vir::expr::{
    VirMethodDispatchKind, VirMethodDispatchMeta, VirMethodReceiverCoercion, VirResolvedMethod,
};
use vole_vir::types::VirType;

use super::static_methods::StaticMethodCallArgs;

// ============================================================================
// MethodCallSource: abstraction over AST and VIR method call data
// ============================================================================

/// Source of a method call's arguments: either AST `CallArg` slices or VIR refs.
///
/// This allows method dispatch code to work with both AST-based (old codegen
/// path) and VIR-based (new lowered path) method calls without duplication.
pub enum ArgSource<'a> {
    Ast(&'a [CallArg]),
    Vir(&'a [VirRef]),
}

impl ArgSource<'_> {
    /// Number of arguments in this source.
    pub fn len(&self) -> usize {
        match self {
            ArgSource::Ast(args) => args.len(),
            ArgSource::Vir(refs) => refs.len(),
        }
    }
}

/// Source of a method call: either an AST `MethodCallExpr` or VIR-native fields.
///
/// VIR method calls carry the pre-lowered receiver and args as `VirExpr` nodes
/// plus the original `NodeId` for sema metadata lookup.  The AST path carries
/// the original `MethodCallExpr` unchanged.
pub enum MethodCallSource<'a> {
    Ast(&'a MethodCallExpr),
    Vir {
        receiver: &'a vole_vir::VirExpr,
        method: Symbol,
        args: &'a [VirRef],
    },
}

impl<'a> MethodCallSource<'a> {
    /// The method name symbol.
    pub fn method(&self) -> Symbol {
        match self {
            MethodCallSource::Ast(mc) => mc.method,
            MethodCallSource::Vir { method, .. } => *method,
        }
    }

    /// The call arguments as an `ArgSource`.
    pub fn arg_source(&self) -> ArgSource<'a> {
        match self {
            MethodCallSource::Ast(mc) => ArgSource::Ast(&mc.args),
            MethodCallSource::Vir { args, .. } => ArgSource::Vir(args),
        }
    }

    /// Number of arguments (not counting receiver).
    pub fn arg_count(&self) -> usize {
        match self {
            MethodCallSource::Ast(mc) => mc.args.len(),
            MethodCallSource::Vir { args, .. } => args.len(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum MethodResolutionRef<'a> {
    Ast(&'a ResolvedMethod),
    Vir(&'a VirResolvedMethod),
}

impl MethodResolutionRef<'_> {
    fn method_id(self) -> Option<MethodId> {
        match self {
            MethodResolutionRef::Ast(r) => r.method_id(),
            MethodResolutionRef::Vir(r) => r.method_id(),
        }
    }

    fn type_def_id(self) -> Option<vole_identity::TypeDefId> {
        match self {
            MethodResolutionRef::Ast(r) => r.type_def_id(),
            MethodResolutionRef::Vir(r) => r.type_def_id(),
        }
    }

    fn is_builtin(self) -> bool {
        match self {
            MethodResolutionRef::Ast(r) => r.is_builtin(),
            MethodResolutionRef::Vir(r) => r.is_builtin(),
        }
    }

    fn method_index(self) -> Option<u32> {
        match self {
            MethodResolutionRef::Ast(r) => r.method_index(),
            MethodResolutionRef::Vir(r) => r.method_index(),
        }
    }

    fn external_info(self) -> Option<ExternalMethodInfo> {
        match self {
            MethodResolutionRef::Ast(r) => r.external_info().copied(),
            MethodResolutionRef::Vir(r) => r.external_info().map(|info| ExternalMethodInfo {
                module_path: info.module_path,
                native_name: info.native_name,
            }),
        }
    }

    fn is_interface_method(self) -> bool {
        match self {
            MethodResolutionRef::Ast(r) => matches!(r, ResolvedMethod::InterfaceMethod { .. }),
            MethodResolutionRef::Vir(r) => r.is_interface_method(),
        }
    }

    fn interface_type_def_id_for_default(self) -> Option<vole_identity::TypeDefId> {
        match self {
            MethodResolutionRef::Ast(ResolvedMethod::DefaultMethod {
                interface_type_def_id,
                ..
            }) => Some(*interface_type_def_id),
            MethodResolutionRef::Ast(_) => None,
            MethodResolutionRef::Vir(r) => r.default_interface_type_def_id(),
        }
    }
}

fn sema_dispatch_kind_from_vir(kind: VirMethodDispatchKind) -> vole_sema::MethodDispatchKind {
    match kind {
        VirMethodDispatchKind::Module { module_id } => {
            vole_sema::MethodDispatchKind::Module(module_id)
        }
        VirMethodDispatchKind::Builtin => vole_sema::MethodDispatchKind::Builtin,
        VirMethodDispatchKind::ArrayPush => vole_sema::MethodDispatchKind::ArrayPush,
        VirMethodDispatchKind::Standard => vole_sema::MethodDispatchKind::Standard,
    }
}

impl Cg<'_, '_, '_> {
    // ========================================================================
    // ArgSource helpers: compile arguments from either AST or VIR
    // ========================================================================

    /// Compile a single argument from an `ArgSource` at the given index.
    pub(crate) fn compile_arg_from_source(
        &mut self,
        source: &ArgSource<'_>,
        index: usize,
    ) -> CodegenResult<CompiledValue> {
        match source {
            ArgSource::Ast(args) => self.expr(args[index].expr()),
            ArgSource::Vir(refs) => self.compile_vir_expr(&refs[index]),
        }
    }

    /// Compile a single argument from an `ArgSource` with an expected type.
    ///
    /// For AST, delegates to `expr_with_expected_type` which propagates the
    /// expected type into array literal compilation (union elem hints).
    ///
    /// For VIR, compiles the expression without coercion.  The caller is
    /// responsible for calling `coerce_to_type` after recording RC ownership
    /// in `rc_temps`, matching the AST path's two-step pattern (compile ->
    /// track ownership -> coerce).
    pub(crate) fn compile_arg_with_expected_type(
        &mut self,
        source: &ArgSource<'_>,
        index: usize,
        expected_type: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match source {
            ArgSource::Ast(args) => self.expr_with_expected_type(args[index].expr(), expected_type),
            ArgSource::Vir(refs) => self.compile_vir_expr(&refs[index]),
        }
    }

    /// Compile all arguments from an `ArgSource`, tracking RC temps.
    pub(crate) fn compile_args_tracking_rc(
        &mut self,
        source: &ArgSource<'_>,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let count = match source {
            ArgSource::Ast(args) => args.len(),
            ArgSource::Vir(refs) => refs.len(),
        };
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
        match resolved {
            MethodResolutionRef::Ast(r) => r.func_type_id(),
            MethodResolutionRef::Vir(r) => self.sema_type_from_vir(r.func_type_id()),
        }
    }

    fn resolved_return_type_id(&self, resolved: MethodResolutionRef<'_>) -> TypeId {
        match resolved {
            MethodResolutionRef::Ast(r) => r.return_type_id(),
            MethodResolutionRef::Vir(r) => self.sema_type_from_vir(r.return_type_id()),
        }
    }

    fn resolved_dispatch_func_type_id(&self, resolved: MethodResolutionRef<'_>) -> TypeId {
        if let Some(method_id) = resolved.method_id() {
            return self.query().get_method(method_id).signature_id;
        }

        let resolved_signature_id = self.resolved_func_type_id(resolved);
        if self.signature_has_self_placeholder_param(resolved_signature_id)
            && let Some(signature_id) = self.resolved_interface_signature_id(resolved)
        {
            return signature_id;
        }
        resolved_signature_id
    }

    fn resolved_concrete_return_hint(&self, resolved: MethodResolutionRef<'_>) -> Option<TypeId> {
        match resolved {
            MethodResolutionRef::Ast(r) => r.concrete_return_hint(),
            MethodResolutionRef::Vir(r) => r
                .concrete_return_hint()
                .map(|ty| self.sema_type_from_vir(ty)),
        }
    }

    /// Resolve canonical interface method signature from `(interface, slot)`.
    ///
    /// Some VIR-carried interface func_type_ids still reference placeholder-
    /// based signatures; this recovers the canonical signature from the
    /// EntityRegistry method table.
    fn resolved_interface_signature_id(&self, resolved: MethodResolutionRef<'_>) -> Option<TypeId> {
        if !resolved.is_interface_method() {
            return None;
        }
        let interface_type_def_id = resolved.type_def_id()?;
        let slot = resolved.method_index()? as usize;
        let method_id = self
            .registry()
            .interface_methods_ordered(interface_type_def_id)
            .get(slot)
            .copied()?;
        Some(self.query().get_method(method_id).signature_id)
    }

    fn signature_has_self_placeholder_param(&self, signature_id: TypeId) -> bool {
        self.arena()
            .unwrap_function(signature_id)
            .is_some_and(|(params, _, _)| params.iter().any(|&p| self.arena().is_self_type(p)))
    }

    /// Resolve method parameter types for argument coercion.
    ///
    /// Primary source is the resolved function type. If unavailable, fall back
    /// to canonical method signatures from the entity registry.
    fn resolved_method_param_type_ids(
        &self,
        resolved: MethodResolutionRef<'_>,
    ) -> Option<Vec<TypeId>> {
        if let Some(method_id) = resolved.method_id() {
            let signature_id = self.query().get_method(method_id).signature_id;
            if let Some((params, _, _)) = self.arena().unwrap_function(signature_id) {
                return Some(params.to_vec());
            }
        }

        let resolved_signature_id = self.resolved_func_type_id(resolved);
        if self.signature_has_self_placeholder_param(resolved_signature_id)
            && let Some(signature_id) = self.resolved_interface_signature_id(resolved)
            && let Some((params, _, _)) = self.arena().unwrap_function(signature_id)
        {
            return Some(params.to_vec());
        }

        if let Some((params, _, _)) = self.arena().unwrap_function(resolved_signature_id) {
            return Some(params.to_vec());
        }
        if let MethodResolutionRef::Vir(r) = resolved
            && let VirType::Function { params, .. } = self.vir_type_table().get(r.func_type_id())
        {
            return Some(
                params
                    .iter()
                    .map(|&ty| self.sema_type_from_vir(ty))
                    .collect(),
            );
        }
        None
    }

    /// TEMP(N279-C): some VIR-resolved method signatures still include an
    /// implicit receiver (`self`) parameter. Call sites pass the receiver
    /// separately, so drop that leading slot only when the call shape shows an
    /// extra parameter beyond provided args.
    fn normalize_method_param_type_ids_for_call(
        &self,
        param_type_ids: &[TypeId],
        provided_arg_count: usize,
    ) -> Vec<TypeId> {
        let has_self_placeholder = param_type_ids
            .first()
            .is_some_and(|&first| self.arena().is_self_type(first));
        if has_self_placeholder && param_type_ids.len() >= provided_arg_count.saturating_add(1) {
            param_type_ids[1..].to_vec()
        } else {
            param_type_ids.to_vec()
        }
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
        let mut resolved: Vec<TypeId> = param_type_ids
            .iter()
            .map(|&ty| self.try_substitute_type(ty))
            .collect();

        let resolved_receiver = self.try_substitute_type(receiver_type_id);
        let receiver_generic = self
            .arena()
            .unwrap_class(resolved_receiver)
            .map(|(type_def_id, type_args)| (type_def_id, type_args.to_vec()))
            .or_else(|| {
                self.arena()
                    .unwrap_interface(resolved_receiver)
                    .map(|(type_def_id, type_args)| (type_def_id, type_args.to_vec()))
            });

        let Some((type_def_id, type_args)) = receiver_generic else {
            return resolved;
        };
        if type_args.is_empty() {
            return resolved;
        }

        let type_params = self.query().get_type(type_def_id).type_params.clone();
        if type_params.len() != type_args.len() {
            return resolved;
        }

        let mut subs: rustc_hash::FxHashMap<NameId, TypeId> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();
        if let Some(func_subs) = self.substitutions {
            for (&k, &v) in func_subs {
                subs.insert(k, v);
            }
        }

        resolved = resolved
            .into_iter()
            .map(|ty| self.arena().lookup_substitute(ty, &subs).unwrap_or(ty))
            .collect();
        resolved
    }

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

    #[tracing::instrument(skip(self, mc), fields(method = %self.interner().resolve(mc.method())))]
    pub fn method_call(
        &mut self,
        mc: &MethodCallSource<'_>,
        expr_id: NodeId,
        vir_dispatch: Option<&VirMethodDispatchMeta>,
    ) -> CodegenResult<CompiledValue> {
        let mc_method = mc.method();

        // Check for static method call FIRST - don't try to compile the receiver
        if let Some(dispatch) = vir_dispatch {
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
                    func_type_id: self.sema_type_from_vir(*func_type_id),
                    arg_source: &mc.arg_source(),
                    method_sym: mc_method,
                    expr_id,
                    vir_dispatch: Some(dispatch),
                });
            }
        } else if let Some(ResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type_id,
            ..
        }) = self.analyzed().query().method_at(expr_id)
        {
            return self.static_method_call(StaticMethodCallArgs {
                type_def_id: *type_def_id,
                method_id: *method_id,
                func_type_id: *func_type_id,
                arg_source: &mc.arg_source(),
                method_sym: mc_method,
                expr_id,
                vir_dispatch: None,
            });
        }

        // Look up method resolution early to get concrete_return_hint for builtin methods.
        // In monomorphized context, skip sema resolution because it was computed for the type parameter,
        // not the concrete type.
        let resolution = if let Some(dispatch) = vir_dispatch {
            dispatch
                .resolved_method
                .as_ref()
                .map(MethodResolutionRef::Vir)
        } else if self.substitutions.is_some() {
            None
        } else {
            self.analyzed()
                .query()
                .method_at(expr_id)
                .map(MethodResolutionRef::Ast)
        };

        // Extract concrete_return_hint for builtin iterator methods (array.iter, string.iter, range.iter)
        let concrete_return_hint = resolution.and_then(|r| self.resolved_concrete_return_hint(r));

        // Handle range.iter() specially since range expressions can't be compiled to values directly.
        // Unwrap Grouping nodes (parenthesization) so `(0..n).iter()` is handled here
        // instead of falling through to builtin_method.
        // Both AST and VIR paths need special handling because the normal dispatch
        // route for range.iter() resolves as Implemented (not Builtin) and calls the
        // external function with wrong arguments (pointer instead of start/end pair).
        match mc {
            MethodCallSource::Ast(ast_mc) => {
                let unwrapped_object = {
                    let mut expr = &ast_mc.object;
                    while let ExprKind::Grouping(inner) = &expr.kind {
                        expr = inner;
                    }
                    expr
                };
                if let ExprKind::Range(range) = &unwrapped_object.kind {
                    let method_name = self.interner().resolve(mc_method);
                    if method_name == "iter" {
                        return self.range_iter(range, concrete_return_hint);
                    }
                }
            }
            MethodCallSource::Vir { receiver, .. } => {
                if let vole_vir::VirExpr::Range {
                    start,
                    end,
                    inclusive,
                } = *receiver
                {
                    let method_name = self.interner().resolve(mc_method);
                    if method_name == "iter" {
                        return self.vir_range_iter(start, end, *inclusive, concrete_return_hint);
                    }
                }
            }
        }

        // Track whether the receiver is a global init producing an RC interface.
        // Global inits re-compile the expression each time, creating a temporary
        // allocation (closure boxed to interface) that must be freed after the call.
        let receiver_is_global_init_rc_iface = match mc {
            MethodCallSource::Ast(ast_mc) => {
                if let ExprKind::Identifier(sym) = &ast_mc.object.kind {
                    self.global_init(*sym).is_some()
                } else {
                    false
                }
            }
            MethodCallSource::Vir { receiver, .. } => {
                if let vole_vir::VirExpr::LocalLoad { name, .. } = receiver {
                    self.global_init(*name).is_some()
                } else {
                    false
                }
            }
        };

        // Compile the receiver expression.
        let obj = match mc {
            MethodCallSource::Ast(ast_mc) => self.expr(&ast_mc.object)?,
            MethodCallSource::Vir { receiver, .. } => self.compile_vir_expr(receiver)?,
        };
        let method_name_str = self.interner().resolve(mc_method);

        // Route method dispatch based on sema's MethodDispatchKind annotation.
        // In monomorphized contexts sema doesn't annotate (resolution is skipped),
        // so we fall back to type-detection for those cases.
        let dispatch_kind = if let Some(dispatch) = vir_dispatch {
            dispatch
                .dispatch_kind
                .map(sema_dispatch_kind_from_vir)
                .unwrap_or_else(|| self.infer_method_dispatch_kind(&obj, method_name_str))
        } else {
            self.get_method_dispatch_kind(expr_id)
                .unwrap_or_else(|| self.infer_method_dispatch_kind(&obj, method_name_str))
        };
        match dispatch_kind {
            vole_sema::MethodDispatchKind::Module(module_id) => {
                return self.module_method_call(
                    module_id,
                    &mc.arg_source(),
                    method_name_str,
                    if vir_dispatch.is_some() {
                        None
                    } else {
                        Some(expr_id)
                    },
                    vir_dispatch.and_then(|d| d.resolved_method.as_ref()),
                    vir_dispatch.and_then(|d| d.generic_monomorph.as_ref()),
                );
            }
            vole_sema::MethodDispatchKind::Builtin => {
                if let Some(result) =
                    self.builtin_method(&obj, method_name_str, concrete_return_hint)?
                {
                    let mut obj = obj;
                    self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                    return Ok(result);
                }
            }
            vole_sema::MethodDispatchKind::ArrayPush => {
                let result = self.array_push_call(&obj, &mc.arg_source())?;
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                return Ok(result);
            }
            vole_sema::MethodDispatchKind::Standard => {
                // Fall through to RuntimeIterator check and standard dispatch below.
            }
        }

        // RuntimeIterator dispatch: detected from the codegen-side compiled type
        // (not sema annotation) because the Iterator<T> → RuntimeIterator<T>
        // conversion happens in codegen only.
        if let Some(elem_type_id) = self.arena().unwrap_runtime_iterator(obj.type_id) {
            let return_type_hint = vir_dispatch
                .and_then(|d| {
                    d.substituted_return_type
                        .map(|ty| self.sema_type_from_vir(ty))
                })
                .or_else(|| resolution.map(|r| self.resolved_return_type_id(r)));
            return self.runtime_iterator_method(
                &obj,
                &mc.arg_source(),
                method_name_str,
                elem_type_id,
                if vir_dispatch.is_some() {
                    None
                } else {
                    Some(expr_id)
                },
                return_type_hint,
            );
        }

        // Handle custom Iterator<T> implementors: box as Iterator<T> interface,
        // wrap via InterfaceIter into RuntimeIterator, then dispatch the method.
        // Driven by sema's CoercionKind annotation — no type re-detection needed.
        let iterator_wrap_elem_type = if let Some(dispatch) = vir_dispatch {
            dispatch.receiver_coercion.map(|coercion| match coercion {
                VirMethodReceiverCoercion::IteratorWrap { elem_type, .. } => {
                    self.sema_type_from_vir(elem_type)
                }
            })
        } else {
            self.get_coercion_kind(expr_id).map(|kind| match kind {
                vole_sema::CoercionKind::IteratorWrap { elem_type } => elem_type,
            })
        };
        if let Some(elem_type) = iterator_wrap_elem_type {
            let runtime_iter = self.box_custom_iterator_to_runtime(&obj, elem_type)?;
            let return_type_hint = vir_dispatch
                .and_then(|d| {
                    d.substituted_return_type
                        .map(|ty| self.sema_type_from_vir(ty))
                })
                .or_else(|| resolution.map(|r| self.resolved_return_type_id(r)));
            return self.runtime_iterator_method(
                &runtime_iter,
                &mc.arg_source(),
                method_name_str,
                elem_type,
                if vir_dispatch.is_some() {
                    None
                } else {
                    Some(expr_id)
                },
                return_type_hint,
            );
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
            Some(r) if r.is_interface_method() && !self.arena().is_interface(obj.type_id) => None,
            other => other,
        };

        // Handle special cases from method resolution metadata.
        if let Some(resolved) = resolution {
            // Interface dispatch with pre-computed slot (optimized path)
            if let Some(method_index) = resolved.method_index() {
                let result = self.interface_dispatch_call_args_by_slot(
                    &obj,
                    &mc.arg_source(),
                    method_index,
                    self.resolved_dispatch_func_type_id(resolved),
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
                    &mc.arg_source(),
                    interface_type_id,
                    method_name_id,
                    self.resolved_dispatch_func_type_id(resolved),
                )?;
                // Consume the owned RC receiver after the call (same as above).
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
                return Ok(result);
            }

            // Functional interface calls
            let functional_func_type_id = match resolved {
                MethodResolutionRef::Ast(ResolvedMethod::FunctionalInterface {
                    func_type_id,
                    ..
                }) => Some(*func_type_id),
                MethodResolutionRef::Vir(VirResolvedMethod::FunctionalInterface {
                    func_type_id,
                    ..
                }) => Some(self.sema_type_from_vir(*func_type_id)),
                MethodResolutionRef::Ast(_) | MethodResolutionRef::Vir(_) => None,
            };
            if let Some(func_type_id) = functional_func_type_id {
                // Use TypeDefId directly for EntityRegistry-based dispatch
                let interface_type_def_id = {
                    let arena = self.arena();
                    arena.unwrap_interface(obj.type_id).map(|(id, _)| id)
                };
                if let Some(interface_type_def_id) = interface_type_def_id {
                    let result = self.interface_dispatch_call_args_by_type_def_id(
                        &obj,
                        &mc.arg_source(),
                        interface_type_def_id,
                        method_name_id,
                        func_type_id,
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
                                .unwrap_function(func_type_id)
                                .map(|(_, _, is_closure)| is_closure)
                        })
                        .unwrap_or(true)
                };
                let result = self.functional_interface_call(
                    obj.value,
                    func_type_id,
                    is_closure,
                    &mc.arg_source(),
                )?;
                let mut obj = obj;
                self.consume_method_receiver(&mut obj, receiver_is_global_init_rc_iface)?;
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
                    .map(|ids| self.normalize_method_param_type_ids_for_call(&ids, arg_count));
                if let Some(param_type_ids) = &param_type_ids {
                    for (i, &param_type_id) in param_type_ids.iter().enumerate().take(arg_count) {
                        let compiled =
                            self.compile_arg_with_expected_type(&arg_source, i, param_type_id)?;
                        if compiled.is_owned() {
                            rc_temps.push(compiled);
                        }
                        let compiled = self.coerce_to_type(compiled, param_type_id)?;
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
                // Use concrete_return_hint if available (for iter() methods),
                // otherwise fall back to maybe_convert_iterator_return_type for other methods
                let return_type_id =
                    self.resolved_concrete_return_hint(resolved)
                        .unwrap_or_else(|| {
                            self.maybe_convert_iterator_return_type(
                                self.resolved_return_type_id(resolved),
                            )
                        });

                // Generic external methods with where-mappings are dispatched through
                // the generic intrinsic resolver (exact arm first, default arm fallback).
                if let Some(type_def_id) = resolved.type_def_id()
                    && let Some(generic_ext_info) = self
                        .analyzed()
                        .implement_registry()
                        .get_generic_external_method(type_def_id, method_name_id)
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
            // Use method resolution's type_def_id for method_func_keys lookup.
            // Uses type's NameId for stable lookup across different analyzer instances
            let type_def_id = resolved
                .type_def_id()
                .ok_or_else(|| CodegenError::not_found("type_def_id", method_name_str))?;
            let type_name_id = self.query().get_type(type_def_id).name_id;

            // Detect if this is a DefaultMethod from Iterable interface.
            // Such methods (range::map, etc.) are compiled from the Iterable body which calls
            // self.iter().map(f). At runtime they return *mut RcIterator, not Iterator<T>.
            let is_iterable_default_method = resolved
                .interface_type_def_id_for_default()
                .is_some_and(|interface_type_def_id| {
                    self.name_table()
                        .well_known
                        .is_iterable_type_def(interface_type_def_id)
                });

            let func_key = self
                .method_func_keys()
                .get(&(type_name_id, method_name_id))
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
                        .get(&(method_name_id, obj.type_id))
                        .copied();
                    if key.is_some() {
                        used_array_iterable_path = true;
                    }
                    key
                });
            (func_key, self.resolved_return_type_id(resolved), None)
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
                    &mc.arg_source(),
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
                    .ok_or_else(|| {
                        CodegenError::not_found(
                            "TypeDefId",
                            format!("{method_name_str} (receiver_type={resolved_obj_type_id:?})"),
                        )
                    })?;

            // Check for external method binding first (interface methods on primitives)
            if let Some(binding) = self.query().method_binding(type_def_id, method_name_id)
                && let Some(external_info) = binding.external_info
            {
                // External method - call via FFI
                let param_type_ids = &binding.func_type.params_id;
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
        } else if let Some(dispatch) = vir_dispatch {
            dispatch
                .substituted_return_type
                .map(|ty| self.sema_type_from_vir(ty))
                .unwrap_or(return_type_id)
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

        let class_method_monomorph_key = vir_dispatch
            .and_then(|dispatch| {
                dispatch.class_method_generic.as_ref().map(|key| {
                    ClassMethodMonomorphKey::new(
                        key.class_name,
                        key.method_name,
                        key.type_keys
                            .iter()
                            .map(|&ty| self.sema_type_from_vir(ty))
                            .collect(),
                    )
                })
            })
            .or_else(|| {
                if vir_dispatch.is_some() {
                    None
                } else {
                    self.query().class_method_generic_at(expr_id).cloned()
                }
            });

        // Check if this is a monomorphized class method call
        // If so, use the monomorphized method's func_key instead
        let (method_func_ref, is_generic_class) =
            if let Some(monomorph_key) = class_method_monomorph_key.as_ref() {
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
            .and_then(|resolved| self.resolved_method_param_type_ids(resolved))
            .or_else(|| fallback_param_type_ids.map(|ids| ids.to_vec()));
        let mut args: ArgVec = smallvec![obj.value];
        let mut rc_temps: Vec<CompiledValue> = Vec::new();
        let final_arg_source = mc.arg_source();
        let final_arg_count = mc.arg_count();
        let param_type_ids = param_type_ids
            .map(|ids| self.normalize_method_param_type_ids_for_call(&ids, final_arg_count))
            .map(|ids| self.concretize_method_param_type_ids_for_receiver(obj.type_id, &ids));
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
        let named_mapping = vir_dispatch
            .and_then(|dispatch| dispatch.resolved_call_args.clone())
            .or_else(|| {
                if vir_dispatch.is_some() {
                    None
                } else {
                    self.analyzed()
                        .node_map
                        .get_resolved_call_args(expr_id)
                        .map(|s| s.to_vec())
                }
            })
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

    /// Infer the method dispatch kind from the receiver type when sema didn't
    /// annotate (e.g. in monomorphized generic contexts where sema resolution
    /// is skipped). RuntimeIterator dispatch is handled separately in the
    /// caller via `unwrap_runtime_iterator` on the compiled value's type.
    fn infer_method_dispatch_kind(
        &self,
        obj: &CompiledValue,
        method_name: &str,
    ) -> vole_sema::MethodDispatchKind {
        let arena = self.arena();
        if let Some(m) = arena.unwrap_module(obj.type_id) {
            return vole_sema::MethodDispatchKind::Module(m.module_id);
        }
        // Check array-specific methods: push needs its own path, other array
        // builtins (length, iter) go through builtin_method.
        if arena.unwrap_array(obj.type_id).is_some() {
            if method_name == "push" {
                return vole_sema::MethodDispatchKind::ArrayPush;
            }
            return vole_sema::MethodDispatchKind::Builtin;
        }
        // String and range builtins
        if obj.type_id == TypeId::STRING || obj.type_id == TypeId::RANGE {
            return vole_sema::MethodDispatchKind::Builtin;
        }
        vole_sema::MethodDispatchKind::Standard
    }
}
