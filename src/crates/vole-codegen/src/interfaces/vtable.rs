use rustc_hash::FxHashMap;
use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use cranelift_module::{DataDescription, DataId, Linkage, Module};

use super::vtable_ctx::{VtableCtx, VtableCtxView};
use crate::RuntimeFn;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, CompileEnv};
use crate::types::{
    CompiledValue, MethodInfo, method_name_id_by_str, type_id_size, type_id_to_cranelift,
    type_metadata_by_name_id, value_to_word, word_to_value_type_id,
};
use vole_frontend::Symbol;
use vole_identity::{MethodId, NameId, TypeDefId};
use vole_sema::EntityRegistry;
use vole_sema::entity_defs::TypeDefKind;
use vole_sema::implement_registry::{ExternalMethodInfo, ImplTypeId};
use vole_sema::type_arena::{SemaType, TypeId};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum InterfaceConcreteType {
    ImplTypeId(ImplTypeId),
    Function { is_closure: bool },
}

/// Key for vtable lookup. Uses String for interface_name instead of Symbol
/// because Symbol values are interner-specific, and different interners (main vs module)
/// would produce different Symbols for the same interface name, causing duplicate
/// vtable declarations.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct InterfaceVtableKey {
    interface_name: String,
    concrete: InterfaceConcreteType,
}

/// Tracking state for a vtable being built in phases.
#[derive(Debug, Clone)]
struct VtableBuildState {
    /// Data ID for this vtable (allocated in Phase 1)
    data_id: DataId,
    /// Interface name ID for method resolution
    interface_name_id: NameId,
    /// Concrete type for wrapper compilation (interned TypeId)
    concrete_type: TypeId,
    /// Type substitutions for generic interfaces (interned TypeIds)
    substitutions: FxHashMap<NameId, TypeId>,
    /// Method IDs to compile wrappers for
    method_ids: Vec<MethodId>,
}

#[derive(Debug, Default)]
pub(crate) struct InterfaceVtableRegistry {
    /// Completed vtables (after Phase 3)
    vtables: FxHashMap<InterfaceVtableKey, DataId>,
    /// In-progress vtables (during phased compilation)
    pending: FxHashMap<InterfaceVtableKey, VtableBuildState>,
    wrapper_counter: u32,
}

/// Wrapper struct containing the resolved method target and signature info.
/// We store param_count and returns_void instead of FunctionType because the method
/// signature may contain Invalid types (e.g., unresolved void) which would cause
/// FunctionType interning to fail. The wrapper only needs these two values for signature.
/// For type conversion in wrappers, we store interned param_type_ids and return_type_id.
struct VtableMethod {
    param_count: usize,
    returns_void: bool,
    /// Interned param TypeIds for type conversion in wrappers.
    /// Individual TypeIds may be Invalid, which is handled gracefully by conversion functions.
    param_type_ids: Vec<TypeId>,
    /// Interned return TypeId for return value conversion (may be Invalid for void).
    /// This is the concrete (substituted) type when available (e.g., `i64 | Done`).
    return_type_id: TypeId,
    /// Tag remapping table for union returns from generic implement blocks.
    /// When the callee is compiled with abstract type params (e.g., `T | Done`), the union
    /// tag ordering may differ from the concrete type (e.g., `i64 | Done`).
    /// Maps callee tag index -> concrete tag index.
    /// Only set when the callee and concrete unions have different variant orderings.
    union_tag_remap: Option<Vec<u8>>,
    target: VtableMethodTarget,
}

/// Target-specific data for vtable method resolution.
/// Direct and Implemented are combined since they have identical structure.
enum VtableMethodTarget {
    /// Direct method call on class (includes both direct methods and explicit implementations)
    Method(MethodInfo),
    /// External/native function binding
    External(ExternalMethodInfo),
    /// Closure or function pointer (no additional data needed)
    Function,
}

impl InterfaceVtableRegistry {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Phase 1: Get or declare a vtable.
    /// Does not compile wrappers yet - call ensure_compiled() later.
    #[tracing::instrument(skip(self, ctx, interface_type_arg_ids), fields(interface = %ctx.interner().resolve(interface_name)))]
    pub(crate) fn get_or_declare<C: VtableCtx>(
        &mut self,
        ctx: &mut C,
        interface_name: Symbol,
        interface_type_def_id: TypeDefId,
        interface_type_arg_ids: &[TypeId],
        concrete_type_id: TypeId,
    ) -> CodegenResult<DataId> {
        // Build key for lookup using arena unwraps
        let concrete_key = {
            let arena = ctx.arena();
            if let Some((_, _, is_closure)) = arena.unwrap_function(concrete_type_id) {
                InterfaceConcreteType::Function { is_closure }
            } else {
                let impl_type_id =
                    ImplTypeId::from_type_id(concrete_type_id, arena, ctx.registry()).ok_or_else(
                        || {
                            format!(
                                "cannot build vtable for unsupported type {:?}",
                                concrete_type_id
                            )
                        },
                    )?;
                InterfaceConcreteType::ImplTypeId(impl_type_id)
            }
        };
        // Resolve interface name to string for key (Symbol is interner-specific)
        let interface_name_str = ctx.interner().resolve(interface_name).to_string();
        let key = InterfaceVtableKey {
            interface_name: interface_name_str,
            concrete: concrete_key,
        };

        // Return if already completed
        if let Some(data_id) = self.vtables.get(&key) {
            return Ok(*data_id);
        }

        // Return if already pending (Phase 1 done)
        if let Some(state) = self.pending.get(&key) {
            return Ok(state.data_id);
        }

        // Get interface metadata from the passed TypeDefId (don't re-resolve by name
        // since interface_by_short_name could return a different interface with the same name)
        let interface_def = ctx.query().get_type(interface_type_def_id);
        let interface_name_id = interface_def.name_id;

        // Build substitution map from type param names to concrete type args (already TypeIds)
        let mut substitutions: FxHashMap<NameId, TypeId> = interface_def
            .type_params
            .iter()
            .zip(interface_type_arg_ids.iter())
            .map(|(param_name_id, &arg_id)| (*param_name_id, arg_id))
            .collect();

        // Also map class type params to their concrete args.
        // When sema pre-computes method signatures for a generic class implementing
        // an interface (e.g. class Foo<K, V> implements Iterator<K>), it substitutes
        // interface params with class params (T -> K), so stored signatures contain
        // class type params (K | Done). We need K -> concrete_arg in the map too.
        let class_info = ctx
            .arena()
            .unwrap_nominal(concrete_type_id)
            .map(|(id, args, _)| (id, args.to_vec()));
        if let Some((class_def_id, class_type_args)) = class_info {
            let class_def = ctx.query().get_type(class_def_id);
            for (param_name, arg_id) in class_def.type_params.iter().zip(class_type_args.iter()) {
                substitutions.insert(*param_name, *arg_id);
            }
        }

        // Collect method IDs
        let method_ids =
            collect_interface_methods_via_entity_registry(interface_type_def_id, ctx.registry())?;

        // Build vtable name and declare data
        let type_name = match concrete_key {
            InterfaceConcreteType::ImplTypeId(type_id) => {
                ctx.analyzed().name_table().display(type_id.name_id())
            }
            InterfaceConcreteType::Function { is_closure } => {
                if is_closure {
                    "closure".to_string()
                } else {
                    "function".to_string()
                }
            }
        };
        let vtable_name = format!(
            "__vole_iface_vtable_{}_{}",
            ctx.interner().resolve(interface_name),
            type_name
        );
        let data_id = ctx
            .jit_module()
            .declare_data(&vtable_name, Linkage::Local, false, false)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

        tracing::debug!(
            interface = %ctx.interner().resolve(interface_name),
            concrete_type = ?concrete_type_id,
            method_count = method_ids.len(),
            "declared vtable (phase 1)"
        );

        // Store pending state (concrete_type_id already a TypeId)
        self.pending.insert(
            key,
            VtableBuildState {
                data_id,
                interface_name_id,
                concrete_type: concrete_type_id,
                substitutions,
                method_ids,
            },
        );

        Ok(data_id)
    }

    /// Phase 2+3: Ensure a vtable is fully compiled.
    /// Must be called after get_or_declare() for the same key.
    #[tracing::instrument(skip(self, ctx), fields(interface = %ctx.interner().resolve(interface_name)))]
    pub(crate) fn ensure_compiled<C: VtableCtx>(
        &mut self,
        ctx: &mut C,
        interface_name: Symbol,
        concrete_type_id: TypeId,
    ) -> CodegenResult<DataId> {
        // Build key for lookup using arena unwraps
        let concrete_key = {
            let arena = ctx.arena();
            if let Some((_, _, is_closure)) = arena.unwrap_function(concrete_type_id) {
                InterfaceConcreteType::Function { is_closure }
            } else {
                let impl_type_id =
                    ImplTypeId::from_type_id(concrete_type_id, arena, ctx.registry()).ok_or_else(
                        || {
                            format!(
                                "cannot build vtable for unsupported type {:?}",
                                concrete_type_id
                            )
                        },
                    )?;
                InterfaceConcreteType::ImplTypeId(impl_type_id)
            }
        };
        // Resolve interface name to string for key (Symbol is interner-specific)
        let interface_name_str = ctx.interner().resolve(interface_name).to_string();
        let key = InterfaceVtableKey {
            interface_name: interface_name_str.clone(),
            concrete: concrete_key,
        };

        // Return if already completed
        if let Some(data_id) = self.vtables.get(&key) {
            return Ok(*data_id);
        }

        // Get pending state
        let state = self
            .pending
            .remove(&key)
            .ok_or_else(|| "vtable not declared - call get_or_declare first".to_string())?;

        let word_bytes = ctx.ptr_type().bytes() as usize;

        // Phase 2: Compile wrappers
        let mut data = DataDescription::new();
        data.define_zeroinit(word_bytes * state.method_ids.len());
        data.set_align(word_bytes as u64);

        // For Iterator<T> interfaces, compute the elem type tag from the
        // substitution for the first type parameter (T) so that the vtable
        // thunk can set it on the created RcIterator.
        let iter_elem_tag: Option<u64> = if interface_name_str == "Iterator" {
            state
                .substitutions
                .values()
                .next()
                .map(|&elem_type_id| crate::types::unknown_type_tag(elem_type_id, ctx.arena()))
        } else {
            None
        };

        for (index, &method_id) in state.method_ids.iter().enumerate() {
            let method = ctx.query().get_method(method_id);
            let method_name_str = ctx.analyzed().name_table().display(method.name_id);
            let target = resolve_vtable_target(
                ctx,
                state.interface_name_id,
                state.concrete_type,
                method_id,
                &state.substitutions,
            )?;
            let wrapper_id = self.compile_wrapper(
                ctx,
                &interface_name_str,
                &method_name_str,
                state.concrete_type,
                &target,
                iter_elem_tag,
            )?;
            let func_ref = ctx.jit_module().declare_func_in_data(wrapper_id, &mut data);
            data.write_function_addr((index * word_bytes) as u32, func_ref);
            let target_type = match &target.target {
                VtableMethodTarget::Method(_) => "Method",
                VtableMethodTarget::External(_) => "External",
                VtableMethodTarget::Function => "Function",
            };
            tracing::debug!(
                slot = index,
                method = %method_name_str,
                target = target_type,
                wrapper = ?wrapper_id,
                "vtable slot (phase 2)"
            );
        }

        // Phase 3: Define data
        ctx.jit_module()
            .define_data(state.data_id, &data)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

        tracing::debug!(
            interface = %interface_name_str,
            "completed vtable (phase 3)"
        );

        self.vtables.insert(key, state.data_id);
        Ok(state.data_id)
    }

    fn compile_wrapper<C: VtableCtx>(
        &mut self,
        ctx: &mut C,
        interface_name: &str,
        method_name: &str,
        concrete_type_id: TypeId,
        method: &VtableMethod,
        iter_elem_tag: Option<u64>,
    ) -> CodegenResult<cranelift_module::FuncId> {
        // Build wrapper signature using param_count and returns_void directly
        let word_type = ctx.ptr_type();
        let mut sig = ctx.jit_module().make_signature();
        sig.params.push(AbiParam::new(word_type)); // self
        for _ in 0..method.param_count {
            sig.params.push(AbiParam::new(word_type));
        }
        if !method.returns_void {
            sig.returns.push(AbiParam::new(word_type));
        }

        let wrapper_name = format!(
            "__vole_iface_wrap_{}_{}_{}",
            interface_name, method_name, self.wrapper_counter
        );
        self.wrapper_counter += 1;

        let func_id = ctx
            .jit_module()
            .declare_function(&wrapper_name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

        let mut func_ctx = ctx.jit_module().make_context();
        func_ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let params = builder.block_params(entry).to_vec();
            // self_word is now the boxed interface pointer [data_ptr, vtable_ptr]
            // We need to extract data_ptr for most targets
            let box_ptr = params[0];
            let data_word = builder.ins().load(word_type, MemFlags::new(), box_ptr, 0);

            // Dispatch to target-specific wrapper compilation
            let results = match &method.target {
                VtableMethodTarget::Function => compile_function_wrapper(
                    &mut builder,
                    ctx,
                    concrete_type_id,
                    data_word,
                    &params,
                    &method.param_type_ids,
                )?,
                VtableMethodTarget::Method(method_info) => compile_method_wrapper(
                    &mut builder,
                    ctx,
                    concrete_type_id,
                    data_word,
                    &params,
                    method_info,
                    &method.param_type_ids,
                )?,
                VtableMethodTarget::External(external_info) => compile_external_wrapper(
                    &mut builder,
                    ctx,
                    concrete_type_id,
                    data_word,
                    box_ptr,
                    &params,
                    external_info,
                    interface_name,
                    &method.param_type_ids,
                    method.return_type_id,
                    iter_elem_tag,
                )?,
            };

            // Handle return value
            if method.returns_void {
                builder.ins().return_(&[]);
            } else {
                let Some(result) = results.first().copied() else {
                    return Err(CodegenError::internal(
                        "interface wrapper missing return value",
                    ));
                };

                // If the return type is a union, the callee returned a pointer to
                // its own stack frame. We must copy tag+payload into heap-allocated
                // storage so the pointer survives after this wrapper returns.
                // value_to_word's fast-path assumes pointer-typed values are already
                // heap-boxed, so we handle union boxing explicitly here.
                if ctx.arena().is_union(method.return_type_id) {
                    let ptr_type = ctx.ptr_type();
                    let union_size =
                        type_id_size(method.return_type_id, ptr_type, ctx.registry(), ctx.arena());

                    // First copy to wrapper-local stack so callee memory is safe to
                    // reference while we call heap_alloc below.
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        union_size,
                        0,
                    ));
                    let tag = builder.ins().load(types::I8, MemFlags::new(), result, 0);

                    // Remap the tag if the callee used a different union variant ordering
                    // (generic implement blocks: callee has `Done | T` but wrapper expects
                    // `i64 | Done` ordering).
                    let remapped_tag = if let Some(remap) = &method.union_tag_remap {
                        remap_union_tag(&mut builder, tag, remap)
                    } else {
                        tag
                    };

                    builder.ins().stack_store(remapped_tag, slot, 0);
                    if union_size > 8 {
                        let payload = builder.ins().load(types::I64, MemFlags::new(), result, 8);
                        builder.ins().stack_store(payload, slot, 8);
                    }

                    // Heap-allocate and copy from local stack to heap.
                    let heap_alloc_ref = runtime_heap_alloc_ref(ctx, &mut builder)?;
                    let size_val = builder.ins().iconst(ptr_type, union_size as i64);
                    let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
                    let heap_ptr = builder.inst_results(alloc_call)[0];

                    let local_tag = builder.ins().stack_load(types::I8, slot, 0);
                    builder.ins().store(MemFlags::new(), local_tag, heap_ptr, 0);
                    if union_size > 8 {
                        let local_payload = builder.ins().stack_load(types::I64, slot, 8);
                        builder
                            .ins()
                            .store(MemFlags::new(), local_payload, heap_ptr, 8);
                    }

                    builder.ins().return_(&[heap_ptr]);
                } else {
                    let heap_alloc_ref = runtime_heap_alloc_ref(ctx, &mut builder)?;
                    let arena = ctx.arena();
                    let word = value_to_word(
                        &mut builder,
                        &CompiledValue::new(
                            result,
                            type_id_to_cranelift(method.return_type_id, arena, ctx.ptr_type()),
                            method.return_type_id,
                        ),
                        ctx.ptr_type(),
                        Some(heap_alloc_ref),
                        ctx.arena(),
                        ctx.registry(),
                    )?;
                    builder.ins().return_(&[word]);
                }
            }

            builder.finalize();
        }

        ctx.jit_module()
            .define_function(func_id, &mut func_ctx)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;
        ctx.jit_module().clear_context(&mut func_ctx);

        Ok(func_id)
    }
}

/// Compile wrapper body for Function target (closure/function pointer calls)
fn compile_function_wrapper<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    concrete_type_id: TypeId,
    data_word: Value,
    params: &[Value],
    param_type_ids: &[TypeId],
) -> CodegenResult<Vec<Value>> {
    // For function wrappers, concrete_type_id is the function type itself.
    // Try to extract is_closure and ret_type from it, falling back to defaults.
    let (ret_type_id, is_closure) = {
        let arena = ctx.arena();
        arena
            .unwrap_function(concrete_type_id)
            .map(|(_, ret, is_closure)| (ret, is_closure))
            .unwrap_or_else(|| (arena.void(), false))
    };

    let self_val = word_to_value_type_id(
        builder,
        data_word,
        concrete_type_id,
        ctx.ptr_type(),
        ctx.registry(),
        ctx.arena(),
    );
    let mut args = Vec::with_capacity(param_type_ids.len() + 1);
    for (param_word, &param_ty_id) in params[1..].iter().zip(param_type_ids.iter()) {
        args.push(word_to_value_type_id(
            builder,
            *param_word,
            param_ty_id,
            ctx.ptr_type(),
            ctx.registry(),
            ctx.arena(),
        ));
    }

    let void_id = ctx.arena().void();
    let (func_ptr, call_args, sig) = if is_closure {
        let closure_get_key = ctx
            .funcs()
            .runtime_key(RuntimeFn::ClosureGetFunc)
            .ok_or_else(|| "closure get func not registered".to_string())?;
        let closure_get_id = ctx
            .funcs()
            .func_id(closure_get_key)
            .ok_or_else(|| "closure get func id missing".to_string())?;
        let closure_get_ref = ctx
            .jit_module()
            .declare_func_in_func(closure_get_id, builder.func);
        let closure_call = builder.ins().call(closure_get_ref, &[self_val]);
        let func_ptr = builder.inst_results(closure_call)[0];

        let mut sig = ctx.jit_module().make_signature();
        let arena = ctx.arena();
        sig.params.push(AbiParam::new(type_id_to_cranelift(
            concrete_type_id,
            arena,
            ctx.ptr_type(),
        )));
        for &param_type_id in param_type_ids {
            sig.params.push(AbiParam::new(type_id_to_cranelift(
                param_type_id,
                arena,
                ctx.ptr_type(),
            )));
        }
        if ret_type_id != void_id {
            sig.returns.push(AbiParam::new(type_id_to_cranelift(
                ret_type_id,
                arena,
                ctx.ptr_type(),
            )));
        }

        let mut call_args = Vec::with_capacity(args.len() + 1);
        call_args.push(self_val);
        call_args.extend(args);
        (func_ptr, call_args, sig)
    } else {
        let mut sig = ctx.jit_module().make_signature();
        let arena = ctx.arena();
        for &param_type_id in param_type_ids {
            sig.params.push(AbiParam::new(type_id_to_cranelift(
                param_type_id,
                arena,
                ctx.ptr_type(),
            )));
        }
        if ret_type_id != void_id {
            sig.returns.push(AbiParam::new(type_id_to_cranelift(
                ret_type_id,
                arena,
                ctx.ptr_type(),
            )));
        }
        (self_val, args, sig)
    };

    let sig_ref = builder.import_signature(sig);
    let call = builder.ins().call_indirect(sig_ref, func_ptr, &call_args);
    Ok(builder.inst_results(call).to_vec())
}

/// Compile wrapper body for Direct/Implemented targets (direct method calls)
fn compile_method_wrapper<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    concrete_type_id: TypeId,
    data_word: Value,
    params: &[Value],
    method_info: &MethodInfo,
    param_type_ids: &[TypeId],
) -> CodegenResult<Vec<Value>> {
    let self_val = word_to_value_type_id(
        builder,
        data_word,
        concrete_type_id,
        ctx.ptr_type(),
        ctx.registry(),
        ctx.arena(),
    );
    let mut call_args = Vec::with_capacity(1 + param_type_ids.len());
    call_args.push(self_val);
    for (param_word, &param_ty_id) in params[1..].iter().zip(param_type_ids.iter()) {
        call_args.push(word_to_value_type_id(
            builder,
            *param_word,
            param_ty_id,
            ctx.ptr_type(),
            ctx.registry(),
            ctx.arena(),
        ));
    }
    let func_id = ctx
        .funcs()
        .func_id(method_info.func_key)
        .ok_or_else(|| "method function id not found".to_string())?;
    let func_ref = ctx.jit_module().declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &call_args);
    Ok(builder.inst_results(call).to_vec())
}

/// Compile wrapper body for External target (native/external function calls)
#[allow(clippy::too_many_arguments)]
fn compile_external_wrapper<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    concrete_type_id: TypeId,
    data_word: Value,
    box_ptr: Value,
    params: &[Value],
    external_info: &ExternalMethodInfo,
    interface_name: &str,
    param_type_ids: &[TypeId],
    return_type_id: TypeId,
    iter_elem_tag: Option<u64>,
) -> CodegenResult<Vec<Value>> {
    // For Iterator interface, wrap the boxed interface in a RcIterator
    // so external functions like vole_iter_collect can iterate via vtable.
    let self_val = if interface_name == "Iterator" {
        // Use tagged variant when we know the element type, so that terminal
        // methods (reduce, count, first, last) can determine RC cleanup needs.
        let (native_name, use_tag) = match iter_elem_tag {
            Some(tag) if tag != 0 => ("interface_iter_tagged", true),
            _ => ("interface_iter", false),
        };
        let interface_iter_ptr = ctx
            .native_registry()
            .lookup("vole:std:runtime", native_name)
            .ok_or_else(|| {
                format!(
                    "native function vole:std:runtime::{} not found",
                    native_name
                )
            })?
            .ptr;
        let mut iter_sig = ctx.jit_module().make_signature();
        iter_sig.params.push(AbiParam::new(ctx.ptr_type()));
        if use_tag {
            iter_sig.params.push(AbiParam::new(types::I64));
        }
        iter_sig.returns.push(AbiParam::new(ctx.ptr_type()));
        let iter_sig_ref = builder.import_signature(iter_sig);
        let iter_fn_ptr = builder
            .ins()
            .iconst(ctx.ptr_type(), interface_iter_ptr as i64);
        let iter_call = if use_tag {
            let tag_val = builder
                .ins()
                .iconst(types::I64, iter_elem_tag.unwrap() as i64);
            builder
                .ins()
                .call_indirect(iter_sig_ref, iter_fn_ptr, &[box_ptr, tag_val])
        } else {
            builder
                .ins()
                .call_indirect(iter_sig_ref, iter_fn_ptr, &[box_ptr])
        };
        builder.inst_results(iter_call)[0]
    } else {
        word_to_value_type_id(
            builder,
            data_word,
            concrete_type_id,
            ctx.ptr_type(),
            ctx.registry(),
            ctx.arena(),
        )
    };

    let mut call_args = Vec::with_capacity(1 + param_type_ids.len());
    call_args.push(self_val);
    for (param_word, &param_ty_id) in params[1..].iter().zip(param_type_ids.iter()) {
        call_args.push(word_to_value_type_id(
            builder,
            *param_word,
            param_ty_id,
            ctx.ptr_type(),
            ctx.registry(),
            ctx.arena(),
        ));
    }

    // Get string names from NameId
    let (module_path, native_name) =
        crate::context::resolve_external_names(ctx.analyzed().name_table(), external_info)?;

    // Extract just the pointer value to end the borrow before jit_module() call
    let native_func_ptr = ctx
        .native_registry()
        .lookup(&module_path, &native_name)
        .ok_or_else(|| format!("native function {}::{} not found", module_path, native_name))?
        .ptr;

    let mut native_sig = ctx.jit_module().make_signature();
    // For Iterator, the self param is now *mut RcIterator (pointer)
    let arena = ctx.arena();
    let self_param_type = if interface_name == "Iterator" {
        ctx.ptr_type()
    } else {
        type_id_to_cranelift(concrete_type_id, arena, ctx.ptr_type())
    };
    native_sig.params.push(AbiParam::new(self_param_type));
    // Use type_id_to_cranelift for param types (handles Invalid gracefully via fallback)
    for &param_type_id in param_type_ids {
        native_sig.params.push(AbiParam::new(type_id_to_cranelift(
            param_type_id,
            arena,
            ctx.ptr_type(),
        )));
    }
    // Add return type if not void
    let void_id = arena.void();
    if return_type_id != void_id {
        native_sig.returns.push(AbiParam::new(type_id_to_cranelift(
            return_type_id,
            arena,
            ctx.ptr_type(),
        )));
    }

    let sig_ref = builder.import_signature(native_sig);
    let func_ptr_val = builder.ins().iconst(ctx.ptr_type(), native_func_ptr as i64);
    let call = builder
        .ins()
        .call_indirect(sig_ref, func_ptr_val, &call_args);
    Ok(builder.inst_results(call).to_vec())
}

/// Look up an interface method slot using EntityRegistry (TypeDefId-based)
///
/// This uses TypeDefId and NameId to locate methods without string comparisons.
pub(crate) fn interface_method_slot_by_type_def_id(
    interface_id: TypeDefId,
    method_name_id: NameId,
    entity_registry: &EntityRegistry,
) -> CodegenResult<usize> {
    // Collect all methods from the interface and its parents
    let methods = collect_interface_methods_via_entity_registry(interface_id, entity_registry)?;

    // Find the method by its name_id
    methods
        .iter()
        .position(|method_id| {
            let method = entity_registry.get_method(*method_id);
            method.name_id == method_name_id
        })
        .ok_or_else(|| {
            CodegenError::not_found(
                "interface method",
                format!(
                    "name_id {:?} on interface {:?}",
                    method_name_id, interface_id
                ),
            )
        })
}

/// Collect all methods from an interface and its parent interfaces using EntityRegistry
///
/// Returns methods in a consistent order for vtable slot assignment.
/// Parent interface methods come first, then the interface's own methods.
/// This matches the order used by collect_interface_methods.
/// Collect all methods from an interface and its parent interfaces using EntityRegistry
pub(crate) fn collect_interface_methods_via_entity_registry(
    interface_id: TypeDefId,
    entity_registry: &EntityRegistry,
) -> CodegenResult<Vec<MethodId>> {
    let interface = entity_registry.get_type(interface_id);

    // Verify this is an interface
    if interface.kind != TypeDefKind::Interface {
        return Err(CodegenError::type_mismatch(
            "interface vtable",
            "interface",
            format!("{:?}", interface.kind),
        ));
    }

    let mut methods = Vec::new();
    let mut seen_interfaces = HashSet::new();
    let mut seen_methods = HashSet::new();

    collect_interface_methods_inner_entity_registry(
        interface_id,
        entity_registry,
        &mut methods,
        &mut seen_interfaces,
        &mut seen_methods,
    );

    Ok(methods)
}

fn collect_interface_methods_inner_entity_registry(
    interface_id: TypeDefId,
    entity_registry: &EntityRegistry,
    methods: &mut Vec<MethodId>,
    seen_interfaces: &mut HashSet<TypeDefId>,
    seen_methods: &mut HashSet<NameId>,
) {
    if !seen_interfaces.insert(interface_id) {
        return;
    }

    let interface = entity_registry.get_type(interface_id);

    // Process parent interfaces first (to match the order of collect_interface_methods)
    for parent_id in interface.extends.clone() {
        collect_interface_methods_inner_entity_registry(
            parent_id,
            entity_registry,
            methods,
            seen_interfaces,
            seen_methods,
        );
    }

    // Add this interface's methods
    for method_id in &interface.methods {
        let method = entity_registry.get_method(*method_id);
        if seen_methods.insert(method.name_id) {
            methods.push(*method_id);
        }
    }
}

/// Box a value as an interface type using TypeId.
///
/// Takes split parameters to allow calling from Cg methods without borrow conflicts.
/// Use box_interface_value_id_cg() for Cg callers or box_interface_value_id_vtable() for generic callers.
#[tracing::instrument(skip(builder, codegen_ctx, env, value), fields(interface_type_id = ?interface_type_id))]
pub(crate) fn box_interface_value_id<'a, 'ctx>(
    builder: &mut FunctionBuilder,
    codegen_ctx: &'a mut CodegenCtx<'ctx>,
    env: &'a CompileEnv<'ctx>,
    value: CompiledValue,
    interface_type_id: TypeId,
) -> CodegenResult<CompiledValue> {
    // Extract interface info using arena
    let (type_def_id, type_args_ids) = {
        let arena = env.analyzed.type_arena();
        match arena.unwrap_interface(interface_type_id) {
            Some((type_def_id, type_args)) => (type_def_id, type_args.to_vec()),
            None => return Ok(value), // Not an interface type
        }
    };

    // Look up the interface Symbol name via EntityRegistry
    let interface_def = env.analyzed.query().get_type(type_def_id);
    let interface_name_str = env
        .analyzed
        .name_table()
        .last_segment_str(interface_def.name_id)
        .ok_or_else(|| format!("cannot get interface name string for {:?}", type_def_id))?;
    let interface_name = env.interner.lookup(&interface_name_str).ok_or_else(|| {
        format!(
            "interface name '{}' not found in interner",
            interface_name_str
        )
    })?;

    // Check if value is already an interface
    if env.analyzed.type_arena().is_interface(value.type_id) {
        tracing::debug!("already interface, skip boxing");
        return Ok(value);
    }

    // Check if this is an external-only interface
    if env.analyzed.entity_registry().is_external_only(type_def_id) {
        tracing::debug!("external-only interface, skip boxing");
        return Ok(CompiledValue::new(
            value.value,
            codegen_ctx.ptr_type(),
            interface_type_id,
        ));
    }

    // Create a VtableCtxView for operations that need VtableCtx
    let mut ctx_view = VtableCtxView::new(codegen_ctx, env);
    let heap_alloc_ref = runtime_heap_alloc_ref(&mut ctx_view, builder)?;
    let data_word = value_to_word(
        builder,
        &value,
        ctx_view.ptr_type(),
        Some(heap_alloc_ref),
        ctx_view.arena(),
        ctx_view.registry(),
    )?;

    // Phase 1: Declare vtable
    let vtable_id = env.state.interface_vtables.borrow_mut().get_or_declare(
        &mut ctx_view,
        interface_name,
        type_def_id,
        &type_args_ids,
        value.type_id,
    )?;
    // Phase 2+3: Compile wrappers and define vtable data
    env.state.interface_vtables.borrow_mut().ensure_compiled(
        &mut ctx_view,
        interface_name,
        value.type_id,
    )?;
    let vtable_gv = ctx_view
        .jit_module()
        .declare_data_in_func(vtable_id, builder.func);
    let vtable_ptr = builder.ins().global_value(ctx_view.ptr_type(), vtable_gv);

    let word_bytes = ctx_view.ptr_type().bytes() as i64;
    let size_val = builder.ins().iconst(ctx_view.ptr_type(), word_bytes * 2);
    let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
    let iface_ptr = builder.inst_results(alloc_call)[0];

    builder
        .ins()
        .store(MemFlags::new(), data_word, iface_ptr, 0);
    builder
        .ins()
        .store(MemFlags::new(), vtable_ptr, iface_ptr, word_bytes as i32);

    Ok(CompiledValue::new(
        iface_ptr,
        ctx_view.ptr_type(),
        interface_type_id,
    ))
}

fn resolve_vtable_target<C: VtableCtx>(
    ctx: &C,
    interface_name_id: NameId,
    concrete_type_id: TypeId,
    interface_method_id: MethodId,
    substitutions: &FxHashMap<NameId, TypeId>,
) -> CodegenResult<VtableMethod> {
    // Get method info from EntityRegistry
    let interface_method = ctx.query().get_method(interface_method_id);
    let method_name_str = ctx
        .analyzed()
        .name_table()
        .display(interface_method.name_id);

    // Apply substitutions to get concrete param/return types (read-only lookup).
    // This may fail for generic classes implementing interfaces (e.g. Foo<K> implements
    // Iterator<K>) because the concrete substituted types (i64 | Done) may not exist
    // in the arena. In that case, we fall through to the direct method or implement
    // registry paths which provide their own concrete types.
    let substituted_types: Option<(Vec<TypeId>, TypeId)> = {
        let arena = ctx.arena();
        let (params, ret, _) = arena
            .unwrap_function(interface_method.signature_id)
            .expect("INTERNAL: vtable method: signature is not a function type");
        let param_ids: Option<Vec<TypeId>> = params
            .iter()
            .map(|&p| arena.lookup_substitute(p, substitutions))
            .collect();
        let ret_id = arena.lookup_substitute(ret, substitutions);
        param_ids.zip(ret_id)
    };

    // Check if concrete type is a function/closure
    let fn_info = ctx
        .arena()
        .unwrap_function(concrete_type_id)
        .map(|(params, ret, is_closure)| (params.to_vec(), ret, is_closure));
    if let Some((param_ids, return_id, _)) = fn_info {
        let arena = ctx.arena();
        let returns_void = matches!(arena.get(return_id), SemaType::Void);
        return Ok(VtableMethod {
            param_count: param_ids.len(),
            returns_void,
            param_type_ids: param_ids,
            return_type_id: return_id,
            union_tag_remap: None,
            target: VtableMethodTarget::Function,
        });
    }

    let impl_type_id = ImplTypeId::from_type_id(concrete_type_id, ctx.arena(), ctx.registry())
        .ok_or_else(|| {
            format!(
                "cannot resolve interface method {} on type {:?}",
                method_name_str, concrete_type_id
            )
        })?;
    // Use string-based lookup for cross-interner safety (method_def is from stdlib interner)
    // This may return None for default interface methods that aren't explicitly implemented
    let method_name_id = method_name_id_by_str(ctx.analyzed(), ctx.interner(), &method_name_str);

    // Check implement registry for explicit implementations
    if let Some(method_name_id) = method_name_id
        && let Some(impl_) = ctx
            .analyzed()
            .implement_registry()
            .get_method(&impl_type_id, method_name_id)
    {
        // Use substituted types when available (required for generic implement blocks
        // where the registry stores abstract types like `T | Done` but we need concrete
        // types like `i64 | Done` for correct union tag ordering in vtable wrappers).
        let (param_type_ids, return_type_id) = substituted_types.unwrap_or_else(|| {
            (
                impl_.func_type.params_id.to_vec(),
                impl_.func_type.return_type_id,
            )
        });
        let returns_void = matches!(ctx.arena().get(return_type_id), SemaType::Void);
        // Build a tag remapping table when the callee's return type (abstract, e.g. `Done | T`)
        // differs from the concrete return type (e.g. `i64 | Done`). The callee was compiled
        // with the abstract union's tag ordering, but the wrapper must produce the concrete
        // union's tag ordering.
        let callee_ret = impl_.func_type.return_type_id;
        let union_tag_remap =
            build_union_tag_remap(ctx.arena(), callee_ret, return_type_id, substitutions);
        tracing::warn!(
            method = %method_name_str,
            callee_ret = ?callee_ret,
            callee_ret_display = %ctx.arena().display_basic(callee_ret),
            return_type = ?return_type_id,
            return_type_display = %ctx.arena().display_basic(return_type_id),
            substitutions = ?substitutions.iter().map(|(k, v)| (k, ctx.arena().display_basic(*v))).collect::<Vec<_>>(),
            remap = ?union_tag_remap,
            "implement registry: tag remap check"
        );
        if let Some(external_info) = impl_.external_info {
            return Ok(VtableMethod {
                param_count: impl_.func_type.params_id.len(),
                returns_void,
                param_type_ids,
                return_type_id,
                union_tag_remap,
                target: VtableMethodTarget::External(external_info),
            });
        }
        // Look up via unified method_func_keys using type's NameId for stable lookup
        let type_name_id = impl_type_id.name_id();
        let func_key = *ctx
            .method_func_keys()
            .get(&(type_name_id, method_name_id))
            .ok_or_else(|| "implement method info not found in method_func_keys".to_string())?;
        let method_info = MethodInfo { func_key };
        return Ok(VtableMethod {
            param_count: impl_.func_type.params_id.len(),
            returns_void,
            param_type_ids,
            return_type_id,
            union_tag_remap,
            target: VtableMethodTarget::Method(method_info),
        });
    }

    // Check direct methods on class using TypeId-based lookup
    // Returns (method_info, param_type_ids, return_type_id)
    let direct_method_result: Option<(MethodInfo, Vec<TypeId>, TypeId)> = (|| {
        let method_name_id = method_name_id?;
        // Get type_def_id from concrete_type_id using arena unwraps
        let arena = ctx.arena();
        let type_def_id = arena.unwrap_class(concrete_type_id).map(|(id, _)| id)?;

        let type_name_id = ctx.query().get_type(type_def_id).name_id;
        let meta = type_metadata_by_name_id(
            ctx.type_metadata(),
            type_name_id,
            ctx.registry(),
            ctx.arena(),
        )?;
        let method_info = meta.method_infos.get(&method_name_id).copied()?;

        // Look up method signature via EntityRegistry - require TypeId fields
        let sig_from_entity = ctx
            .registry()
            .find_method_on_type(type_def_id, method_name_id)
            .and_then(|m_id| {
                let method = ctx.query().get_method(m_id);
                let arena = ctx.arena();
                let (params, ret, _) = arena.unwrap_function(method.signature_id)?;
                Some((params.to_vec(), ret))
            });
        // Use entity registry signature, fall back to substituted interface types
        let (param_ids, ret_id) = sig_from_entity
            .or_else(|| substituted_types.clone())
            .unwrap_or_else(|| {
                // Last resort: use original interface method's unsubstituted types.
                // This handles cases where both entity lookup and substitution fail.
                let arena = ctx.arena();
                let (params, ret, _) = arena
                    .unwrap_function(interface_method.signature_id)
                    .expect("INTERNAL: vtable method: signature is not a function type");
                (params.to_vec(), ret)
            });
        Some((method_info, param_ids, ret_id))
    })();

    if let Some((method_info, param_type_ids, return_type_id)) = direct_method_result {
        let returns_void = matches!(ctx.arena().get(return_type_id), SemaType::Void);
        return Ok(VtableMethod {
            param_count: param_type_ids.len(),
            returns_void,
            param_type_ids,
            return_type_id,
            union_tag_remap: None,
            target: VtableMethodTarget::Method(method_info),
        });
    }

    // Fall back to interface default if method has one
    if interface_method.has_default {
        // Check for default external binding via EntityRegistry
        if let Some(interface_type_def_id) = ctx.registry().type_by_name(interface_name_id)
            && let Some(method_name_id) = method_name_id
            && let Some(found_method_id) = ctx
                .registry()
                .find_method_on_type(interface_type_def_id, method_name_id)
            && let Some(external_info) = ctx.registry().get_external_binding(found_method_id)
        {
            // For external bindings, use the original interface method signature.
            // The Rust implementation handles type dispatch, so we don't need substituted types.
            let (param_type_ids, return_type_id) = {
                let arena = ctx.arena();
                let (params, ret, _) = arena
                    .unwrap_function(interface_method.signature_id)
                    .expect("INTERNAL: interface vtable: method signature is not a function type");
                (params.to_vec(), ret)
            };
            let returns_void = matches!(ctx.arena().get(return_type_id), SemaType::Void);
            return Ok(VtableMethod {
                param_count: param_type_ids.len(),
                returns_void,
                param_type_ids,
                return_type_id,
                union_tag_remap: None,
                target: VtableMethodTarget::External(*external_info),
            });
        }
        // TODO: Handle Vole body defaults when interface method bodies are supported
    }

    Err(CodegenError::not_found(
        "method implementation",
        format!("{} on type {:?}", method_name_str, concrete_type_id),
    ))
}

/// Build a tag remapping table for union returns from generic implement blocks.
///
/// Handles two cases:
/// 1. **Concrete substitution**: callee uses `Done | T` (abstract) but wrapper expects
///    `i64 | Done` (concrete). Tags differ because TypeParam(sort=40) < Sentinel(sort=50)
///    but Primitive(sort=100) > Sentinel(sort=50).
/// 2. **Abstract with TypeParams**: callee and wrapper use different abstract unions
///    (e.g., callee has `Done | K` but concrete is `i64 | Done`). When substitution
///    resolves TypeParam to another TypeParam, match non-TypeParam variants by identity
///    and assign remaining positions to TypeParam variants.
///
/// Returns `None` if no remapping is needed (identity mapping).
fn build_union_tag_remap(
    arena: &vole_sema::type_arena::TypeArena,
    callee_type_id: TypeId,
    concrete_type_id: TypeId,
    substitutions: &FxHashMap<NameId, TypeId>,
) -> Option<Vec<u8>> {
    let callee_variants = arena.unwrap_union(callee_type_id)?;

    if callee_type_id == concrete_type_id {
        // Same type: check for TypeParam misordering.
        // TypeParams (sort=40) sort after sentinels (sort=50) in abstract unions,
        // but at runtime become concrete types that sort before sentinels.
        let has_type_params = callee_variants
            .iter()
            .any(|&v| matches!(arena.get(v), SemaType::TypeParam(_)));
        if !has_type_params {
            return None;
        }
        // TypeParam variants should get low tags (values), non-TypeParam get high tags (sentinels)
        let mut type_param_indices: Vec<usize> = Vec::new();
        let mut non_type_param_indices: Vec<usize> = Vec::new();
        for (i, &v) in callee_variants.iter().enumerate() {
            if matches!(arena.get(v), SemaType::TypeParam(_)) {
                type_param_indices.push(i);
            } else {
                non_type_param_indices.push(i);
            }
        }
        let mut remap = vec![0u8; callee_variants.len()];
        let mut target_tag = 0u8;
        for &i in &type_param_indices {
            remap[i] = target_tag;
            target_tag += 1;
        }
        for &i in &non_type_param_indices {
            remap[i] = target_tag;
            target_tag += 1;
        }
        let is_identity = remap.iter().enumerate().all(|(i, &t)| t == i as u8);
        return if is_identity { None } else { Some(remap) };
    }

    // Different types: callee and concrete have different union layouts.
    let concrete_variants = arena.unwrap_union(concrete_type_id)?;
    if callee_variants.len() != concrete_variants.len() {
        return None;
    }

    let mut remap = Vec::with_capacity(callee_variants.len());
    let mut is_identity = true;

    // Track which concrete positions are taken
    let mut used_concrete: Vec<bool> = vec![false; concrete_variants.len()];

    // First pass: match non-TypeParam callee variants by identity in concrete union
    let mut pending_type_params: Vec<usize> = Vec::new();
    for (callee_tag, &callee_variant) in callee_variants.iter().enumerate() {
        match arena.get(callee_variant) {
            SemaType::TypeParam(name_id) => {
                // Try to resolve via substitution
                let resolved = substitutions.get(name_id).copied();
                let is_still_type_param = resolved
                    .map(|r| matches!(arena.get(r), SemaType::TypeParam(_)))
                    .unwrap_or(true);
                if is_still_type_param {
                    // Can't resolve to concrete, defer
                    pending_type_params.push(callee_tag);
                    remap.push(0); // placeholder
                } else if let Some(concrete_variant) = resolved {
                    if let Some(pos) = concrete_variants
                        .iter()
                        .position(|&v| v == concrete_variant)
                    {
                        used_concrete[pos] = true;
                        if callee_tag != pos {
                            is_identity = false;
                        }
                        remap.push(pos as u8);
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            }
            _ => {
                // Match by TypeId identity
                if let Some(pos) = concrete_variants.iter().position(|&v| v == callee_variant) {
                    used_concrete[pos] = true;
                    if callee_tag != pos {
                        is_identity = false;
                    }
                    remap.push(pos as u8);
                } else {
                    return None;
                }
            }
        }
    }

    // Second pass: assign remaining concrete positions to unresolved TypeParam variants
    if !pending_type_params.is_empty() {
        let free_positions: Vec<usize> = used_concrete
            .iter()
            .enumerate()
            .filter(|(_, used)| !*used)
            .map(|(i, _)| i)
            .collect();
        if free_positions.len() != pending_type_params.len() {
            return None;
        }
        for (&callee_tag, &concrete_pos) in pending_type_params.iter().zip(free_positions.iter()) {
            if callee_tag != concrete_pos {
                is_identity = false;
            }
            remap[callee_tag] = concrete_pos as u8;
        }
    }

    if is_identity { None } else { Some(remap) }
}

/// Emit Cranelift IR to remap a union tag byte using a compile-time remap table.
///
/// For the common 2-variant case (e.g., `[1, 0]`), emits a simple select:
///   remapped = select (tag == 0), remap[0], remap[1]
/// For larger unions, chains select instructions.
fn remap_union_tag(builder: &mut FunctionBuilder, tag: Value, remap: &[u8]) -> Value {
    assert!(!remap.is_empty(), "empty tag remap table");
    // Start with the last entry as the default, then chain selects backwards
    let mut result = builder
        .ins()
        .iconst(types::I8, remap[remap.len() - 1] as i64);
    for i in (0..remap.len() - 1).rev() {
        let cmp_val = builder.ins().iconst(types::I8, i as i64);
        let is_match = builder.ins().icmp(IntCC::Equal, tag, cmp_val);
        let mapped = builder.ins().iconst(types::I8, remap[i] as i64);
        result = builder.ins().select(is_match, mapped, result);
    }
    result
}

fn runtime_heap_alloc_ref<C: VtableCtx>(
    ctx: &mut C,
    builder: &mut FunctionBuilder,
) -> CodegenResult<FuncRef> {
    let key = ctx
        .funcs()
        .runtime_key(RuntimeFn::HeapAlloc)
        .ok_or_else(|| "heap allocator not registered".to_string())?;
    let func_id = ctx
        .funcs()
        .func_id(key)
        .ok_or_else(|| "heap allocator function id missing".to_string())?;
    Ok(ctx.jit_module().declare_func_in_func(func_id, builder.func))
}
