use rustc_hash::FxHashMap;
use std::collections::HashSet;

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};

use super::vtable_ctx::{VtableCtx, VtableCtxView};
use crate::RuntimeKey;
use crate::calls::string_ops::{declare_string_data, reference_string_data};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CodegenCtx, CompileEnv};
use crate::types::{
    CompiledValue, MethodInfo, method_name_id_by_str, type_id_size, type_id_to_cranelift,
    type_metadata_by_name_id, value_to_word, word_to_value_type_id,
};
use crate::union_layout;
use vole_frontend::Symbol;
use vole_identity::{MethodId, NameId, TypeDefId};
use vole_sema::EntityRegistry;
use vole_sema::implement_registry::{ExternalMethodInfo, ImplTypeId};
use vole_sema::type_arena::{SemaType, TypeId};

/// Vtable slot 0 is reserved for the meta getter function pointer.
/// Method slots start at index 1.
pub(crate) const VTABLE_META_SLOT: usize = 0;
/// Offset applied to method indices to account for the meta getter at slot 0.
pub(crate) const VTABLE_METHOD_OFFSET: usize = 1;

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
    /// TypeDefId of the interface (for well-known type checks)
    interface_type_def_id: TypeDefId,
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

/// Iterator-specific vtable info passed from `ensure_compiled` to wrapper compilation.
/// `None` means the interface is not Iterator.
/// `Some(tag)` means Iterator with optional element type tag.
type IteratorVtableInfo = Option<Option<u64>>;

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
            if let Some((_, _, is_closure)) = ctx.arena().unwrap_function(concrete_type_id) {
                InterfaceConcreteType::Function { is_closure }
            } else {
                let impl_type_id = impl_type_id_ctx(concrete_type_id, ctx).ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "cannot build vtable for unsupported type",
                        format!("{:?}", concrete_type_id),
                    )
                })?;
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
        let method_ids = collect_interface_methods_ctx(interface_type_def_id, ctx)?;

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
            .map_err(CodegenError::cranelift)?;

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
                interface_type_def_id,
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
            if let Some((_, _, is_closure)) = ctx.arena().unwrap_function(concrete_type_id) {
                InterfaceConcreteType::Function { is_closure }
            } else {
                let impl_type_id = impl_type_id_ctx(concrete_type_id, ctx).ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "cannot build vtable for unsupported type",
                        format!("{:?}", concrete_type_id),
                    )
                })?;
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
            .ok_or_else(|| CodegenError::missing_resource("vtable"))?;

        let word_bytes = ctx.ptr_type().bytes() as usize;

        // Phase 2: Compile wrappers
        // Slot 0 is reserved for the meta getter function pointer.
        // Method wrappers occupy slots 1..n+1.
        let total_slots = VTABLE_METHOD_OFFSET + state.method_ids.len();
        let mut data = DataDescription::new();
        data.define_zeroinit(word_bytes * total_slots);
        data.set_align(word_bytes as u64);

        // Compile the meta getter and write it at slot 0.
        let meta_getter_id =
            self.compile_meta_getter(ctx, &interface_name_str, state.concrete_type)?;
        let meta_func_ref = ctx
            .jit_module()
            .declare_func_in_data(meta_getter_id, &mut data);
        data.write_function_addr((VTABLE_META_SLOT * word_bytes) as u32, meta_func_ref);
        tracing::debug!(
            slot = VTABLE_META_SLOT,
            wrapper = ?meta_getter_id,
            "vtable meta getter (phase 2)"
        );

        // For Iterator<T> interfaces, compute the elem type tag from the
        // substitution for the first type parameter (T) so that the vtable
        // thunk can set it on the created RcIterator.
        let iterator_info: IteratorVtableInfo =
            if ctx
                .analyzed()
                .name_table()
                .well_known
                .is_iterator_type_def(state.interface_type_def_id)
            {
                Some(
                    state.substitutions.values().next().map(|&elem_type_id| {
                        crate::types::unknown_type_tag(elem_type_id, ctx.arena())
                    }),
                )
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
                iterator_info,
            )?;
            let vtable_slot = index + VTABLE_METHOD_OFFSET;
            let func_ref = ctx.jit_module().declare_func_in_data(wrapper_id, &mut data);
            data.write_function_addr((vtable_slot * word_bytes) as u32, func_ref);
            let target_type = match &target.target {
                VtableMethodTarget::Method(_) => "Method",
                VtableMethodTarget::External(_) => "External",
                VtableMethodTarget::Function => "Function",
            };
            tracing::debug!(
                slot = vtable_slot,
                method = %method_name_str,
                target = target_type,
                wrapper = ?wrapper_id,
                "vtable slot (phase 2)"
            );
        }

        // Phase 3: Define data
        ctx.jit_module()
            .define_data(state.data_id, &data)
            .map_err(CodegenError::cranelift)?;

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
        iterator_info: IteratorVtableInfo,
    ) -> CodegenResult<FuncId> {
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
            .map_err(CodegenError::cranelift)?;

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
                    iterator_info,
                    &method.param_type_ids,
                    method.return_type_id,
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
                    let union_size = type_size_ctx(method.return_type_id, ctx);

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
                    if union_size > union_layout::TAG_ONLY_SIZE {
                        let payload = builder.ins().load(
                            types::I64,
                            MemFlags::new(),
                            result,
                            union_layout::PAYLOAD_OFFSET,
                        );
                        builder
                            .ins()
                            .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
                    }

                    // Heap-allocate and copy from local stack to heap.
                    let heap_alloc_ref = runtime_heap_alloc_ref(ctx, &mut builder)?;
                    let size_val = builder.ins().iconst(ptr_type, union_size as i64);
                    let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
                    let heap_ptr = builder.inst_results(alloc_call)[0];

                    let local_tag = builder.ins().stack_load(types::I8, slot, 0);
                    builder.ins().store(MemFlags::new(), local_tag, heap_ptr, 0);
                    if union_size > union_layout::TAG_ONLY_SIZE {
                        let local_payload = builder.ins().stack_load(
                            types::I64,
                            slot,
                            union_layout::PAYLOAD_OFFSET,
                        );
                        builder.ins().store(
                            MemFlags::new(),
                            local_payload,
                            heap_ptr,
                            union_layout::PAYLOAD_OFFSET,
                        );
                    }

                    builder.ins().return_(&[heap_ptr]);
                } else {
                    let heap_alloc_ref = runtime_heap_alloc_ref(ctx, &mut builder)?;
                    let compiled = {
                        let arena = ctx.arena();
                        CompiledValue::new(
                            result,
                            type_id_to_cranelift(method.return_type_id, arena, ctx.ptr_type()),
                            method.return_type_id,
                        )
                    };
                    let word =
                        value_to_word_ctx(&mut builder, &compiled, Some(heap_alloc_ref), ctx)?;
                    builder.ins().return_(&[word]);
                }
            }

            builder.finalize();
        }

        ctx.jit_module()
            .define_function(func_id, &mut func_ctx)
            .map_err(CodegenError::cranelift)?;
        ctx.jit_module().clear_context(&mut func_ctx);

        Ok(func_id)
    }

    /// Compile a meta getter function for a concrete type.
    ///
    /// The meta getter is a standalone JIT function `() -> *TypeMeta` that
    /// builds a TypeMeta instance containing the concrete type's name, field
    /// metadata, and constructor. It is stored at vtable slot 0 and called
    /// when `val.@meta` is accessed on an interface-typed value.
    ///
    /// For class/struct types, this includes full field metadata and a
    /// constructor trampoline. For function/closure types (used in functional
    /// interfaces), this produces a minimal TypeMeta with just the type name,
    /// empty fields, and a stub constructor.
    fn compile_meta_getter<C: VtableCtx>(
        &mut self,
        ctx: &mut C,
        interface_name: &str,
        concrete_type_id: TypeId,
    ) -> CodegenResult<FuncId> {
        let ptr_type = ctx.ptr_type();

        // Check if concrete type is a function/closure (functional interfaces)
        let is_function_type = ctx.arena().unwrap_function(concrete_type_id).is_some();

        if is_function_type {
            return self.compile_meta_getter_function(ctx, interface_name, concrete_type_id);
        }

        // --- Class/struct path: full fields and constructor ---

        // Resolve concrete type name and TypeDefId
        let (type_def_id, type_name) = resolve_concrete_type_name(ctx, concrete_type_id)?;

        // Resolve TypeMeta and FieldMeta class metadata
        let type_meta_info = resolve_reflection_meta(ctx)?;

        // Resolve all needed runtime FuncIds upfront
        let instance_new = resolve_runtime_in_vtable(ctx, RuntimeKey::InstanceNew)?;
        let instance_set = resolve_runtime_in_vtable(ctx, RuntimeKey::InstanceSetField)?;
        let array_new = resolve_runtime_in_vtable(ctx, RuntimeKey::ArrayNew)?;
        let array_push = resolve_runtime_in_vtable(ctx, RuntimeKey::ArrayPush)?;
        let instance_get = resolve_runtime_in_vtable(ctx, RuntimeKey::InstanceGetField)?;
        let heap_alloc = resolve_runtime_in_vtable(ctx, RuntimeKey::HeapAlloc)?;
        let closure_alloc = resolve_runtime_in_vtable(ctx, RuntimeKey::ClosureAlloc)?;
        let rc_inc = resolve_runtime_in_vtable(ctx, RuntimeKey::RcInc)?;
        let cache_get = resolve_runtime_in_vtable(ctx, RuntimeKey::TypeMetaCacheGet)?;
        let cache_store = resolve_runtime_in_vtable(ctx, RuntimeKey::TypeMetaCacheStore)?;

        // Collect field info from the concrete type
        let field_info = collect_concrete_field_info(ctx, type_def_id);

        // Compile getter, setter, and constructor trampolines as sub-functions
        let getter_ids = compile_getter_trampolines(ctx, &field_info, instance_get, heap_alloc)?;
        let setter_ids = compile_setter_trampolines(ctx, &field_info, instance_set)?;
        let ctor_id = compile_constructor_trampoline(
            ctx,
            type_def_id,
            instance_new,
            instance_set,
            heap_alloc,
        )?;

        // Pre-declare all string data BEFORE creating the FunctionBuilder.
        // Uses jit_module_and_funcs() to borrow both simultaneously, avoiding
        // the split-borrow issue where jit_module() and funcs() each need &mut self.
        let name_data_id = {
            let (module, funcs) = ctx.jit_module_and_funcs();
            declare_string_data(&type_name, module, funcs)?
        };
        let field_name_data_ids: Vec<DataId> = {
            let mut ids = Vec::with_capacity(field_info.len());
            for f in &field_info {
                let (module, funcs) = ctx.jit_module_and_funcs();
                ids.push(declare_string_data(&f.name, module, funcs)?);
            }
            ids
        };
        let field_type_name_data_ids: Vec<DataId> = {
            let mut ids = Vec::with_capacity(field_info.len());
            for f in &field_info {
                let (module, funcs) = ctx.jit_module_and_funcs();
                ids.push(declare_string_data(&f.type_name, module, funcs)?);
            }
            ids
        };

        // Get a unique cache key for this concrete type.
        // Classes use their nonzero runtime type_id; structs (type_id=0) get a
        // fresh unique ID so different struct types don't collide in the cache.
        let cache_key_id = ctx
            .type_metadata()
            .get(&type_def_id)
            .map(|m| m.type_id)
            .filter(|&id| id != 0)
            .unwrap_or_else(vole_runtime::type_registry::alloc_type_id);

        // Now compile the meta getter function itself
        let getter_name = format!(
            "__vole_iface_meta_{}_{}",
            interface_name, self.wrapper_counter
        );
        self.wrapper_counter += 1;

        let mut sig = ctx.jit_module().make_signature();
        sig.returns.push(AbiParam::new(ptr_type)); // returns TypeMeta ptr

        let func_id = ctx
            .jit_module()
            .declare_function(&getter_name, Linkage::Local, &sig)
            .map_err(CodegenError::cranelift)?;

        let mut func_ctx = ctx.jit_module().make_context();
        func_ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            // Emit lazy-init cache check (hot path already wired).
            let (_cold_block, merge_block) =
                emit_meta_cache_check(&mut builder, ctx, cache_key_id, cache_get, rc_inc);

            // --- Cold path: build TypeMeta and cache it ---

            // Allocate TypeMeta instance
            let type_meta_ptr = emit_alloc_instance(
                &mut builder,
                ctx.jit_module(),
                instance_new,
                ptr_type,
                type_meta_info.type_meta_type_id_val,
                type_meta_info.type_meta_field_count,
            );

            // Reference pre-declared name string and store it
            let name_val =
                reference_string_data(&mut builder, name_data_id, ptr_type, ctx.jit_module());
            emit_set_field(
                &mut builder,
                ctx.jit_module(),
                instance_set,
                type_meta_ptr,
                type_meta_info.name_slot,
                name_val,
                ptr_type,
            );

            // Build fields array with FieldMeta entries
            let fields_ptr = emit_build_field_array(
                &mut builder,
                ctx,
                &type_meta_info,
                &field_info,
                &field_name_data_ids,
                &field_type_name_data_ids,
                &getter_ids,
                &setter_ids,
                instance_new,
                instance_set,
                array_new,
                array_push,
                closure_alloc,
            );
            emit_set_field(
                &mut builder,
                ctx.jit_module(),
                instance_set,
                type_meta_ptr,
                type_meta_info.fields_slot,
                fields_ptr,
                ptr_type,
            );

            // Build constructor closure and store
            let ctor_fn_ref = ctx.jit_module().declare_func_in_func(ctor_id, builder.func);
            let ctor_addr = builder.ins().func_addr(ptr_type, ctor_fn_ref);
            let closure_alloc_ref = ctx
                .jit_module()
                .declare_func_in_func(closure_alloc, builder.func);
            let zero = builder.ins().iconst(types::I64, 0);
            let ctor_call = builder.ins().call(closure_alloc_ref, &[ctor_addr, zero]);
            let ctor_closure = builder.inst_results(ctor_call)[0];
            emit_set_field(
                &mut builder,
                ctx.jit_module(),
                instance_set,
                type_meta_ptr,
                type_meta_info.construct_slot,
                ctor_closure,
                ptr_type,
            );

            // Store into cache and rc_inc for the caller.
            emit_meta_cache_store(
                &mut builder,
                ctx,
                cache_key_id,
                cache_store,
                rc_inc,
                type_meta_ptr,
                merge_block,
            );

            // Merge: return the TypeMeta pointer (from either path).
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);
            let result = builder.block_params(merge_block)[0];
            builder.ins().return_(&[result]);
            builder.finalize();
        }

        ctx.jit_module()
            .define_function(func_id, &mut func_ctx)
            .map_err(CodegenError::cranelift)?;
        ctx.jit_module().clear_context(&mut func_ctx);

        Ok(func_id)
    }

    /// Compile a minimal meta getter for function/closure concrete types.
    ///
    /// Function types have no fields and no meaningful constructor, so this
    /// produces a TypeMeta with name "function"/"closure", empty fields array,
    /// and a stub constructor that panics with "cannot construct function type".
    fn compile_meta_getter_function<C: VtableCtx>(
        &mut self,
        ctx: &mut C,
        interface_name: &str,
        concrete_type_id: TypeId,
    ) -> CodegenResult<FuncId> {
        let ptr_type = ctx.ptr_type();

        let (_, _, is_closure) = ctx
            .arena()
            .unwrap_function(concrete_type_id)
            .expect("INTERNAL: compile_meta_getter_function called for non-function type");
        let type_name = if is_closure { "closure" } else { "function" };

        let type_meta_info = resolve_reflection_meta(ctx)?;

        let instance_new = resolve_runtime_in_vtable(ctx, RuntimeKey::InstanceNew)?;
        let instance_set = resolve_runtime_in_vtable(ctx, RuntimeKey::InstanceSetField)?;
        let array_new = resolve_runtime_in_vtable(ctx, RuntimeKey::ArrayNew)?;
        let closure_alloc = resolve_runtime_in_vtable(ctx, RuntimeKey::ClosureAlloc)?;
        let rc_inc = resolve_runtime_in_vtable(ctx, RuntimeKey::RcInc)?;
        let cache_get = resolve_runtime_in_vtable(ctx, RuntimeKey::TypeMetaCacheGet)?;
        let cache_store = resolve_runtime_in_vtable(ctx, RuntimeKey::TypeMetaCacheStore)?;

        // Allocate a unique pseudo-type-id as cache key for function/closure types.
        let cache_key_id = vole_runtime::type_registry::alloc_type_id();

        // Compile a stub constructor that panics
        let ctor_id = compile_stub_constructor(ctx)?;

        // Pre-declare string data before the FunctionBuilder.
        let name_data_id = {
            let (module, funcs) = ctx.jit_module_and_funcs();
            declare_string_data(type_name, module, funcs)?
        };

        let getter_name = format!(
            "__vole_iface_meta_{}_{}",
            interface_name, self.wrapper_counter
        );
        self.wrapper_counter += 1;

        let mut sig = ctx.jit_module().make_signature();
        sig.returns.push(AbiParam::new(ptr_type));

        let func_id = ctx
            .jit_module()
            .declare_function(&getter_name, Linkage::Local, &sig)
            .map_err(CodegenError::cranelift)?;

        let mut func_ctx = ctx.jit_module().make_context();
        func_ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            // Emit lazy-init cache check (hot path already wired).
            let (_cold_block, merge_block) =
                emit_meta_cache_check(&mut builder, ctx, cache_key_id, cache_get, rc_inc);

            // --- Cold path: build TypeMeta and cache it ---

            // Allocate TypeMeta instance
            let type_meta_ptr = emit_alloc_instance(
                &mut builder,
                ctx.jit_module(),
                instance_new,
                ptr_type,
                type_meta_info.type_meta_type_id_val,
                type_meta_info.type_meta_field_count,
            );

            // Set name
            let name_val =
                reference_string_data(&mut builder, name_data_id, ptr_type, ctx.jit_module());
            emit_set_field(
                &mut builder,
                ctx.jit_module(),
                instance_set,
                type_meta_ptr,
                type_meta_info.name_slot,
                name_val,
                ptr_type,
            );

            // Empty fields array
            let arr_new_ref = ctx
                .jit_module()
                .declare_func_in_func(array_new, builder.func);
            let arr_call = builder.ins().call(arr_new_ref, &[]);
            let fields_ptr = builder.inst_results(arr_call)[0];
            emit_set_field(
                &mut builder,
                ctx.jit_module(),
                instance_set,
                type_meta_ptr,
                type_meta_info.fields_slot,
                fields_ptr,
                ptr_type,
            );

            // Stub constructor closure
            let ctor_fn_ref = ctx.jit_module().declare_func_in_func(ctor_id, builder.func);
            let ctor_addr = builder.ins().func_addr(ptr_type, ctor_fn_ref);
            let closure_alloc_ref = ctx
                .jit_module()
                .declare_func_in_func(closure_alloc, builder.func);
            let zero = builder.ins().iconst(types::I64, 0);
            let ctor_call = builder.ins().call(closure_alloc_ref, &[ctor_addr, zero]);
            let ctor_closure = builder.inst_results(ctor_call)[0];
            emit_set_field(
                &mut builder,
                ctx.jit_module(),
                instance_set,
                type_meta_ptr,
                type_meta_info.construct_slot,
                ctor_closure,
                ptr_type,
            );

            // Store into cache and rc_inc for the caller.
            emit_meta_cache_store(
                &mut builder,
                ctx,
                cache_key_id,
                cache_store,
                rc_inc,
                type_meta_ptr,
                merge_block,
            );

            // Merge: return the TypeMeta pointer (from either path).
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);
            let result = builder.block_params(merge_block)[0];
            builder.ins().return_(&[result]);
            builder.finalize();
        }

        ctx.jit_module()
            .define_function(func_id, &mut func_ctx)
            .map_err(CodegenError::cranelift)?;
        ctx.jit_module().clear_context(&mut func_ctx);

        Ok(func_id)
    }
}

/// Info about a concrete type's field for meta getter compilation.
struct ConcreteFieldInfo {
    name: String,
    type_name: String,
    slot: usize,
    runtime_tag: i64,
}

/// Pre-resolved TypeMeta/FieldMeta class info for meta getter compilation.
struct ReflectionMetaInfo {
    type_meta_type_id_val: u32,
    type_meta_field_count: u32,
    name_slot: usize,
    fields_slot: usize,
    construct_slot: usize,
    field_meta_type_id_val: u32,
    field_meta_field_count: u32,
    fm_name_slot: usize,
    fm_type_name_slot: usize,
    fm_annotations_slot: usize,
    fm_get_slot: usize,
    fm_set_slot: usize,
}

/// Resolve the concrete type's name and TypeDefId from a TypeId.
fn resolve_concrete_type_name<C: VtableCtx>(
    ctx: &C,
    concrete_type_id: TypeId,
) -> CodegenResult<(TypeDefId, String)> {
    let arena = ctx.arena();
    // Try class first, then struct/nominal
    let type_def_id = arena
        .unwrap_class(concrete_type_id)
        .map(|(id, _)| id)
        .or_else(|| arena.unwrap_nominal(concrete_type_id).map(|(id, _, _)| id))
        .ok_or_else(|| {
            CodegenError::internal_with_context(
                "meta getter: cannot resolve concrete type",
                format!("{:?}", concrete_type_id),
            )
        })?;
    let type_def = ctx.query().get_type(type_def_id);
    let type_name = ctx
        .query()
        .last_segment(type_def.name_id)
        .unwrap_or_else(|| "?".to_string());
    Ok((type_def_id, type_name))
}

/// Resolve TypeMeta and FieldMeta class metadata from type_metadata.
fn resolve_reflection_meta<C: VtableCtx>(ctx: &C) -> CodegenResult<ReflectionMetaInfo> {
    let registry = ctx.registry();
    let name_table = ctx.analyzed().name_table();

    let type_meta_def_id = registry
        .type_by_short_name("TypeMeta", name_table)
        .ok_or_else(|| CodegenError::not_found("TypeMeta class", "entity registry"))?;
    let field_meta_def_id = registry
        .type_by_short_name("FieldMeta", name_table)
        .ok_or_else(|| CodegenError::not_found("FieldMeta class", "entity registry"))?;

    let tm_meta = ctx
        .type_metadata()
        .get(&type_meta_def_id)
        .ok_or_else(|| CodegenError::not_found("TypeMeta", "type_metadata"))?;
    let fm_meta = ctx
        .type_metadata()
        .get(&field_meta_def_id)
        .ok_or_else(|| CodegenError::not_found("FieldMeta", "type_metadata"))?;

    let lookup = |slots: &FxHashMap<String, usize>, name: &str, ty: &str| -> CodegenResult<usize> {
        slots.get(name).copied().ok_or_else(|| {
            CodegenError::not_found("reflection field slot", format!("{}.{}", ty, name))
        })
    };

    Ok(ReflectionMetaInfo {
        type_meta_type_id_val: tm_meta.type_id,
        type_meta_field_count: tm_meta.physical_slot_count as u32,
        name_slot: lookup(&tm_meta.field_slots, "name", "TypeMeta")?,
        fields_slot: lookup(&tm_meta.field_slots, "fields", "TypeMeta")?,
        construct_slot: lookup(&tm_meta.field_slots, "construct", "TypeMeta")?,
        field_meta_type_id_val: fm_meta.type_id,
        field_meta_field_count: fm_meta.physical_slot_count as u32,
        fm_name_slot: lookup(&fm_meta.field_slots, "name", "FieldMeta")?,
        fm_type_name_slot: lookup(&fm_meta.field_slots, "type_name", "FieldMeta")?,
        fm_annotations_slot: lookup(&fm_meta.field_slots, "annotations", "FieldMeta")?,
        fm_get_slot: lookup(&fm_meta.field_slots, "get", "FieldMeta")?,
        fm_set_slot: lookup(&fm_meta.field_slots, "set", "FieldMeta")?,
    })
}

/// Collect field info from a concrete type for meta getter compilation.
fn collect_concrete_field_info<C: VtableCtx>(
    ctx: &C,
    type_def_id: TypeDefId,
) -> Vec<ConcreteFieldInfo> {
    let query = ctx.query();
    let arena = ctx.arena();
    let name_table = ctx.analyzed().name_table();
    query
        .fields_on_type(type_def_id)
        .map(|field_id| {
            let field = query.get_field(field_id);
            let name = name_table
                .last_segment_str(field.name_id)
                .unwrap_or_default();
            let type_name = arena.display_basic(field.ty);
            let runtime_tag = crate::types::unknown_type_tag(field.ty, arena) as i64;
            ConcreteFieldInfo {
                name,
                type_name,
                slot: field.slot,
                runtime_tag,
            }
        })
        .collect()
}

/// Emit the lazy-init cache check at the start of a meta getter function.
///
/// Calls `type_meta_cache_get(cache_key_id)` and branches on the result.
/// Returns `(cold_block, merge_block)`. The caller should:
/// 1. Build the TypeMeta in `cold_block` (ending with `emit_meta_cache_store`).
/// 2. The merge block has a single block param containing the TypeMeta pointer.
///
/// Hot path (cache hit) is already wired: rc_incs cached ptr, jumps to merge.
fn emit_meta_cache_check<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    cache_key_id: u32,
    cache_get_id: FuncId,
    rc_inc_id: FuncId,
) -> (Block, Block) {
    let ptr_type = ctx.ptr_type();

    // Call type_meta_cache_get(cache_key_id)
    let cache_get_ref = ctx
        .jit_module()
        .declare_func_in_func(cache_get_id, builder.func);
    let key_val = builder.ins().iconst(types::I32, cache_key_id as i64);
    let get_call = builder.ins().call(cache_get_ref, &[key_val]);
    let cached_ptr = builder.inst_results(get_call)[0];

    let null = builder.ins().iconst(ptr_type, 0);
    let is_null = builder.ins().icmp(IntCC::Equal, cached_ptr, null);

    let cold_block = builder.create_block();
    let hot_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, ptr_type);

    builder.ins().brif(is_null, cold_block, &[], hot_block, &[]);

    // Hot path: rc_inc and return cached value.
    builder.switch_to_block(hot_block);
    builder.seal_block(hot_block);
    let rc_inc_ref = ctx
        .jit_module()
        .declare_func_in_func(rc_inc_id, builder.func);
    builder.ins().call(rc_inc_ref, &[cached_ptr]);
    builder.ins().jump(merge_block, &[cached_ptr.into()]);

    // Cold block will be filled by caller.
    builder.switch_to_block(cold_block);
    builder.seal_block(cold_block);

    (cold_block, merge_block)
}

/// Emit the store-and-inc at the end of the cold path after building TypeMeta.
///
/// rc_incs `type_meta_ptr` so the cache holds one reference AND the caller gets one,
/// calls `type_meta_cache_store(cache_key_id, ptr)`, then jumps to merge_block.
fn emit_meta_cache_store<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    cache_key_id: u32,
    cache_store_id: FuncId,
    rc_inc_id: FuncId,
    type_meta_ptr: Value,
    merge_block: Block,
) {
    // rc_inc so the cache holds one reference AND the caller gets one.
    let rc_inc_ref = ctx
        .jit_module()
        .declare_func_in_func(rc_inc_id, builder.func);
    builder.ins().call(rc_inc_ref, &[type_meta_ptr]);

    // Store into runtime cache (cache takes ownership of one rc reference).
    let cache_store_ref = ctx
        .jit_module()
        .declare_func_in_func(cache_store_id, builder.func);
    let key_val = builder.ins().iconst(types::I32, cache_key_id as i64);
    builder
        .ins()
        .call(cache_store_ref, &[key_val, type_meta_ptr]);
    builder.ins().jump(merge_block, &[type_meta_ptr.into()]);
}

/// Resolve a RuntimeKey to a FuncId through the vtable context's function registry.
fn resolve_runtime_in_vtable<C: VtableCtx>(ctx: &mut C, key: RuntimeKey) -> CodegenResult<FuncId> {
    let func_key = ctx
        .funcs()
        .runtime_key(key)
        .ok_or_else(|| CodegenError::not_found("runtime function", key.name()))?;
    ctx.funcs()
        .func_id(func_key)
        .ok_or_else(|| CodegenError::not_found("runtime func_id", key.name()))
}

/// Compile getter trampoline functions for each field.
/// Returns a Vec of FuncIds, one per field.
fn compile_getter_trampolines<C: VtableCtx>(
    ctx: &mut C,
    fields: &[ConcreteFieldInfo],
    instance_get: FuncId,
    heap_alloc: FuncId,
) -> CodegenResult<Vec<FuncId>> {
    let ptr_type = ctx.ptr_type();
    let mut ids = Vec::with_capacity(fields.len());

    for field in fields {
        let func_name = ctx
            .funcs()
            .next_string_data_name()
            .replace("string_data", "meta_getter");

        // Signature: (closure_ptr, unknown_ptr) -> unknown_ptr
        let mut sig = ctx.jit_module().make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // closure
        sig.params.push(AbiParam::new(ptr_type)); // instance as unknown
        sig.returns.push(AbiParam::new(ptr_type)); // field value as unknown

        let func_id = ctx
            .jit_module()
            .declare_function(&func_name, Linkage::Local, &sig)
            .map_err(CodegenError::cranelift)?;

        let mut func_ctx = ctx.jit_module().make_context();
        func_ctx.func.signature = sig;
        {
            let mut fbc = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut fbc);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);
            let params = builder.block_params(entry).to_vec();
            let unknown_ptr = params[1];

            // Extract instance pointer from TaggedValue payload (offset 8)
            let instance_raw = builder
                .ins()
                .load(types::I64, MemFlags::new(), unknown_ptr, 8);
            let instance_ptr = builder
                .ins()
                .bitcast(ptr_type, MemFlags::new(), instance_raw);

            // Read field
            let get_ref = ctx
                .jit_module()
                .declare_func_in_func(instance_get, builder.func);
            let slot_val = builder.ins().iconst(types::I32, field.slot as i64);
            let call = builder.ins().call(get_ref, &[instance_ptr, slot_val]);
            let field_raw = builder.inst_results(call)[0];

            // Box result as unknown (16-byte TaggedValue on heap)
            let alloc_ref = ctx
                .jit_module()
                .declare_func_in_func(heap_alloc, builder.func);
            let size_val = builder.ins().iconst(ptr_type, 16);
            let alloc_call = builder.ins().call(alloc_ref, &[size_val]);
            let tagged_ptr = builder.inst_results(alloc_call)[0];
            let tag_val = builder.ins().iconst(types::I64, field.runtime_tag);
            builder.ins().store(MemFlags::new(), tag_val, tagged_ptr, 0);
            builder
                .ins()
                .store(MemFlags::new(), field_raw, tagged_ptr, 8);

            builder.ins().return_(&[tagged_ptr]);
            builder.finalize();
        }

        ctx.jit_module()
            .define_function(func_id, &mut func_ctx)
            .map_err(CodegenError::cranelift)?;
        ctx.jit_module().clear_context(&mut func_ctx);

        ids.push(func_id);
    }

    Ok(ids)
}

/// Compile setter trampoline functions for each field.
/// Returns a Vec of FuncIds, one per field.
fn compile_setter_trampolines<C: VtableCtx>(
    ctx: &mut C,
    fields: &[ConcreteFieldInfo],
    instance_set: FuncId,
) -> CodegenResult<Vec<FuncId>> {
    let ptr_type = ctx.ptr_type();
    let mut ids = Vec::with_capacity(fields.len());

    for field in fields {
        let func_name = ctx
            .funcs()
            .next_string_data_name()
            .replace("string_data", "meta_setter");

        // Signature: (closure_ptr, unknown_ptr, unknown_ptr) -> i64 (void)
        let mut sig = ctx.jit_module().make_signature();
        sig.params.push(AbiParam::new(ptr_type)); // closure
        sig.params.push(AbiParam::new(ptr_type)); // instance as unknown
        sig.params.push(AbiParam::new(ptr_type)); // value as unknown
        sig.returns.push(AbiParam::new(types::I64)); // void return

        let func_id = ctx
            .jit_module()
            .declare_function(&func_name, Linkage::Local, &sig)
            .map_err(CodegenError::cranelift)?;

        let mut func_ctx = ctx.jit_module().make_context();
        func_ctx.func.signature = sig;
        {
            let mut fbc = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut fbc);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);
            let params = builder.block_params(entry).to_vec();
            let unknown_instance = params[1];
            let unknown_value = params[2];

            // Extract instance pointer from TaggedValue payload
            let inst_raw = builder
                .ins()
                .load(types::I64, MemFlags::new(), unknown_instance, 8);
            let instance_ptr = builder.ins().bitcast(ptr_type, MemFlags::new(), inst_raw);

            // Extract field value from TaggedValue payload
            let field_val = builder
                .ins()
                .load(types::I64, MemFlags::new(), unknown_value, 8);

            // Write field
            let set_ref = ctx
                .jit_module()
                .declare_func_in_func(instance_set, builder.func);
            let slot_val = builder.ins().iconst(types::I32, field.slot as i64);
            builder
                .ins()
                .call(set_ref, &[instance_ptr, slot_val, field_val]);

            let zero = builder.ins().iconst(types::I64, 0);
            builder.ins().return_(&[zero]);
            builder.finalize();
        }

        ctx.jit_module()
            .define_function(func_id, &mut func_ctx)
            .map_err(CodegenError::cranelift)?;
        ctx.jit_module().clear_context(&mut func_ctx);

        ids.push(func_id);
    }

    Ok(ids)
}

/// Compile a constructor trampoline for the concrete type.
/// Signature: (closure_ptr, [unknown]) -> unknown_ptr
fn compile_constructor_trampoline<C: VtableCtx>(
    ctx: &mut C,
    type_def_id: TypeDefId,
    instance_new: FuncId,
    instance_set: FuncId,
    heap_alloc: FuncId,
) -> CodegenResult<FuncId> {
    let ptr_type = ctx.ptr_type();

    let meta = ctx
        .type_metadata()
        .get(&type_def_id)
        .ok_or_else(|| CodegenError::not_found("target type", "type_metadata for constructor"))?;
    let runtime_type_id = meta.type_id;
    let field_count = meta.physical_slot_count;

    let array_get_val = resolve_runtime_in_vtable(ctx, RuntimeKey::ArrayGetValue)?;

    let func_name = ctx
        .funcs()
        .next_string_data_name()
        .replace("string_data", "meta_ctor");

    // Signature: (closure_ptr, array_ptr) -> unknown_ptr
    let mut sig = ctx.jit_module().make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // closure
    sig.params.push(AbiParam::new(ptr_type)); // [unknown] array
    sig.returns.push(AbiParam::new(ptr_type)); // result as unknown ptr

    let func_id = ctx
        .jit_module()
        .declare_function(&func_name, Linkage::Local, &sig)
        .map_err(CodegenError::cranelift)?;

    let mut func_ctx = ctx.jit_module().make_context();
    func_ctx.func.signature = sig;
    {
        let mut fbc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut fbc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let params = builder.block_params(entry).to_vec();
        let array_ptr = params[1];

        // Allocate instance
        let new_ref = ctx
            .jit_module()
            .declare_func_in_func(instance_new, builder.func);
        let type_id_val = builder.ins().iconst(types::I32, runtime_type_id as i64);
        let field_count_val = builder.ins().iconst(types::I32, field_count as i64);
        let rt_type = builder.ins().iconst(
            types::I32,
            vole_runtime::value::RuntimeTypeId::Instance as i64,
        );
        let new_call = builder
            .ins()
            .call(new_ref, &[type_id_val, field_count_val, rt_type]);
        let instance_ptr = builder.inst_results(new_call)[0];

        // For each field, read from [unknown] array and store to instance
        let get_val_ref = ctx
            .jit_module()
            .declare_func_in_func(array_get_val, builder.func);
        let set_ref = ctx
            .jit_module()
            .declare_func_in_func(instance_set, builder.func);

        for slot in 0..field_count {
            let idx = builder.ins().iconst(types::I64, slot as i64);
            let elem_call = builder.ins().call(get_val_ref, &[array_ptr, idx]);
            let tagged_ptr_raw = builder.inst_results(elem_call)[0];

            let tagged_ptr = builder
                .ins()
                .bitcast(ptr_type, MemFlags::new(), tagged_ptr_raw);
            let field_val = builder
                .ins()
                .load(types::I64, MemFlags::new(), tagged_ptr, 8);

            let slot_val = builder.ins().iconst(types::I32, slot as i64);
            builder
                .ins()
                .call(set_ref, &[instance_ptr, slot_val, field_val]);
        }

        // Box instance as unknown
        let instance_as_i64 = builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), instance_ptr);
        let alloc_ref = ctx
            .jit_module()
            .declare_func_in_func(heap_alloc, builder.func);
        let size_val = builder.ins().iconst(ptr_type, 16);
        let alloc_call = builder.ins().call(alloc_ref, &[size_val]);
        let tagged_ptr = builder.inst_results(alloc_call)[0];
        let tag_val = builder.ins().iconst(
            types::I64,
            vole_runtime::value::RuntimeTypeId::Instance as i64,
        );
        builder.ins().store(MemFlags::new(), tag_val, tagged_ptr, 0);
        builder
            .ins()
            .store(MemFlags::new(), instance_as_i64, tagged_ptr, 8);

        builder.ins().return_(&[tagged_ptr]);
        builder.finalize();
    }

    ctx.jit_module()
        .define_function(func_id, &mut func_ctx)
        .map_err(CodegenError::cranelift)?;
    ctx.jit_module().clear_context(&mut func_ctx);

    Ok(func_id)
}

/// Compile a stub constructor for function/closure types.
/// Signature: (closure_ptr, [unknown]) -> unknown_ptr
/// Simply traps -- function types cannot be constructed via @meta.
fn compile_stub_constructor<C: VtableCtx>(ctx: &mut C) -> CodegenResult<FuncId> {
    let ptr_type = ctx.ptr_type();
    let func_name = ctx
        .funcs()
        .next_string_data_name()
        .replace("string_data", "meta_ctor_stub");

    let mut sig = ctx.jit_module().make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // closure
    sig.params.push(AbiParam::new(ptr_type)); // [unknown] array
    sig.returns.push(AbiParam::new(ptr_type)); // result (never reached)

    let func_id = ctx
        .jit_module()
        .declare_function(&func_name, Linkage::Local, &sig)
        .map_err(CodegenError::cranelift)?;

    let mut func_ctx = ctx.jit_module().make_context();
    func_ctx.func.signature = sig;
    {
        let mut fbc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut fbc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        builder.ins().trap(crate::trap_codes::PANIC);
        builder.finalize();
    }

    ctx.jit_module()
        .define_function(func_id, &mut func_ctx)
        .map_err(CodegenError::cranelift)?;
    ctx.jit_module().clear_context(&mut func_ctx);

    Ok(func_id)
}

/// Emit IR to allocate a class instance via InstanceNew.
fn emit_alloc_instance(
    builder: &mut FunctionBuilder,
    module: &mut cranelift_jit::JITModule,
    instance_new: FuncId,
    _ptr_type: Type,
    type_id: u32,
    field_count: u32,
) -> Value {
    let new_ref = module.declare_func_in_func(instance_new, builder.func);
    let type_id_val = builder.ins().iconst(types::I32, type_id as i64);
    let field_count_val = builder.ins().iconst(types::I32, field_count as i64);
    let rt_type = builder.ins().iconst(
        types::I32,
        vole_runtime::value::RuntimeTypeId::Instance as i64,
    );
    let call = builder
        .ins()
        .call(new_ref, &[type_id_val, field_count_val, rt_type]);
    builder.inst_results(call)[0]
}

/// Emit IR to set a field on an instance via InstanceSetField.
fn emit_set_field(
    builder: &mut FunctionBuilder,
    module: &mut cranelift_jit::JITModule,
    instance_set: FuncId,
    instance_ptr: Value,
    slot: usize,
    value: Value,
    _ptr_type: Type,
) {
    let set_ref = module.declare_func_in_func(instance_set, builder.func);
    let slot_val = builder.ins().iconst(types::I32, slot as i64);
    let value_as_i64 = builder.ins().bitcast(types::I64, MemFlags::new(), value);
    builder
        .ins()
        .call(set_ref, &[instance_ptr, slot_val, value_as_i64]);
}

/// Emit IR to build the [FieldMeta] array inside the meta getter function.
///
/// String DataIds are pre-declared before the FunctionBuilder is created to avoid
/// split-borrow issues on VtableCtx.
#[expect(clippy::too_many_arguments)]
fn emit_build_field_array<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    info: &ReflectionMetaInfo,
    fields: &[ConcreteFieldInfo],
    field_name_data_ids: &[DataId],
    field_type_name_data_ids: &[DataId],
    getter_ids: &[FuncId],
    setter_ids: &[FuncId],
    instance_new: FuncId,
    instance_set: FuncId,
    array_new: FuncId,
    array_push: FuncId,
    closure_alloc: FuncId,
) -> Value {
    let ptr_type = ctx.ptr_type();

    // Create empty array
    let arr_new_ref = ctx
        .jit_module()
        .declare_func_in_func(array_new, builder.func);
    let arr_call = builder.ins().call(arr_new_ref, &[]);
    let arr_ptr = builder.inst_results(arr_call)[0];

    let arr_push_ref = ctx
        .jit_module()
        .declare_func_in_func(array_push, builder.func);

    for (i, _field) in fields.iter().enumerate() {
        // Allocate FieldMeta instance
        let fm_ptr = emit_alloc_instance(
            builder,
            ctx.jit_module(),
            instance_new,
            ptr_type,
            info.field_meta_type_id_val,
            info.field_meta_field_count,
        );

        // Set name (from pre-declared string data)
        let name_val =
            reference_string_data(builder, field_name_data_ids[i], ptr_type, ctx.jit_module());
        emit_set_field(
            builder,
            ctx.jit_module(),
            instance_set,
            fm_ptr,
            info.fm_name_slot,
            name_val,
            ptr_type,
        );

        // Set type_name (from pre-declared string data)
        let type_name_val = reference_string_data(
            builder,
            field_type_name_data_ids[i],
            ptr_type,
            ctx.jit_module(),
        );
        emit_set_field(
            builder,
            ctx.jit_module(),
            instance_set,
            fm_ptr,
            info.fm_type_name_slot,
            type_name_val,
            ptr_type,
        );

        // Set annotations (empty array)
        let ann_new_ref = ctx
            .jit_module()
            .declare_func_in_func(array_new, builder.func);
        let ann_call = builder.ins().call(ann_new_ref, &[]);
        let ann_ptr = builder.inst_results(ann_call)[0];
        emit_set_field(
            builder,
            ctx.jit_module(),
            instance_set,
            fm_ptr,
            info.fm_annotations_slot,
            ann_ptr,
            ptr_type,
        );

        // Set getter closure
        let getter_fn_ref = ctx
            .jit_module()
            .declare_func_in_func(getter_ids[i], builder.func);
        let getter_addr = builder.ins().func_addr(ptr_type, getter_fn_ref);
        let closure_ref = ctx
            .jit_module()
            .declare_func_in_func(closure_alloc, builder.func);
        let zero = builder.ins().iconst(types::I64, 0);
        let getter_call = builder.ins().call(closure_ref, &[getter_addr, zero]);
        let getter_closure = builder.inst_results(getter_call)[0];
        emit_set_field(
            builder,
            ctx.jit_module(),
            instance_set,
            fm_ptr,
            info.fm_get_slot,
            getter_closure,
            ptr_type,
        );

        // Set setter closure
        let setter_fn_ref = ctx
            .jit_module()
            .declare_func_in_func(setter_ids[i], builder.func);
        let setter_addr = builder.ins().func_addr(ptr_type, setter_fn_ref);
        let setter_call = builder.ins().call(closure_ref, &[setter_addr, zero]);
        let setter_closure = builder.inst_results(setter_call)[0];
        emit_set_field(
            builder,
            ctx.jit_module(),
            instance_set,
            fm_ptr,
            info.fm_set_slot,
            setter_closure,
            ptr_type,
        );

        // Push FieldMeta to array
        let tag = builder.ins().iconst(
            types::I64,
            vole_runtime::value::RuntimeTypeId::Instance as i64,
        );
        builder.ins().call(arr_push_ref, &[arr_ptr, tag, fm_ptr]);
    }

    arr_ptr
}

/// Collect all method IDs for an interface using the vtable context.
///
/// Consolidates `collect_interface_methods_via_entity_registry(id, ctx.registry())`
/// at vtable construction sites.
fn collect_interface_methods_ctx<C: VtableCtx>(
    interface_id: TypeDefId,
    ctx: &C,
) -> CodegenResult<Vec<MethodId>> {
    collect_interface_methods_via_entity_registry(interface_id, ctx.registry())
}

/// Convert an i64 word back to its properly typed Cranelift value.
///
/// Consolidates the repeated `word_to_value_type_id(builder, word, ty, ctx.ptr_type(),
/// ctx.registry(), ctx.arena())` call pattern used throughout vtable wrapper compilation.
#[inline]
fn word_to_value_ctx<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    word: Value,
    type_id: TypeId,
    ctx: &C,
) -> Value {
    word_to_value_type_id(
        builder,
        word,
        type_id,
        ctx.ptr_type(),
        ctx.registry(),
        ctx.arena(),
    )
}

/// Convert a typed value to an i64 word for vtable dispatch.
///
/// Consolidates `value_to_word(builder, value, ctx.ptr_type(), heap_alloc_ref,
/// ctx.arena(), ctx.registry())` call sites.
#[inline]
fn value_to_word_ctx<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    heap_alloc_ref: Option<FuncRef>,
    ctx: &mut C,
) -> CodegenResult<Value> {
    value_to_word(
        builder,
        value,
        ctx.ptr_type(),
        heap_alloc_ref,
        ctx.arena(),
        ctx.registry(),
    )
}

/// Convert a TypeId to an ImplTypeId using vtable context internals.
///
/// Consolidates `ImplTypeId::from_type_id(ty, ctx.arena(), ctx.registry())` call sites.
#[inline]
fn impl_type_id_ctx<C: VtableCtx>(ty: TypeId, ctx: &C) -> Option<ImplTypeId> {
    ImplTypeId::from_type_id(ty, ctx.arena(), ctx.registry())
}

/// Get the byte size of a TypeId using vtable context internals.
///
/// Consolidates `type_id_size(ty, ctx.ptr_type(), ctx.registry(), ctx.arena())` call sites.
#[inline]
fn type_size_ctx<C: VtableCtx>(ty: TypeId, ctx: &C) -> u32 {
    type_id_size(ty, ctx.ptr_type(), ctx.registry(), ctx.arena())
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

    let self_val = word_to_value_ctx(builder, data_word, concrete_type_id, ctx);
    let mut args = Vec::with_capacity(param_type_ids.len() + 1);
    for (param_word, &param_ty_id) in params[1..].iter().zip(param_type_ids.iter()) {
        args.push(word_to_value_ctx(builder, *param_word, param_ty_id, ctx));
    }

    let (func_ptr, call_args, sig) = if is_closure {
        let closure_get_key = ctx
            .funcs()
            .runtime_key(RuntimeKey::ClosureGetFunc)
            .ok_or_else(|| CodegenError::missing_resource("ClosureGetFunc runtime function"))?;
        let closure_get_id = ctx
            .funcs()
            .func_id(closure_get_key)
            .ok_or_else(|| CodegenError::not_found("function id", "ClosureGetFunc"))?;
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
        if !ctx.arena().is_void(ret_type_id) {
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
        if !ctx.arena().is_void(ret_type_id) {
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
    let self_val = word_to_value_ctx(builder, data_word, concrete_type_id, ctx);
    let mut call_args = Vec::with_capacity(1 + param_type_ids.len());
    call_args.push(self_val);
    for (param_word, &param_ty_id) in params[1..].iter().zip(param_type_ids.iter()) {
        call_args.push(word_to_value_ctx(builder, *param_word, param_ty_id, ctx));
    }
    let func_id = ctx
        .funcs()
        .func_id(method_info.func_key)
        .ok_or_else(|| CodegenError::not_found("method function id", ""))?;
    let func_ref = ctx.jit_module().declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &call_args);
    Ok(builder.inst_results(call).to_vec())
}

/// Try to import a native function by pointer in the vtable context.
///
/// Returns a `FuncRef` for a direct `call` if the function pointer is found
/// in the `ptr_to_symbol` reverse map, or `None` to fall back to `call_indirect`.
fn try_import_native_in_vtable<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    native_ptr: *const u8,
    sig: &Signature,
) -> Option<FuncRef> {
    // Clone the symbol name to release the immutable borrow on ctx
    // before calling jit_module() which requires a mutable borrow.
    let symbol_name = ctx.ptr_to_symbol().get(&(native_ptr as usize))?.clone();
    let module = ctx.jit_module();
    let func_id = module
        .declare_function(&symbol_name, Linkage::Import, sig)
        .ok()?;
    Some(module.declare_func_in_func(func_id, builder.func))
}

/// Compile wrapper body for External target (native/external function calls)
#[expect(clippy::too_many_arguments)]
fn compile_external_wrapper<C: VtableCtx>(
    builder: &mut FunctionBuilder,
    ctx: &mut C,
    concrete_type_id: TypeId,
    data_word: Value,
    box_ptr: Value,
    params: &[Value],
    external_info: &ExternalMethodInfo,
    iterator_info: IteratorVtableInfo,
    param_type_ids: &[TypeId],
    return_type_id: TypeId,
) -> CodegenResult<Vec<Value>> {
    // For Iterator interface, wrap the boxed interface in a RcIterator
    // so external functions like vole_iter_collect can iterate via vtable.
    let self_val = if let Some(iter_elem_tag) = iterator_info {
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
                CodegenError::not_found(
                    "native function",
                    format!("vole:std:runtime::{}", native_name),
                )
            })?
            .ptr;
        let mut iter_sig = ctx.jit_module().make_signature();
        iter_sig.params.push(AbiParam::new(ctx.ptr_type()));
        if use_tag {
            iter_sig.params.push(AbiParam::new(types::I64));
        }
        iter_sig.returns.push(AbiParam::new(ctx.ptr_type()));

        let iter_call = if use_tag {
            let tag_val = builder.ins().iconst(
                types::I64,
                iter_elem_tag.expect("tagged iterator requires known element type") as i64,
            );
            if let Some(func_ref) =
                try_import_native_in_vtable(builder, ctx, interface_iter_ptr, &iter_sig)
            {
                builder.ins().call(func_ref, &[box_ptr, tag_val])
            } else {
                let iter_sig_ref = builder.import_signature(iter_sig);
                let iter_fn_ptr = builder
                    .ins()
                    .iconst(ctx.ptr_type(), interface_iter_ptr as i64);
                builder
                    .ins()
                    .call_indirect(iter_sig_ref, iter_fn_ptr, &[box_ptr, tag_val])
            }
        } else if let Some(func_ref) =
            try_import_native_in_vtable(builder, ctx, interface_iter_ptr, &iter_sig)
        {
            builder.ins().call(func_ref, &[box_ptr])
        } else {
            let iter_sig_ref = builder.import_signature(iter_sig);
            let iter_fn_ptr = builder
                .ins()
                .iconst(ctx.ptr_type(), interface_iter_ptr as i64);
            builder
                .ins()
                .call_indirect(iter_sig_ref, iter_fn_ptr, &[box_ptr])
        };
        builder.inst_results(iter_call)[0]
    } else {
        word_to_value_ctx(builder, data_word, concrete_type_id, ctx)
    };

    let mut call_args = Vec::with_capacity(1 + param_type_ids.len());
    call_args.push(self_val);
    for (param_word, &param_ty_id) in params[1..].iter().zip(param_type_ids.iter()) {
        call_args.push(word_to_value_ctx(builder, *param_word, param_ty_id, ctx));
    }

    // Get string names from NameId
    let (module_path, native_name) =
        crate::context::resolve_external_names(ctx.analyzed().name_table(), external_info)?;

    // Extract just the pointer value to end the borrow before jit_module() call
    let native_func_ptr = ctx
        .native_registry()
        .lookup(&module_path, &native_name)
        .ok_or_else(|| {
            CodegenError::not_found(
                "native function",
                format!("{}::{}", module_path, native_name),
            )
        })?
        .ptr;

    let mut native_sig = ctx.jit_module().make_signature();
    // For Iterator, the self param is now *mut RcIterator (pointer)
    let arena = ctx.arena();
    let self_param_type = if iterator_info.is_some() {
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
    if !arena.is_void(return_type_id) {
        native_sig.returns.push(AbiParam::new(type_id_to_cranelift(
            return_type_id,
            arena,
            ctx.ptr_type(),
        )));
    }

    let call = if let Some(func_ref) =
        try_import_native_in_vtable(builder, ctx, native_func_ptr, &native_sig)
    {
        builder.ins().call(func_ref, &call_args)
    } else {
        let sig_ref = builder.import_signature(native_sig);
        let func_ptr_val = builder.ins().iconst(ctx.ptr_type(), native_func_ptr as i64);
        builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, &call_args)
    };
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
    if !entity_registry.is_interface_type(interface_id) {
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
        .ok_or_else(|| {
            CodegenError::not_found("interface name string", format!("{:?}", type_def_id))
        })?;
    let interface_name = env.interner.lookup(&interface_name_str).ok_or_else(|| {
        CodegenError::not_found("interface name in interner", &interface_name_str)
    })?;

    // Check if value is already an interface
    if env.analyzed.type_arena().is_interface(value.type_id) {
        tracing::debug!("already interface, skip boxing");
        return Ok(value);
    }

    // Check if this is an external-only interface
    if env.analyzed.query().is_external_only(type_def_id) {
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
    let data_word = value_to_word_ctx(builder, &value, Some(heap_alloc_ref), &mut ctx_view)?;

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

    let impl_type_id = impl_type_id_ctx(concrete_type_id, ctx).ok_or_else(|| {
        CodegenError::not_found(
            "interface method",
            format!("{} on {:?}", method_name_str, concrete_type_id),
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
            .ok_or_else(|| CodegenError::not_found("method info", "method_func_keys lookup"))?;
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
        let meta = type_metadata_by_name_id(ctx.type_metadata(), type_name_id)?;
        let method_info = meta.method_infos.get(&method_name_id).copied()?;

        // Look up method signature via ProgramQuery - require TypeId fields
        let sig_from_entity = ctx
            .query()
            .find_method(type_def_id, method_name_id)
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
        if let Some(interface_type_def_id) = ctx.query().try_type_def_id(interface_name_id)
            && let Some(method_name_id) = method_name_id
            && let Some(found_method_id) = ctx
                .query()
                .find_method(interface_type_def_id, method_name_id)
            && let Some(external_info) = ctx.query().method_external_binding(found_method_id)
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
        // Handle Vole-body default methods: look up the compiled function via
        // method_func_keys. Sema's register_interface_default_methods_on_implementing_type
        // copies default methods onto the implementing type, and the compiler registers
        // their JIT functions in method_func_keys during register_implement_block.
        if let Some(method_name_id) = method_name_id {
            let type_name_id = impl_type_id.name_id();
            if let Some(&func_key) = ctx.method_func_keys().get(&(type_name_id, method_name_id)) {
                let (param_type_ids, return_type_id) = substituted_types.unwrap_or_else(|| {
                    let arena = ctx.arena();
                    let (params, ret, _) = arena
                        .unwrap_function(interface_method.signature_id)
                        .expect("INTERNAL: vtable default: signature is not a function");
                    (params.to_vec(), ret)
                });
                let returns_void = matches!(ctx.arena().get(return_type_id), SemaType::Void);
                let method_info = MethodInfo { func_key };
                return Ok(VtableMethod {
                    param_count: param_type_ids.len(),
                    returns_void,
                    param_type_ids,
                    return_type_id,
                    union_tag_remap: None,
                    target: VtableMethodTarget::Method(method_info),
                });
            }
        }
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
                    let pos = concrete_variants
                        .iter()
                        .position(|&v| v == concrete_variant)?;
                    used_concrete[pos] = true;
                    if callee_tag != pos {
                        is_identity = false;
                    }
                    remap.push(pos as u8);
                } else {
                    return None;
                }
            }
            _ => {
                // Match by TypeId identity
                let pos = concrete_variants
                    .iter()
                    .position(|&v| v == callee_variant)?;
                used_concrete[pos] = true;
                if callee_tag != pos {
                    is_identity = false;
                }
                remap.push(pos as u8);
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
        .runtime_key(RuntimeKey::HeapAlloc)
        .ok_or_else(|| CodegenError::missing_resource("HeapAlloc runtime function"))?;
    let func_id = ctx
        .funcs()
        .func_id(key)
        .ok_or_else(|| CodegenError::not_found("function id", "HeapAlloc"))?;
    Ok(ctx.jit_module().declare_func_in_func(func_id, builder.func))
}
